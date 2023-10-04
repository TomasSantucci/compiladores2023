{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE RecordWildCards #-}
{-|
Module      : Bytecompile
Description : Compila a bytecode. Ejecuta bytecode.
Copyright   : (c) Mauro Jaskelioff, Guido Martínez, 2020.
License     : GPL-3
Maintainer  : mauro@fceia.unr.edu.ar
Stability   : experimental

Este módulo permite compilar módulos a la Macchina. También provee
una implementación de la Macchina para ejecutar el bytecode.
-}
module Bytecompile
  (Bytecode, runBC, bcWrite, bcRead, bytecompileModule, showBC, showOps)
 where

import Lang
import MonadFD4

import qualified Data.ByteString.Lazy as BS
import Data.Binary ( Word32, Binary(put, get), decode, encode )
import Data.Binary.Put ( putWord32le )
import Data.Binary.Get ( getWord32le, isEmpty )

import Data.Maybe (fromJust)
import Data.List (intercalate, elemIndex)
import Data.Char

type Opcode = Int
type Bytecode = [Int]

newtype Bytecode32 = BC { un32 :: [Word32] }

{- Esta instancia explica como codificar y decodificar Bytecode de 32 bits -}
instance Binary Bytecode32 where
  put (BC bs) = mapM_ putWord32le bs
  get = go
    where go =
           do
            empty <- isEmpty
            if empty
              then return $ BC []
              else do x <- getWord32le
                      BC xs <- go
                      return $ BC (x:xs)

{- Estos sinónimos de patrón nos permiten escribir y hacer
pattern-matching sobre el nombre de la operación en lugar del código
entero, por ejemplo:

   f (CALL : cs) = ...

 Notar que si hubieramos escrito algo como
   call = 5
 no podríamos hacer pattern-matching con `call`.

 En lo posible, usar estos códigos exactos para poder ejectutar un
 mismo bytecode compilado en distintas implementaciones de la máquina.
-}
pattern NULL     = 0
pattern RETURN   = 1
pattern CONST    = 2
pattern ACCESS   = 3
pattern FUNCTION = 4
pattern CALL     = 5
pattern ADD      = 6
pattern SUB      = 7
pattern FIX      = 9
pattern STOP     = 10
pattern SHIFT    = 11
pattern DROP     = 12
pattern PRINT    = 13
pattern PRINTN   = 14
pattern JUMP     = 15

--función util para debugging: muestra el Bytecode de forma más legible.
showOps :: Bytecode -> [String]
showOps [] = []
showOps (NULL:xs)        = "NULL" : showOps xs
showOps (RETURN:xs)      = "RETURN" : showOps xs
showOps (CONST:i:xs)     = ("CONST " ++  show i) : showOps xs
showOps (ACCESS:i:xs)    = ("ACCESS " ++ show i) : showOps xs
showOps (FUNCTION:i:xs)  = ("FUNCTION len=" ++ show i) : showOps xs
showOps (CALL:xs)        = "CALL" : showOps xs
showOps (ADD:xs)         = "ADD" : showOps xs
showOps (SUB:xs)         = "SUB" : showOps xs
showOps (FIX:xs)         = "FIX" : showOps xs
showOps (STOP:xs)        = "STOP" : showOps xs
showOps (JUMP:i:xs)      = ("JUMP off=" ++ show i) : showOps xs
showOps (SHIFT:xs)       = "SHIFT" : showOps xs
showOps (DROP:xs)        = "DROP" : showOps xs
showOps (PRINT:xs)       = let (msg,_:rest) = span (/=NULL) xs
                           in ("PRINT " ++ show (bc2string msg)) : showOps rest
showOps (PRINTN:xs)      = "PRINTN" : showOps xs
showOps (ADD:xs)         = "ADD" : showOps xs
showOps (x:xs)           = show x : showOps xs

showBC :: Bytecode -> String
showBC = intercalate "; " . showOps

bcc :: MonadFD4 m => TTerm -> m Bytecode
bcc (V _ (Bound i)) = return [ACCESS,i]

bcc (Const _ (CNat i)) = return [CONST,i]

bcc (Lam _ _ _ (Sc1 t)) = do
  ct <- bcc t
  return $ [FUNCTION, (length ct) + 1] ++ ct ++ [RETURN]

bcc (App _ t1 t2) = do
  ct1 <- bcc t1
  ct2 <- bcc t2
  return $ ct1 ++ ct2 ++ [CALL]

bcc (Print _ str t) = do
  ct <- bcc t
  return $ ct ++ [PRINTN,PRINT] ++ (string2bc str) ++ [NULL]

bcc (BinaryOp _ op t1 t2) = do
  ct1 <- bcc t1
  ct2 <- bcc t2
  return $ ct1 ++ ct2 ++ (op2bc op)

bcc (Fix _ _ _ _ _ (Sc2 t)) = do--Preguntar !!!
  ct <- bcc t
  return  $ [FUNCTION, (length ct) + 1] ++ ct ++ [RETURN,FIX]

bcc (IfZ _ c t e) = do -- Jump solo salta si se encuentra un 0 en el stack top.
  cc <- bcc c
  ct <- bcc t
  ce <- bcc e
  return $ cc ++ [JUMP, (length ce) + 4] ++ ce ++ [CONST,0,JUMP,length ct] ++ ct

bcc (Let _ _ _ def (Sc1 body)) = do
  cdef <- bcc def
  cbody <- bcc body
  return $ cdef ++ [SHIFT] ++ cbody ++ [DROP]

bcc t = failFD4 (show t)

op2bc :: BinaryOp -> Bytecode
op2bc Add = [ADD]
op2bc Sub = [SUB]

-- ord/chr devuelven los codepoints unicode, o en otras palabras
-- la codificación UTF-32 del caracter.
string2bc :: String -> Bytecode
string2bc = map ord

bc2string :: Bytecode -> String
bc2string = map chr

bytecompileModule :: MonadFD4 m => Module -> m Bytecode
bytecompileModule m = do 
  t <- module2term m
  bc <- bcc t
  return $ bc ++ [STOP]

glb2bound :: MonadFD4 m => TTerm -> [Name] -> Int -> m TTerm
glb2bound (V i (Global name)) decs n = do
  case elemIndex name decs of
    Nothing -> failFD4 ("Variable global no declarada: " ++ (show name))
    Just d -> return $ V i (Bound (n + d))
glb2bound v@(V _ _) _ _ = return v
glb2bound (Lam p y ty (Sc1 t)) decs n = do
  t' <- glb2bound t decs (n+1)
  return $ Lam p y ty (Sc1 t')
glb2bound (App p l r) decs n = do
  l' <- glb2bound l decs n
  r' <- glb2bound r decs n
  return $ App p l' r'
glb2bound (Fix p f fty x xty (Sc2 t)) decs n = do
  t' <- glb2bound t decs (n+2)
  return $ Fix p f fty x xty (Sc2 t')
glb2bound (IfZ p c t e) decs n = do
  c' <- glb2bound c decs n
  t' <- glb2bound t decs n
  e' <- glb2bound e decs n
  return $ IfZ p c' t' e'
glb2bound t@(Const _ _) decs n = return t
glb2bound (Print p str t) decs n = do
  t' <- glb2bound t decs n
  return $ Print p str t'
glb2bound (BinaryOp p op t u) decs n = do
  t' <- glb2bound t decs n
  u' <- glb2bound u decs n
  return $ BinaryOp p op t' u'
glb2bound (Let p v vty m (Sc1 o)) decs n = do
  m' <- glb2bound m decs n
  o' <- glb2bound o decs (n+1)
  return $ Let p v vty m' (Sc1 o')

module2term :: MonadFD4 m => Module -> m TTerm
module2term m = do
  module2term' m []

module2term' :: MonadFD4 m => Module -> [Name] -> m TTerm
module2term' [] _ = failFD4 "Módulo inválido."
module2term' [Decl _ _ _ t] decs = glb2bound t decs 0
module2term' ((Decl p x xty t):ds) decs = do
    t' <- module2term' ds (x:decs)
    tbound <- glb2bound t decs 0
    return (Let (p,xty) x xty tbound (Sc1 t'))

-- | Toma un bytecode, lo codifica y lo escribe un archivo
bcWrite :: Bytecode -> FilePath -> IO ()
bcWrite bs filename = BS.writeFile filename (encode $ BC $ fromIntegral <$> bs)

---------------------------
-- * Ejecución de bytecode
---------------------------

-- | Lee de un archivo y lo decodifica a bytecode
bcRead :: FilePath -> IO Bytecode
bcRead filename = (map fromIntegral <$> un32) . decode <$> BS.readFile filename

type Env = [Val]

data Val = I Int | Fun Env Bytecode | RA Env Bytecode

runBC :: MonadFD4 m => Bytecode -> m ()
runBC bc = runBC' bc [] []

runBC' :: MonadFD4 m => Bytecode -> [Val] -> [Val]-> m ()
runBC' (STOP:c) _ _ = return ()

runBC' (CONST:n:c) e s =
  runBC' c e ((I n):s)

runBC' (ADD:c) e ((I n):(I m):s) =
  runBC' c e ((I (n+m)):s)

runBC' (SUB:c) e ((I n):(I m):s) =
  runBC' c e ((I (max (n-m) 0)):s)

runBC' (ACCESS:i:c) e s =
  runBC' c e ((e!!i):s)

runBC' (CALL:c) e (v:(Fun e' c'):s) =
  runBC' c' (v:e') ((RA e c):s)

runBC' (FUNCTION:l:c) e s =
  runBC' c' e ((Fun e cf):s)
  where c' = drop l c
        cf = take l c

runBC' (RETURN:_) _ (v:(RA e c):s) =
  runBC' c e (v:s)

runBC' (SHIFT:c) e (v:s) =
  runBC' c (v:e) s

runBC' (DROP:c) (v:e) (s) =
  runBC' c e s

runBC' (PRINTN:c) e ((I n):s) =
  runBC' c e ((I n):s)

runBC' (PRINT:c) e ((I n):s) = do
  let (msg,_:rest) = span (NULL /=) c
  printFD4 $ (bc2string msg) ++ (show n)
  runBC' rest e ((I n):s)

-- Esta regla se ejecuta inmediatamente 
-- despues de la regla de function por ende e y e' son el mismo 
runBC' (FIX:c) e ((Fun e' c'):s) = do
  let efix = (Fun efix c'):e'
  runBC' c e ((Fun efix c'):s)

runBC' (JUMP:n:c) e ((I z) : s) = do
  if z == 0 
    then runBC' (drop n c) e s
    else runBC' c e s

runBC' c _ s = failFD4 "Error en ejecución de la Macchina."