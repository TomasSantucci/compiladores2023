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
import Data.Binary ( Binary(put, get), decode, encode )
import Data.Binary.Put ( putWord8 )
import Data.Binary.Get ( isEmpty, getWord8 )

import Data.Word
import Data.Bits

import Data.Text.Internal.Encoding.Utf8

import Data.List (intercalate, elemIndex)
import Data.Char

type Opcode = Int
type Bytecode = [Int]

newtype Bytecode8 = BC { un8 :: [Word8] }

{- Esta instancia explica como codificar y decodificar Bytecode de 32 bits -}
instance Binary Bytecode8 where
  put (BC bs) = mapM_ putWord8 bs
  get = go
    where go =
           do
            empty <- isEmpty
            if empty
              then return $ BC []
              else do x <- getWord8
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
pattern NULL     :: Int
pattern NULL     = 0
pattern RETURN   :: Int
pattern RETURN   = 1
pattern CONST    :: Int
pattern CONST    = 2
pattern ACCESS   :: Int
pattern ACCESS   = 3
pattern FUNCTION :: Int
pattern FUNCTION = 4
pattern CALL     :: Int
pattern CALL     = 5
pattern ADD      :: Int
pattern ADD      = 6
pattern SUB      :: Int
pattern SUB      = 7
pattern FIX      :: Int
pattern FIX      = 9
pattern STOP     :: Int
pattern STOP     = 10
pattern SHIFT    :: Int
pattern SHIFT    = 11
pattern DROP     :: Int
pattern DROP     = 12
pattern PRINT    :: Int
pattern PRINT    = 13
pattern PRINTN   :: Int
pattern PRINTN   = 14
pattern JUMP     :: Int
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
showOps (x:xs)           = show x : showOps xs

opArgs :: Int -> Int
opArgs STOP = -1
opArgs CONST = 1
opArgs ACCESS = 1
opArgs FUNCTION = 1
opArgs JUMP = 1
opArgs PRINT = -2
opArgs _ = 0

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
bcWrite bc filename = BS.writeFile filename (encode $ BC $ bcToWords8 bc)

chrToUtf8 :: Char -> [Word8]
chrToUtf8 c = case utf8Length c of
              1 -> [fromIntegral (ord c)]
              2 -> let (w1,w2) = ord2 c
                   in [w1,w2]
              3 -> let (w1,w2,w3) = ord3 c
                   in [w1,w2,w3]
              4 -> let (w1,w2,w3,w4) = ord4 c
                   in [w1,w2,w3,w4]
              _ -> []

encodeStr :: Bytecode -> ([Word8],Bytecode)
encodeStr [] = ([],[])
encodeStr (b:bs) | b == NULL = ([fromIntegral b],bs)
                 | otherwise = let (str, remstr) = encodeStr bs in
                               ((chrToUtf8 (chr b)) ++ str, remstr)

intToWords8 :: Int -> [Word8]
intToWords8 n =
  [ fromIntegral (n .&. 0xFF)
  , fromIntegral ((n `shiftR` 8) .&. 0xFF)
  , fromIntegral ((n `shiftR` 16) .&. 0xFF)
  , fromIntegral ((n `shiftR` 24) .&. 0xFF)
  ]

-- | Toma un bytecode, y lo codifica a lista de bytes (Word8)
bcToWords8 :: Bytecode -> [Word8]
bcToWords8 [] = []
bcToWords8 (b:bs) = case opArgs b of
                  -2 -> let (ws, rm) = encodeStr bs
                        in (fromIntegral b) : (ws ++ (bcToWords8 rm))
                  -1 -> [fromIntegral b]
                  0 -> (fromIntegral b) : (bcToWords8 bs)
                  1 -> (fromIntegral b) : (intToWords8 (head bs)) ++ (bcToWords8 (tail bs))
                  _ -> []

---------------------------
-- * Ejecución de bytecode
---------------------------

-- | Lee de un archivo y lo decodifica a bytecode
bcRead :: FilePath -> IO Bytecode
bcRead filename = (words8ToBc . un8 . decode) <$> (BS.readFile filename)

words8ToChr :: [Word8] -> Int -> Char
words8ToChr [b] 1 = chr (fromIntegral b)
words8ToChr [b1,b2] 2 = chr2 b1 b2
words8ToChr [b1,b2,b3] 3 = chr3 b1 b2 b3
words8ToChr [b1,b2,b3,b4] 4 = chr4 b1 b2 b3 b4
words8ToChr _ _ = error "Se esperaban entre 1 y 4 bytes para formar un char."

decodeStr :: [Word8] -> (Bytecode,[Word8])
decodeStr [] = ([],[])
decodeStr ws | head ws == 0 = ([0], tail ws)
             | otherwise =
                let len = utf8LengthByLeader (head ws)
                    (remBc,remWords) = decodeStr (drop len ws)
                    fstBc = ord $ words8ToChr (take len ws) len
                in (fstBc : remBc, remWords)

read32BitInt :: [Word8] -> Int
read32BitInt [b1, b2, b3, b4] =
    let byte1 = fromIntegral b1
        byte2 = fromIntegral b2
        byte3 = fromIntegral b3
        byte4 = fromIntegral b4
    in byte4 `shiftL` 24 .|. byte3 `shiftL` 16 .|. byte2 `shiftL` 8 .|. byte1
read32BitInt _ = error "Se esperaban 4 bytes para formar un entero."

words8ToBc :: [Word8] -> Bytecode
words8ToBc [] = []
words8ToBc (b:bs) =
  let i = fromIntegral b in
  case opArgs i of
    -2 -> let (strBc, rm) = decodeStr bs
          in i : strBc ++ (words8ToBc rm)
    -1 -> [i]
    0 -> i : (words8ToBc bs)
    1 -> i : (read32BitInt (take 4 bs)) : (words8ToBc (drop 4 bs))
    _ -> []

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
  runBC' c e ((I (max (m-n) 0)):s)

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