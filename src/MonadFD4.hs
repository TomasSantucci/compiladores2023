{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE FlexibleContexts #-}
{-# OPTIONS_GHC -Wno-name-shadowing #-}
{-# OPTIONS_GHC -Wno-unrecognised-pragmas #-}
{-# HLINT ignore "Use <$>" #-}

{-|
Module      : MonadFD4
Description : Mónada con soporte para estado, errores, e IO.
Copyright   : (c) Mauro Jaskelioff, Guido Martínez, 2020.
License     : GPL-3
Maintainer  : mauro@fceia.unr.edu.ar
Stability   : experimental

Definimos la clase de mónadas 'MonadFD4' que abstrae las mónadas con soporte para estado, errores e IO,
y la mónada 'FD4' que provee una instancia de esta clase.
-}

module MonadFD4 (
  FD4,
  runFD4,
  lookupDecl,
  lookupTy,
  printFD4,
  printFD4',
  setLastFile,
  getLastFile,
  setInter,
  getInter,
  getSynonyms,
  addSynonym,
  getMode,
  getOpt,
  getProf,
  getGlb,
  eraseLastFileDecls,
  failPosFD4,
  failFD4,
  addDecl,
  catchErrors,
  lookupEnv,
  updateGlbDecls,
  updateDecl,
  stepCEK,
  opBC,
  changeStack,
  countClos,
  MonadFD4,
  module Control.Monad.Except,
  module Control.Monad.State)
 where

import Common
import Lang
import Global
import Errors ( Error(..) )
import Control.Monad.State
import Control.Monad.Except
import Control.Monad.Reader
import System.IO

-- * La clase 'MonadFD4'

{-| La clase de mónadas 'MonadFD4' clasifica a las mónadas con soporte para una configuración Global 'Global.Conf', 
    para operaciones @IO@, estado de tipo 'Global.GlEnv', y errores de tipo 'Errors.Error'.

Las mónadas @m@ de esta clase cuentan con las operaciones:
   - @ask :: m Conf@
   - @get :: m GlEnv@
   - @put :: GlEnv -> m ()@
   - @throwError :: Error -> m a@
   - @catchError :: m a -> (Error -> m a) -> m a@
   - @liftIO :: IO a -> m a@

y otras operaciones derivadas de ellas, como por ejemplo
   - @modify :: (GlEnv -> GlEnv) -> m ()@
   - @gets :: (GlEnv -> a) -> m a@  
-}
class (MonadIO m, MonadState GlEnv m, MonadError Error m, MonadReader Conf m) => MonadFD4 m where

getOpt :: MonadFD4 m => m Bool
getOpt = asks opt

getMode :: MonadFD4 m => m Mode
getMode = asks modo

getProf :: MonadFD4 m => m Bool
getProf = asks prof

getGlb :: MonadFD4 m => m [Decl TTerm]
getGlb = gets glb

setInter :: MonadFD4 m => Bool -> m ()
setInter b = modify (\s-> s {inter = b})

getInter :: MonadFD4 m => m Bool
getInter = gets inter

getSynonyms :: MonadFD4 m => m [(Name,Ty)]
getSynonyms = gets synonyms

addSynonym :: MonadFD4 m => Name -> Ty -> m ()
addSynonym n ty = modify (\s -> s { synonyms = (n,ty):synonyms s })

printFD4 :: MonadFD4 m => String -> m ()
printFD4 = liftIO . putStrLn

printFD4' :: MonadFD4 m => String -> m ()
printFD4' = liftIO . putStr

setLastFile :: MonadFD4 m => FilePath -> m ()
setLastFile filename = modify (\s -> s {lfile = filename , cantDecl = 0})

getLastFile :: MonadFD4 m => m FilePath
getLastFile = gets lfile

addDecl :: MonadFD4 m => Decl TTerm -> m ()
addDecl d = modify (\s -> s { glb = glb s ++ [d], cantDecl = cantDecl s + 1 })

eraseLastFileDecls :: MonadFD4 m => m ()
eraseLastFileDecls = do
      s <- get
      let n = cantDecl s
          (_,rem) = splitAt n (glb s)
      modify (\s -> s {glb = rem, cantDecl = 0})

lookupDecl :: MonadFD4 m => Name -> m (Maybe TTerm)
lookupDecl nm = do
     s <- get
     case filter (hasName nm) (glb s) of
       (Decl { declBody=e }):_ -> return (Just e)
       [] -> return Nothing
   where hasName :: Name -> Decl a -> Bool
         hasName nm (Decl { declName = nm' }) = nm == nm'

lookupTy :: MonadFD4 m => Name -> m (Maybe Ty)
lookupTy nm = do
      s <- get
      return $ lookup nm (tyEnv s)

lookupEnv :: MonadFD4 m => Name -> m (Maybe CEKEnv)
lookupEnv nm = do
      s <- get
      return $ lookup nm (declEnvs s)

failPosFD4 :: MonadFD4 m => Pos -> String -> m a
failPosFD4 p s = throwError (ErrPos p s)

failFD4 :: MonadFD4 m => String -> m a
failFD4 = failPosFD4 NoPos

catchErrors :: MonadFD4 m => m a -> m (Maybe a)
catchErrors c = catchError (Just <$> c)
                           (\e -> liftIO $ hPrint stderr e
                              >> return Nothing)

updateGlbDecls :: MonadFD4 m => [Decl TTerm] -> m ()
updateGlbDecls ds = modify (\s -> s {glb = ds, cantDecl = length ds})

updateDecl :: MonadFD4 m => Name -> TTerm -> m ()
updateDecl name t = modify (\s -> s {glb = replace (glb s) name t })
  where replace [] name t = []
        replace (d@(Decl i r n ty _):ds) name t | name == n = Decl i r n ty t:ds
        replace (d@(Decl i r n ty _):ds) name t | otherwise = d: replace ds name t

stepCEK :: MonadFD4 m => m ()
stepCEK = modify (\s -> s { stepsCEK = stepsCEK s + 1 })

opBC :: MonadFD4 m => m ()
opBC = modify (\s -> s { opsBC = opsBC s + 1 })

changeStack :: MonadFD4 m => (Int -> Int) -> m ()
changeStack f =
      modify (\s -> s { maxStackSize = max (maxStackSize s) (f (currStackSize s)),
                        currStackSize = f (currStackSize s) })

countClos :: MonadFD4 m => m ()
countClos = modify (\s -> s { clos = clos s + 1 })

----
-- Importante, no eta-expandir porque GHC no hace una
-- eta-contracción de sinónimos de tipos
-- y Main no va a compilar al escribir `InputT FD4 ()`

-- | El tipo @FD4@ es un sinónimo de tipo para una mónada construida usando dos transformadores de mónada sobre la mónada @IO@.
-- El transformador de mónad @ExcepT Error@ agrega a la mónada IO la posibilidad de manejar errores de tipo 'Errors.Error'.
-- El transformador de mónadas @StateT GlEnv@ agrega la mónada @ExcepT Error IO@ la posibilidad de manejar un estado de tipo 'Global.GlEnv'.
type FD4 = ReaderT Conf (StateT GlEnv (ExceptT Error IO))

-- | Esta es una instancia vacía, ya que 'MonadFD4' no tiene funciones miembro.
instance MonadFD4 FD4

-- 'runFD4\'' corre una computación de la mónad 'FD4' en el estado inicial 'Global.initialEnv' 
runFD4' :: FD4 a -> Conf -> IO (Either Error (a, GlEnv))
runFD4' c conf =  runExceptT $ runStateT (runReaderT c conf)  initialEnv

runFD4:: FD4 a -> Conf -> IO (Either Error a)
runFD4 c conf = fmap fst <$> runFD4' c conf