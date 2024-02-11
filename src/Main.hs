{-# LANGUAGE RecordWildCards #-}

{-|
Module      : Main
Description : Compilador de FD4.
Copyright   : (c) Mauro Jaskelioff, Guido Martínez, 2020.
License     : GPL-3
Maintainer  : mauro@fceia.unr.edu.ar
Stability   : experimental

-}

module Main where

import System.Console.Haskeline ( defaultSettings, getInputLine, runInputT, InputT )
import Control.Monad.Catch (MonadMask)

--import Control.Monad
import Control.Monad.Trans
import Data.List (nub, isPrefixOf, intercalate )
import Data.Char ( isSpace )
import Control.Exception ( catch , IOException )
import System.IO ( hPrint, stderr, hPutStrLn )
import Data.Maybe ( fromMaybe )

import System.Exit ( exitWith, ExitCode(ExitFailure) )
import Options.Applicative

import Global
import Errors
import Lang
import Parse ( P, tm, program, declOrTm, runP )
import Elab ( elab, elabDecl )
import Eval ( eval )
import CEK ( evalCEK )
import PPrint ( pp , ppTy, ppDecl )
import MonadFD4
import TypeChecker ( tc, tcDecl )
import Bytecompile
import Optimization
import ClosureConvert
import IR
import C

prompt :: String
prompt = "FD4> "



-- | Parser de banderas
parseMode :: Parser (Mode,Bool,Bool)
parseMode = (,,) <$>
      (flag' Typecheck ( long "typecheck" <> short 't' <> help "Chequear tipos e imprimir el término")
      <|> flag' InteractiveCEK (long "interactiveCEK" <> short 'd' <> help "Ejecutar interactivamente en la CEK")
      <|> flag' CEK (long "cek" <> short 'k' <> help "Ejecutar CEK")
      <|> flag' Bytecompile (long "bytecompile" <> short 'm' <> help "Compilar a la BVM")
      <|> flag' RunVM (long "runVM" <> short 'r' <> help "Ejecutar bytecode en la BVM")
      <|> flag Interactive Interactive ( long "interactive" <> short 'i' <> help "Ejecutar en forma interactiva")
      <|> flag Eval        Eval        (long "eval" <> short 'e' <> help "Evaluar programa")
      <|> flag' CC ( long "cc" <> short 'c' <> help "Compilar a código C")
  -- <|> flag' Canon ( long "canon" <> short 'n' <> help "Imprimir canonicalización")
  -- <|> flag' Assembler ( long "assembler" <> short 'a' <> help "Imprimir Assembler resultante")
  -- <|> flag' Build ( long "build" <> short 'b' <> help "Compilar")
      )
   <*> flag False True (long "optimize" <> short 'o' <> help "Optimizar código")
   <*> flag False True (long "profile" <> short 'p' <> help "Optimizar código")

-- | Parser de opciones general, consiste de un modo y una lista de archivos a procesar
parseArgs :: Parser (Mode,Bool,Bool, [FilePath])
parseArgs = (\(a,b,c) d -> (a,b,c,d)) <$> parseMode <*> many (argument str (metavar "FILES..."))

main :: IO ()
main = execParser opts >>= go
  where
    opts = info (parseArgs <**> helper)
      ( fullDesc
     <> progDesc "Compilador de FD4"
     <> header "Compilador de FD4 de la materia Compiladores 2022" )

    go :: (Mode,Bool,Bool,[FilePath]) -> IO ()
    go (InteractiveCEK,opt,prof,files) =
              runOrFail (Conf opt InteractiveCEK prof) (runInputT defaultSettings (repl files))
    go (Interactive,opt,prof,files) =
              runOrFail (Conf opt Interactive prof) (runInputT defaultSettings (repl files))
    go (Bytecompile,opt,prof,files) =
              runOrFail (Conf opt Bytecompile prof) (mapM_ bytecompileFile files)
    go (RunVM,opt,prof,files) =
              runOrFail (Conf opt RunVM prof) (mapM_ runVMFile files)
    go (CEK,opt,prof,files) =
              runOrFail (Conf opt CEK prof) $ mapM_ compileCEK files
    go (Typecheck,opt,prof,files) =
              runOrFail (Conf opt Typecheck prof) $ mapM_ compileTypeCheck files
    go (CC,opt,prof,files) =
              runOrFail (Conf opt CC prof) $ mapM_ compileCC files
    go (Eval,opt,prof,files) =
              runOrFail (Conf opt Eval prof) $ mapM_ compileEval files
--  go (m,opt,prof,files) =
--            runOrFail (Conf opt m prof) $ mapM_ compileFile files

runOrFail :: Conf -> FD4 a -> IO a
runOrFail c m = do
  r <- runFD4 m c
  case r of
    Left err -> do
      liftIO $ hPrint stderr err
      exitWith (ExitFailure 1)
    Right v -> return v

repl :: (MonadFD4 m, MonadMask m) => [FilePath] -> InputT m ()
repl args = do
       lift $ setInter True
       lift $ catchErrors $ mapM_ compileFile args
       s <- lift get
       when (inter s) $ liftIO $ putStrLn
         (  "Entorno interactivo para FD4.\n"
         ++ "Escriba :? para recibir ayuda.")
       loop
  where loop = do
           minput <- getInputLine prompt
           case minput of
               Nothing -> return ()
               Just "" -> loop
               Just x -> do
                       c <- liftIO $ interpretCommand x
                       b <- lift $ catchErrors $ handleCommand c
                       maybe loop (`when` loop) b

loadFile ::  MonadFD4 m => FilePath -> m [SDecl]
loadFile f = do
    let filename = reverse (dropWhile isSpace (reverse f))
    x <- liftIO $ catch (readFile filename)
               (\e -> do let err = show (e :: IOException)
                         hPutStrLn stderr ("No se pudo abrir el archivo " ++ filename ++ ": " ++ err)
                         return "")
    setLastFile filename
    parseIO filename program x

-- Elaboracion, chequeo de tipos y optimizacion de un archivo
processFile :: MonadFD4 m => FilePath -> m Module
processFile f = do
    decls <- loadFile f
    mapM_ handleDecl decls
    decls1 <- getGlb
    opt <- getOpt
    when opt $ optimizeModule 10 decls1
    getGlb

compileCEK :: MonadFD4 m => FilePath -> m ()
compileCEK f = do
    decls <- processFile f
    mapM_ evalAndUpdate decls
    prof <- getProf
    s <- get
    when prof $ printFD4 $ "Maquina CEK ejectuto en " ++ show (stepsCEK s) ++ " pasos"
  where
    evalAndUpdate d = do t' <- evalCEK (declBody d)
                         updateDecl (declName d) t'

compileCC :: MonadFD4 m => FilePath -> m ()
compileCC f = do
    decls <- processFile f
    let s = ir2C $ IrDecls $ runCC decls
    liftIO $ writeFile "out.c" s

compileTypeCheck :: MonadFD4 m => FilePath -> m ()
compileTypeCheck f = do
    printFD4 ("Chequeando tipos de "++f)
    decls <- processFile f
    mapM_ printDecls decls
  where printDecls d = ppDecl d >>= printFD4

bytecompileFile ::  MonadFD4 m => FilePath -> m ()
bytecompileFile f = do
    printFD4 ("Abriendo "++f++"...")
    decls2 <- processFile f
    bc <- bytecompileModule decls2
    let f' = reverse (drop 3 (reverse f))
    liftIO $ bcWrite bc (f' ++ "bc8")
    printFD4 ("Compilado a bytecode correctamente en "++f'++"bc8")

compileEval :: MonadFD4 m => FilePath -> m ()
compileEval f = do
    decls <- processFile f
    mapM_ evalAndUpdate decls
  where
    evalAndUpdate d = do t' <- eval (declBody d)
                         updateDecl (declName d) t'

compileFile ::  MonadFD4 m => FilePath -> m ()
compileFile f = do
    i <- getInter
    setInter False
    when i $ printFD4 ("Abriendo "++f++"...")
    decls <- loadFile f
    mapM_ handleDecl decls
    setInter i

runVMFile ::  MonadFD4 m => FilePath -> m ()
runVMFile f = do
    bc <- liftIO $ bcRead f
    prof <- getProf
    if prof then runBCProf bc else runBC bc
    s <- get
    when prof $ printBCStats s
  where printBCStats s = do printFD4 $ "Operaciones ejecutadas: " ++ show (opsBC s)
                            printFD4 $ "Tamano maximo del stack: " ++ show (maxStackSize s)
                            printFD4 $ "Cantidad de clausuras creadas: " ++ show (clos s)

parseIO ::  MonadFD4 m => String -> P a -> String -> m a
parseIO filename p x = case runP p x filename of
                  Left e  -> throwError (ParseErr e)
                  Right r -> return r

handleDecl ::  MonadFD4 m => SDecl -> m ()
handleDecl dec = do
  dec' <- elabDecl dec
  case dec' of
    Nothing -> return ()
    Just d@(Decl p r x ty t) -> handleDecl' d

handleDecl' :: MonadFD4 m => Decl Term -> m ()
handleDecl' d = do
  m <- getMode
  case m of
    InteractiveCEK -> do
        tcd <- tcDecl d
        te <- evalCEK (declBody tcd)
        addDecl $ tcd {declBody = te}
    Interactive -> do
        tcd <- tcDecl d
        te <- eval (declBody tcd)
        addDecl $ tcd {declBody = te}
    Typecheck -> do
        tcd <- tcDecl d
        addDecl tcd
    Eval -> do
        tcd <- tcDecl d
        addDecl tcd
    CEK -> do
        tcd <- tcDecl d
        addDecl tcd
    Bytecompile -> do
        tcd <- tcDecl d
        addDecl tcd
    CC -> do
        tcd <- tcDecl d
        addDecl tcd
    _ ->
        return ()

data Command = Compile CompileForm
             | PPrint String
             | Type String
             | Reload
             | Browse
             | Quit
             | Help
             | Noop

data CompileForm = CompileInteractive  String
                 | CompileFile         String

data InteractiveCommand = Cmd [String] String (String -> Command) String

-- | Parser simple de comando interactivos
interpretCommand :: String -> IO Command
interpretCommand x
  =  if ":" `isPrefixOf` x then
       do  let  (cmd,t')  =  break isSpace x
                t         =  dropWhile isSpace t'
           --  find matching commands
           let  matching  =  filter (\ (Cmd cs _ _ _) -> any (isPrefixOf cmd) cs) commands
           case matching of
             []  ->  do  putStrLn ("Comando desconocido `" ++ cmd ++ "'. Escriba :? para recibir ayuda.")
                         return Noop
             [Cmd _ _ f _]
                 ->  return (f t)
             _   ->  do  putStrLn ("Comando ambigüo, podría ser " ++
                                   intercalate ", " ([ head cs | Cmd cs _ _ _ <- matching ]) ++ ".")
                         return Noop

     else
       return (Compile (CompileInteractive x))

commands :: [InteractiveCommand]
commands
  =  [ Cmd [":browse"]      ""        (const Browse) "Ver los nombres en scope",
       Cmd [":load"]        "<file>"  (Compile . CompileFile)
                                                     "Cargar un programa desde un archivo",
       Cmd [":print"]       "<exp>"   PPrint          "Imprime un término y sus ASTs sin evaluarlo",
       Cmd [":reload"]      ""        (const Reload)         "Vuelve a cargar el último archivo cargado",
       Cmd [":type"]        "<exp>"   Type           "Chequea el tipo de una expresión",
       Cmd [":quit",":Q"]        ""        (const Quit)   "Salir del intérprete",
       Cmd [":help",":?"]   ""        (const Help)   "Mostrar esta lista de comandos" ]

helpTxt :: [InteractiveCommand] -> String
helpTxt cs
  =  "Lista de comandos:  Cualquier comando puede ser abreviado a :c donde\n" ++
     "c es el primer caracter del nombre completo.\n\n" ++
     "<expr>                  evaluar la expresión\n" ++
     "let <var> = <expr>      definir una variable\n" ++
     unlines (map (\ (Cmd c a _ d) ->
                   let  ct = intercalate ", " (map (++ if null a then "" else " " ++ a) c)
                   in   ct ++ replicate ((24 - length ct) `max` 2) ' ' ++ d) cs)

-- | 'handleCommand' interpreta un comando y devuelve un booleano
-- indicando si se debe salir del programa o no.
handleCommand ::  MonadFD4 m => Command  -> m Bool
handleCommand cmd = do
   s@GlEnv {..} <- get
   case cmd of
       Quit   ->  return False
       Noop   ->  return True
       Help   ->  printFD4 (helpTxt commands) >> return True
       Browse ->  do  printFD4 (unlines (reverse (nub (map declName glb))))
                      return True
       Compile c ->
                  do  case c of
                          CompileInteractive e -> compilePhrase e
                          CompileFile f        -> compileFile f
                      return True
       Reload ->  eraseLastFileDecls >> (getLastFile >>= compileFile) >> return True
       PPrint e   -> printPhrase e >> return True
       Type e    -> typeCheckPhrase e >> return True

compilePhrase ::  MonadFD4 m => String -> m ()
compilePhrase x = do
    dot <- parseIO "<interactive>" declOrTm x
    case dot of
      Left d  -> handleDecl d
      Right t -> do
        m <- getMode
        handleTerm t (evalFun m)
  where evalFun Interactive = eval
        evalFun InteractiveCEK = evalCEK
        evalFun _ = eval

handleTerm ::  MonadFD4 m => STerm -> (TTerm -> m TTerm)-> m ()
handleTerm t evalFun = do
         t' <- elab t
         s <- get
         tt <- tc t' (tyEnv s)
         te <- evalFun tt
         ppte <- pp te
         printFD4 (ppte ++ " : " ++ ppTy (getTy tt))

printPhrase   :: MonadFD4 m => String -> m ()
printPhrase x =
  do
    x' <- parseIO "<interactive>" tm x
    ex <- elab x'
    tyenv <- gets tyEnv
    tex <- tc ex tyenv
    t  <- case x' of
           (SV p f) -> fromMaybe tex <$> lookupDecl f
           _       -> return tex
    printFD4 "STerm:"
    printFD4 (show x')
    printFD4 "TTerm:"
    printFD4 (show t)

typeCheckPhrase :: MonadFD4 m => String -> m ()
typeCheckPhrase x = do
         t <- parseIO "<interactive>" tm x
         t' <- elab t
         s <- get
         tt <- tc t' (tyEnv s)
         let ty = getTy tt
         printFD4 (ppTy ty)
