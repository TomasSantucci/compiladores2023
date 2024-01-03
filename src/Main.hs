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
    go (mode, opt, prof, files) = if prof then runProfMode mode opt files
                                  else runDefaultMode mode opt files

    runProfMode :: Mode -> Bool -> [FilePath] -> IO ()
    runProfMode Bytecompile opt files = runOrFailProf (Conf opt Bytecompile True) (mapM_ bytecompileFile files)
    runProfMode RunVM opt files = runOrFailProf (Conf opt RunVM True) (mapM_ runVMFile files)
    runProfMode CEK opt files = runOrFailProf (Conf opt CEK True) $ mapM_ compileCEK files
    runProfMode Typecheck opt files = runOrFailProf (Conf opt Typecheck True) $ mapM_ compileTypeCheck files
    runProfMode CC opt files = runOrFailProf (Conf opt CC True) $ mapM_ compileCC files
    runProfMode m opt files = runOrFailProf (Conf opt m True) $ mapM_ compileFile files

    runDefaultMode :: Mode -> Bool -> [FilePath] -> IO ()
    runDefaultMode InteractiveCEK opt files = runOrFail (Conf opt InteractiveCEK False) (runInputT defaultSettings (repl files))
    runDefaultMode Interactive opt files = runOrFail (Conf opt Interactive False) (runInputT defaultSettings (repl files))
    runDefaultMode Bytecompile opt files = runOrFail (Conf opt Bytecompile False) (mapM_ bytecompileFile files)
    runDefaultMode RunVM opt files = runOrFail (Conf opt RunVM False) (mapM_ runVMFile files)
    runDefaultMode CEK opt files = runOrFail (Conf opt CEK False) $ mapM_ compileCEK files
    runDefaultMode Typecheck opt files = runOrFail (Conf opt Typecheck False) $ mapM_ compileTypeCheck files
    runDefaultMode CC opt files = runOrFail (Conf opt CC False) $ mapM_ compileCC files
    runDefaultMode m opt files = runOrFail (Conf opt m False) $ mapM_ compileFile files

runOrFail :: Conf -> FD4 a -> IO a
runOrFail c m = do
  r <- runFD4 m c
  case r of
    Left err -> do
      liftIO $ hPrint stderr err
      exitWith (ExitFailure 1)
    Right v -> return v

runOrFailProf :: Conf -> FD4Prof a -> IO a
runOrFailProf c m = do
  r <- runFD4Prof m c
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

compileCEK :: MonadFD4 m => FilePath -> m ()
compileCEK f = do
    decls <- loadFile f
    mapM_ handleDecl decls
    s1 <- get
    opt <- getOpt
    when opt $ optimization 10 (glb s1)
    s2 <- get
    mapM_ evalAndUpdate (glb s2)
    prof <- getProf
    s3 <- get
    when prof $ printFD4 $ "Maquina CEK ejectuto en " ++ (show (stepsCEK s3)) ++ " pasos"
  where
    evalAndUpdate (Decl _ _ name _ body) = do t' <- evalCEK body
                                              updateDecl name t'
    getBody (Decl _ _ _ _ body) = body

compileCC :: MonadFD4 m => FilePath -> m ()
compileCC f = do
    decls <- loadFile f
    mapM_ handleDecl decls
    s1 <- get
    opt <- getOpt
    when opt $ optimization 10 (glb s1)
    s2 <- get
    let s = ir2C $ IrDecls $ runCC (glb s2)
    liftIO $ writeFile "out.c" s

compileTypeCheck :: MonadFD4 m => FilePath -> m ()
compileTypeCheck f = do
    printFD4 ("Chequeando tipos de "++f)
    decls <- loadFile f
    mapM_ handleDecl decls
    s1 <- get
    opt <- getOpt
    when opt $ optimization 10 (glb s1)
    s2 <- get
    mapM_ printDecls (glb s2)
  where printDecls d = ppDecl d >>= printFD4

compileFile ::  MonadFD4 m => FilePath -> m ()
compileFile f = do
    i <- getInter
    setInter False
    when i $ printFD4 ("Abriendo "++f++"...")
    decls <- loadFile f
    mapM_ handleDecl decls
    setInter i

bytecompileFile ::  MonadFD4 m => FilePath -> m ()
bytecompileFile f = do
    printFD4 ("Abriendo "++f++"...")
    decls <- loadFile f
    mapM_ handleDecl decls
    s <- get
    opt <- getOpt
    when opt $ optimization 10 (glb s)
    s1 <- get
    bc <- bytecompileModule (glb s1)
    let f' = reverse (drop 3 (reverse f))
    liftIO $ bcWrite bc (f' ++ "bc8")
    printFD4 ("Compilado a bytecode correctamente en "++f'++"bc8")

runVMFile ::  MonadFD4 m => FilePath -> m ()
runVMFile f = do
    bc <- liftIO $ bcRead f
    runBC bc
    prof <- getProf
    s <- get
    when prof $ printBCStats s
  where printBCStats s = do printFD4 $ "Operaciones ejecutadas: " ++ (show (opsBC s))
                            printFD4 $ "Tamano maximo del stack: " ++ (show (maxStackSize s))
                            printFD4 $ "Cantidad de clausuras creadas: " ++ (show (clos s))

parseIO ::  MonadFD4 m => String -> P a -> String -> m a
parseIO filename p x = case runP p x filename of
                  Left e  -> throwError (ParseErr e)
                  Right r -> return r

evalDecl :: MonadFD4 m => Decl TTerm -> m (Decl TTerm)
evalDecl (Decl p r x ty e) = do
    e' <- eval e
    return (Decl p r x ty e')

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
        (Decl p r x ty tt) <- tcDecl d
        te <- evalCEK tt
        addDecl (Decl p r x ty te)
    Interactive -> do
        (Decl p r x ty tt) <- tcDecl d
        te <- eval tt
        addDecl (Decl p r x ty te)
    Typecheck -> do
        f <- getLastFile
        td <- tcDecl d
        addDecl td
    Eval -> do
        td <- tcDecl d
        -- td' <- if opt then optimizeDecl td else return td
        ed <- evalDecl td
        addDecl ed
    CEK -> do
        (Decl p r x ty tt) <- tcDecl d
        addDecl (Decl p r x ty tt)
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
                 ->  do  return (f t)
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
