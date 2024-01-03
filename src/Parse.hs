{-# OPTIONS_GHC -Wno-unrecognised-pragmas #-}
{-# HLINT ignore "Use <$>" #-}
{-|
Module      : Parse
Description : Define un parser de términos FD40 a términos fully named.
Copyright   : (c) Mauro Jaskelioff, Guido Martínez, 2020.
License     : GPL-3
Maintainer  : mauro@fceia.unr.edu.ar
Stability   : experimental

-}

module Parse (tm, Parse.parse, decl, runP, P, program, declOrTm) where

import Prelude hiding ( const )
import Lang hiding (getPos)
import Common
import Text.Parsec hiding (runP,parse)
--import Data.Char ( isNumber, ord )
import qualified Text.Parsec.Token as Tok
import Text.ParserCombinators.Parsec.Language --( GenLanguageDef(..), emptyDef )
import qualified Text.Parsec.Expr as Ex
import Text.Parsec.Expr (Operator, Assoc)
import Control.Monad.Identity (Identity)

type P = Parsec String ()

-----------------------
-- Lexer
-----------------------
-- | Analizador de Tokens
lexer :: Tok.TokenParser u
lexer = Tok.makeTokenParser langDef

langDef :: LanguageDef u
langDef = emptyDef {
         commentLine    = "#",
         reservedNames = ["let", "rec","fun", "fix", "then", "else","in",
                           "ifz", "print","Nat","type"],
         reservedOpNames = ["->",":","=","+","-"]
        }

whiteSpace :: P ()
whiteSpace = Tok.whiteSpace lexer

natural :: P Integer 
natural = Tok.natural lexer

stringLiteral :: P String
stringLiteral = Tok.stringLiteral lexer

parens :: P a -> P a
parens = Tok.parens lexer

identifier :: P String
identifier = Tok.identifier lexer

reserved :: String -> P ()
reserved = Tok.reserved lexer

reservedOp :: String -> P ()
reservedOp = Tok.reservedOp lexer

tyIdentifier :: P String
tyIdentifier = Tok.lexeme lexer $ do
  c  <- upper
  cs <- many (identLetter langDef)
  return (c:cs)

-----------------------
-- Parsers
-----------------------

num :: P Int
num = fromInteger <$> natural

var :: P Name
var = identifier

getPos :: P Pos
getPos = do pos <- getPosition
            return $ Pos (sourceLine pos) (sourceColumn pos)

tyatom :: P STy
tyatom = (reserved "Nat" >> return SNatTy)
         <|> parens typeP
         <|> do n <- identifier
                return (SSyn n)

typeP :: P STy
typeP = try (do 
          x <- tyatom
          reservedOp "->"
          y <- typeP
          return (SFunTy x y))
      <|> tyatom
          
const :: P Const
const = CNat <$> num

printOp :: P STerm
printOp = do
  i <- getPos
  reserved "print"
  str <- option "" stringLiteral
  a <- atom
  return (SPrint i str a)

printOpFun :: P STerm
printOpFun = do
  i <- getPos
  reserved "print"
  str <- option "" stringLiteral
  return (SPrintFun i str)

binary :: String -> BinaryOp -> Assoc -> Operator String () Identity STerm
binary s f = Ex.Infix (reservedOp s >> return (SBinaryOp NoPos f))

table :: [[Operator String () Identity STerm]]
table = [[binary "+" Add Ex.AssocLeft,
          binary "-" Sub Ex.AssocLeft]]

expr :: P STerm
expr = Ex.buildExpressionParser table tm

atom :: P STerm
atom =     (flip SConst <$> const <*> getPos)
       <|> flip SV <$> var <*> getPos
       <|> parens expr
       <|> printOp

-- parsea un par (variable : tipo)
binding :: P (Name, STy)
binding = do
  v <- var
  reservedOp ":"
  ty <- typeP
  return (v, ty)

multibinding :: P [(Name, STy)]
multibinding = do
  v <- many1 var
  reservedOp ":"
  ty <- typeP
  let res = map (\c -> (c,ty)) v
  return res

bindings :: P [(Name, STy)]
bindings = do res <- many1 (parens multibinding)
              return (concat res)

lam :: P STerm
lam = do i <- getPos
         reserved "fun"
         bs <- bindings
         reservedOp "->"
         t <- expr
         return (SLam i bs t)

-- Nota el parser app también parsea un solo atom.
app :: P STerm
app = do i <- getPos
         f <- atom
         args <- many atom
         return (foldl (SApp i) f args)

ifz :: P STerm
ifz = do i <- getPos
         reserved "ifz"
         c <- expr
         reserved "then"
         t <- expr
         reserved "else"
         e <- expr
         return (SIfZ i c t e)

fix :: P STerm
fix = do i <- getPos
         reserved "fix"
         (f, fty) <- parens binding
         bs <- bindings
         reservedOp "->"
         t <- expr
         return (SFix i (f,fty) bs t)

letexpRec :: P STerm
letexpRec = do
  i <- getPos
  reserved "let"
  reserved "rec"
  v <- identifier
  bs <- bindings
  reservedOp ":"
  ty <- typeP
  reservedOp "="  
  def <- expr
  reserved "in"
  body <- expr
  return (SLet False True i (v,ty) bs def body)

letexpFun :: P STerm
letexpFun = do
  i <- getPos
  reserved "let"
  v <- identifier
  bs <- bindings
  reservedOp ":"
  ty <- typeP
  reservedOp "="  
  def <- expr
  reserved "in"
  body <- expr
  return (SLet False False i (v,ty) bs def body)

letexpParens :: P STerm
letexpParens = do
  i <- getPos
  reserved "let"
  (v,ty) <- parens binding
  reservedOp "="  
  def <- expr
  reserved "in"
  body <- expr
  return (SLet True False i (v,ty) [] def body)

letexpCore :: P STerm
letexpCore = do
  i <- getPos
  reserved "let"
  (v,ty) <- binding
  reservedOp "="  
  def <- expr
  reserved "in"
  body <- expr
  return (SLet False False i (v,ty) [] def body)

letexp :: P STerm
letexp = try letexpCore
         <|> try letexpFun
         <|> try letexpParens
         <|> try letexpRec

-- | Parser de términos
tm :: P STerm
tm = try letexp
     <|> try app
     <|> try lam
     <|> try ifz
     <|> try printOp
     <|> try printOpFun
     <|> fix

-- | Parser de declaraciones
declCore :: P SDecl
declCore = do 
     i <- getPos
     reserved "let"
     (v,ty) <- binding
     reservedOp "="
     t <- expr
     return (SDecl i v ty [] False t)

declRec :: P SDecl
declRec = do 
     i <- getPos
     reserved "let"
     reserved "rec"
     v <- var
     bs <- bindings
     reservedOp ":"
     ty <- typeP
     reservedOp "="
     t <- expr
     return (SDecl i v ty bs True t)

declFun :: P SDecl
declFun = do 
     i <- getPos
     reserved "let"
     v <- var
     bs <- bindings
     reservedOp ":"
     ty <- typeP
     reservedOp "="
     t <- expr
     return (SDecl i v ty bs False t)

typeSyn :: P SDecl
typeSyn = do
     i <- getPos
     reserved "type"
     v <- var
     reservedOp "="
     ty <- typeP
     return (SDefType i v ty)

decl :: P SDecl
decl = try declCore 
       <|> try declRec
       <|> try declFun
       <|> try typeSyn

-- | Parser de programas (listas de declaraciones) 
program :: P [SDecl]
program = many decl

-- | Parsea una declaración a un término
-- Útil para las sesiones interactivas
declOrTm :: P (Either SDecl STerm)
declOrTm =  try (Right <$> expr) <|> (Left <$> decl)

-- Corre un parser, chequeando que se pueda consumir toda la entrada
runP :: P a -> String -> String -> Either ParseError a
runP p s filename = runParser (whiteSpace *> p <* eof) () filename s

--para debugging en uso interactivo (ghci)
parse :: String -> STerm
parse s = case runP expr s "" of
            Right t -> t
            Left e -> error ("no parse: " ++ show s)
