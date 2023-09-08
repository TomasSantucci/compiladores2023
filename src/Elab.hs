{-|
Module      : Elab
Description : Elabora un término fully named a uno locally closed.
Copyright   : (c) Mauro Jaskelioff, Guido Martínez, 2020.
License     : GPL-3
Maintainer  : mauro@fceia.unr.edu.ar
Stability   : experimental

Este módulo permite elaborar términos y declaraciones para convertirlas desde
fully named (@STerm) a locally closed (@Term@)
-}

module Elab ( elab, elabDecl) where

import Common ( Pos )

import Lang
import Subst
import MonadFD4

-- | 'elab' transforma variables ligadas en índices de de Bruijn
-- en un término dado. 
elab :: (MonadFD4 m) => STerm -> m Term
elab = elab' [] 

elab' :: (MonadFD4 m) => [Name] -> STerm -> m Term
elab' env (SV p v) =
  -- Tenemos que ver si la variable es Global o es un nombre local
  -- En env llevamos la lista de nombres locales.
  if v `elem` env 
    then  return (V p (Free v))
    else  return (V p (Global v))

elab' _ (SConst p c) = return $ (Const p c)

elab' env (SLam p [(v,ty)] t) = do
  t' <- (elab' (v:env) t)
  ty' <- elabTy p ty
  return $ Lam p v ty' (close v t')
elab' env (SLam p ((v,ty):bs) t) = do 
  t' <- (elab' (v:env) (SLam p bs t))
  ty' <- elabTy p ty
  return $ Lam p v ty' (close v t')

-- falta caso error sin argumentos?
elab' env (SFix p (f,fty) [(x,xty)] t) = do
  t' <- (elab' (x:f:env) t)
  fty' <- elabTy p fty
  xty' <- elabTy p xty
  return $ Fix p f fty' x xty' (close2 f x t')
  
elab' env (SFix p (f,fty) ((x,xty):bs) t) = do
  t' <- elab' (x:f:env) (SLam p bs t)
  fty' <- elabTy p fty
  xty' <- elabTy p xty
  return $ Fix p f fty' x xty' (close2 f x t')

elab' env (SIfZ p c t e) = do
  t1 <- (elab' env c)
  t2 <- (elab' env t)
  t3 <- (elab' env e)
  return $ IfZ p t1 t2 t3
-- Operadores binarios
elab' env (SBinaryOp i o t u) = do
  t1 <- elab' env t
  t2 <- elab' env u
  return $ BinaryOp i o t1 t2
-- Operador Print
elab' env (SPrint i str t) = do
  t' <- elab' env t
  return $ Print i str t'
-- Aplicaciones generales
elab' env (SApp p h a) = do
  t1 <- (elab' env h)
  t2 <- (elab' env a)
  return $ App p t1 t2

elab' env (SLet parens False p (v,vty) [] def body) = do
  t1 <- (elab' env def)
  t2 <- (elab' (v:env) body) 
  vty' <- elabTy p vty
  return $ Let p v vty' t1 (close v t2)

elab' env (SLet parens False p (v,vty) (b:bs) def body) = do
  def' <- (elab' env (SLam p (b:bs) def))
  vty' <- (getFunType p (map snd (b:bs)) vty)
  body' <- (elab' (v:env) body)
  return $ Let p v vty' def' (close v body') --CHEAQUEAR LA POSICION TODO

elab' env (SLet parens True p (v,vty) [(x,xty)] def body) =do
  vty' <- (getFunType p [xty] vty)
  xty' <- elabTy p xty
  t' <- elab' env def
--  def' <- (elab' env (SFix p (v,vty') [(x,xty)] def))
  let def' = Fix p v vty' x xty' (close2 v x t')
  body' <- (elab' (v:env) body)
  return $ Let p v vty' def' (close v body')

elab' env (SLet parens True p (f,rty) ((x,xty):bs) def body) = do
  fty <- getFunSType (map snd bs) rty
  let def' = SLam p bs def
  elab' env (SLet parens True p (f,fty) [(x,xty)] def' body)
 
elabTy :: (MonadFD4 m) => Pos -> STy -> m Ty
elabTy _ SNatTy = return $ NatTy Nothing

elabTy p (SFunTy sty1 sty2) = do
  t1 <- elabTy p sty1
  t2 <- elabTy p sty2
  return $ FunTy t1 t2 Nothing

elabTy p (SSyn n) = do
  s <- getSynonyms
  case lookup n s of
    Nothing -> failPosFD4 p ("Sinónimo de tipo (" ++ n ++ ") no definido.")
    Just ty -> return ty

getFunType :: (MonadFD4 m) => Pos -> [STy] -> STy -> m Ty
getFunType p [] ty = elabTy p ty
getFunType p (t:ts) ty = do
  t' <- elabTy p t
  ts' <- getFunType p ts ty
  return $ FunTy t' ts' Nothing

getFunSType :: (MonadFD4 m) => [STy] -> STy -> m STy
getFunSType [] sty = return sty
getFunSType (t:ts) sty = do
  ts' <- getFunSType ts sty
  return $ SFunTy t ts'

elabDecl :: (MonadFD4 m) => SDecl -> m (Maybe (Decl Term))
elabDecl (SDefType p n sty) = do
  s <- getSynonyms
  case lookup n s of
    Nothing -> do ty <- elabTy p sty
                  addSynonym n ty
    Just _ -> failPosFD4 p ("Type " ++ n ++ " already defined.")
  return Nothing

elabDecl (SDecl p v vty [] False t) = do
  t' <- elab t
  vty' <- elabTy p vty
  return $ Just $ Decl p v vty' t'

elabDecl (SDecl p f rty bs False t) = do
  fty <- getFunType p (map snd bs) rty
  t' <- elab (SLam p bs t)
  return $ Just $ Decl p f fty t'

elabDecl (SDecl p f rty [(x,xty)] True t) = do
  fty <- getFunType p [xty] rty
  sfty <- getFunSType [xty] rty
  t' <- elab (SFix p (f,sfty) [(x,xty)] t)
  return $ Just $ Decl p f fty t'

elabDecl (SDecl p f rty ((x,xty):bs) True t) = do
  fty <- getFunSType (map snd bs) rty
  let t' = (SLam p bs t)
  elabDecl (SDecl p f fty [(x,xty)] True t')

