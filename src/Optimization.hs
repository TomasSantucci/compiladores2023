{-# OPTIONS_GHC -Wno-unrecognised-pragmas #-}
{-# HLINT ignore "Redundant return" #-}
module Optimization where

import MonadFD4
import Lang
import Subst
import Data.List (find)

optimization :: MonadFD4 m => Int -> Module ->  m ()
optimization 0 m = updateGlbDecls m
optimization n m = do
  m' <- moduleOptimization m
  optimization (n-1) m'

moduleOptimization :: MonadFD4 m => Module -> m Module
moduleOptimization m = do
  decls1 <- inline m
  decls2 <- dceDec decls1
  mapM constFoldingProp decls2

applyRec :: MonadFD4 m => TTerm -> (TTerm -> m TTerm) -> m TTerm
applyRec t@(Const {}) f = return t
applyRec t@(V {}) f = return t
applyRec (Lam i n ty sc) f = do
    t' <- f $ open n sc
    return $ Lam i n ty $ close n t'

applyRec (App i t1 t2) f = do
    t1' <- f t1
    t2' <- f t2
    return $ App i t1' t2'

applyRec (Print i s t) f= do
    t' <- f t
    return $ Print i s t'

applyRec (Fix i n nty m mty sc) f= do
    t' <- f $ open2 n m sc
    return $ Fix i n nty m mty $ close2 n m t'

applyRec (BinaryOp i op t1 t2) f = do
    t1' <- f t1
    t2' <- f t2
    return $ BinaryOp i op t1' t2'

applyRec (IfZ i t1 t2 t3) f = do
    t1' <- f t1
    t2' <- f t2
    t3' <- f t3
    return $ IfZ i t1' t2' t3'

applyRec (Let i n ty t1 sc) f = do
    t1' <- f t1
    t2' <- f $ open n sc
    return $ Let i n ty t1' $ close n t2'

constFoldingProp :: MonadFD4 m => Decl TTerm -> m (Decl TTerm)
constFoldingProp (Decl p r s ty t) = do
  t1 <- propagation t
  t2 <- constFolding t1
  return (Decl p r s ty t2)

constFolding :: MonadFD4 m => TTerm -> m TTerm
constFolding (BinaryOp i op t1 t2) = do
  t1' <- constFolding t1
  t2' <- constFolding t2
  case (t1' ,t2', op) of
      (_,Const _ (CNat 0),_) -> return t1'
      (Const _ (CNat 0),_,Add) -> return t2'
      (Const _ (CNat 0),_,Sub) -> return t1'
      (Const _ (CNat n),Const _ (CNat m) ,_ ) -> return (Const i (CNat (semOp op n m)))
      _ -> return (BinaryOp i op t1' t2')
constFolding (IfZ i t1 t2 t3) = do
  t1' <- constFolding t1
  t2' <- constFolding t2
  t3' <- constFolding t3
  case t1' of
      (Const _ (CNat 0)) -> return t2'
      (Const _ _) -> return t3'
      _ -> return (IfZ i t1' t2' t3')

constFolding t = applyRec t constFolding

propagation :: MonadFD4 m => TTerm -> m TTerm
propagation (Let i n ty def sc@(Sc1 body)) = do
  def' <- propagation def
  case def' of
    Const {} -> propagation $ subst def' sc
    _ -> do body' <- propagation body
            return $ Let i n ty def' (Sc1 body')

propagation t = applyRec t propagation

hasPrint :: TTerm -> Bool
hasPrint (Print {}) = True
hasPrint (BinaryOp _ _ t1 t2) = hasPrint t1 || hasPrint t2
hasPrint (IfZ _ c t e) = hasPrint c || hasPrint t || hasPrint e
hasPrint (Let _ _ _ def (Sc1 body)) = hasPrint def || hasPrint body
hasPrint (App _ (Lam _ _ _ (Sc1 t1)) t2) = hasPrint t1 || hasPrint t2
hasPrint (App _ (Fix _ _ _ _ _ (Sc2 t1)) t2) = hasPrint t1 || hasPrint t2
hasPrint _ = False

isVarUsed :: TTerm -> Bool
isVarUsed tt = go tt 0
  where go :: TTerm -> Int -> Bool
        go (V _ (Bound i)) d = i == d
        go (V _ _) d = False
        go (Const _ _) d = False
        go (Lam _ _ ty (Sc1 t)) d = go t (d+1)
        go (App _ t1 t2) d = go t1 d || go t2 d
        go (Print _ _ t) d = go t d
        go (BinaryOp _ _ t1 t2) d = go t1 d || go t2 d
        go (Fix _ _ _ _ _ (Sc2 t)) d = go t (d+2)
        go (IfZ _ t1 t2 t3) d = go t1 d || go t2 d || go t3 d
        go (Let _ _ _ t1 (Sc1 t2)) d = go t1 d || go t2 (d+1)

dceTerm :: TTerm -> TTerm
dceTerm (V p var) = V p var

dceTerm (Const p n) = Const p n

dceTerm (Lam p x xty (Sc1 body)) =
  Lam p x xty (Sc1 (dceTerm body))

dceTerm (App p t1 t2) =
  App p (dceTerm t1) (dceTerm t2)

dceTerm (Print p s t) =
  Print p s (dceTerm t)

dceTerm (BinaryOp p op t1 t2) =
  BinaryOp p op (dceTerm t1) (dceTerm t2)

dceTerm (Fix p f fty x xty (Sc2 t)) =
  Fix p f fty x xty (Sc2 (dceTerm t))

dceTerm (IfZ p cond t1 t2) =
  IfZ p (dceTerm cond) (dceTerm t1) (dceTerm t2)

dceTerm t@(Let p x xty def (Sc1 body)) =
  let body' = dceTerm body
  in if isVarUsed body' || hasPrint def
     then Let p x xty (dceTerm def) (Sc1 body')
     else body'

dceDec :: MonadFD4 m => Module -> m Module
dceDec [] = return []
dceDec (dec:decs) = do
  decs' <- dceDec decs
  let occursLater = any (globalVarSearch (declName dec) . declBody) decs'
      dec' = dceTerm <$> dec
  if occursLater || hasPrint (declBody dec')
    then return (dec':decs')
    else return decs'

countNodes :: TTerm -> Int
countNodes (V _ (Global n)) = 1
countNodes (V _ _) = 1
countNodes (Const _ _) = 1
countNodes (Lam _ _ _ (Sc1 t)) = 1 + countNodes t
countNodes (App _ t1 t2) = countNodes t1 + countNodes t2 + 1
countNodes (Print _ _ t) = countNodes t + 1
countNodes (BinaryOp _ _ t1 t2) = countNodes t1 + countNodes t2 + 1
countNodes (Fix _ _ _ _ _ (Sc2 t)) = 1 + countNodes t
countNodes (IfZ _ t1 t2 t3) = countNodes t1 + countNodes t2 + countNodes t3 + 1
countNodes (Let _ x _ def (Sc1 body)) = countNodes def + countNodes body + 1

inline :: MonadFD4 m => Module -> m Module
inline m = go m []
  where go :: MonadFD4 m => Module -> [Decl TTerm] -> m Module
        go [] _ = return []
        go (dec:decs) inlineCandidates = do
            body' <- inlineTerm inlineCandidates (declBody dec)
            let dec' = dec {declBody = body'}
                inlineCandidates' = if countNodes body' < 15
                                    then dec' : inlineCandidates
                                    else inlineCandidates
            decs' <- go decs inlineCandidates'
            return $ dec' : decs'

inlineTerm :: MonadFD4 m => Module -> TTerm -> m TTerm 
inlineTerm [] t = return t

inlineTerm decs t@(App _ (V _ (Global n)) t1@(Const ty (CNat m))) = do
    case find (\d -> declName d == n) decs of
        Just (Decl _ _ _ _ (Lam _ _ _ ct)) -> inlineTerm decs (subst t1 ct)
        Just (Decl _ _ _ _ (Fix {})) -> return t
        Nothing -> return t
        _ -> failFD4 "Error haciendo inline expansion."

inlineTerm decs t@(App i (V p (Global n)) t1) = do
    case find (\d -> declName d == n) decs of
        Just (Decl _ _ _ _ (Lam _ x _ sc)) -> do
            t1' <- inlineTerm decs t1
            return $ Let i x (getTy t1) t1' sc
        Just (Decl _ _ _ _ (Fix {})) -> do
            t1' <- inlineTerm decs t1
            return $ App i (V p (Global n)) t1'
        Nothing -> return t
        _ -> failFD4 "Error haciendo inline expansion."

inlineTerm decs t@(V _ (Global n)) =
    case find (\d -> declName d == n) decs of
        Just (Decl _ _ _ _ t') -> return t'
        Nothing -> return t

inlineTerm decs t = applyRec t (inlineTerm decs)