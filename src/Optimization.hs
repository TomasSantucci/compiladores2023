{-# OPTIONS_GHC -Wno-unrecognised-pragmas #-}
{-# HLINT ignore "Redundant return" #-}
module Optimization where

import MonadFD4
import Lang
import Subst
import Data.List (find)
import Control.Monad.Writer

optimization :: MonadFD4 m => Int -> Module ->  m ()
optimization 0 d = return ()
optimization n d = go d (analizeModule d) n
  where
    go :: MonadFD4 m => Module -> ([Int],[Name]) -> Int -> m ()
    go decl info 0 = updateGlbDecls decl
    go decl info i = do d' <- uncurry (moduleOptimization decl) info
                        go d' info (i-1)

analizeModule :: Module -> ([Int],[Name])
analizeModule m = runWriter $ mapM (countNodes . declBody) m

countNodes :: TTerm -> Writer [Name] Int
countNodes (V _ (Global n)) = do
  tell [n]
  return 1

countNodes (V _ _) = return 1

countNodes (Const _ _) = return 1

countNodes (Lam _ _ _ (Sc1 t)) = do
  nodes <- countNodes t
  return (nodes + 1)

countNodes (App _ t1 t2) = do
  nodes1 <- countNodes t1
  nodes2 <- countNodes t2
  return (nodes1 + nodes2 + 1)

countNodes (Print _ _ t) = do
  nodes <- countNodes t
  return (nodes + 1)

countNodes (BinaryOp _ _ t1 t2) = do
  nodes1 <- countNodes t1
  nodes2 <- countNodes t2
  return (nodes1 + nodes2 + 1)

countNodes (Fix _ _ _ _ _ (Sc2 t)) = do
  nodes <- countNodes t
  return (nodes + 1)

countNodes (IfZ _ t1 t2 t3) = do
  nodes1 <- countNodes t1
  nodes2 <- countNodes t2
  nodes3 <- countNodes t3
  return (nodes1 + nodes2 + nodes3 + 1)

countNodes (Let _ x _ def (Sc1 body)) = do
  nodesDef <- countNodes def
  nodesBody <- countNodes body
  return (nodesDef + nodesBody + 1)

moduleOptimization :: MonadFD4 m => Module -> [Int] -> [Name] -> m Module
moduleOptimization ts depths glbs = do
    decls1 <- inline ts depths glbs
    decls2 <- deadCodeElim decls1
    decls3 <- mapM constFoldingProp decls2
    return decls3

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

propagation::MonadFD4 m => TTerm -> m TTerm
propagation (Let i n ty t1 (Sc1 t2)) = do
    t1' <- propagation t1
    t2' <- propagation t2
    case t1' of
        (Const _ (CNat m)) -> return (subst t1' (Sc1 t2'))
        _ -> return (Let i n ty t1' (Sc1 t2'))
propagation t = applyRec t propagation

applyRec :: MonadFD4 m => TTerm -> (TTerm -> m TTerm) -> m TTerm
applyRec t f = case t of
    Const{} -> return t
    V{} -> return t
    Lam i n ty (Sc1 t') -> Lam i n ty . Sc1 <$> f t'
    App i t1 t2 -> App i <$> f t1 <*> f t2
    Print i s t' -> Print i s <$> f t'
    Fix i n nty m mty (Sc2 t') -> Fix i n nty m mty . Sc2 <$> f t'
    BinaryOp i op t1 t2 -> BinaryOp i op <$> f t1 <*> f t2
    IfZ i t1 t2 t3 -> IfZ i <$> f t1 <*> f t2 <*> f t3
    Let i n ty t1 (Sc1 t2) -> Let i n ty <$> f t1 <*> (Sc1 <$> f t2)

hasPrint :: TTerm -> Bool
hasPrint (Print {}) = True
hasPrint (BinaryOp _ _ t1 t2) = hasPrint t1 || hasPrint t2
hasPrint (IfZ _ c t e) = hasPrint c || hasPrint t || hasPrint e
hasPrint (Let _ _ _ def (Sc1 body)) = hasPrint def || hasPrint body
hasPrint (App _ t1 t2) = hasPrint t1 || hasPrint t2
hasPrint _ = False

deadCodeElim :: MonadFD4 m => Module -> m Module
deadCodeElim [] = return []
deadCodeElim [t] = return [t]
deadCodeElim (t@(Decl _ _ n _ tt):ts) = do
    ts' <- deadCodeElim ts
    let occursLater = any (globalVarSearch n . declBody) ts
    if occursLater || hasPrint tt
      then return (t:ts')
      else return ts'

checkHeuristic :: Int -> Name -> [Name] -> Bool
checkHeuristic depth name glbs =
    depth < 15 || length (filter (name==) glbs) == 1

inline :: MonadFD4 m => Module -> [Int] -> [Name] -> m Module
inline m depths glbs = go m [] depths
  where go :: MonadFD4 m => Module -> Module -> [Int] -> m Module
        go [] _ _ = return []
        go ((Decl p r name ty body):decs) inlineCandidates (d:ds) = do
            body' <- inlineTerm inlineCandidates body
            let dec = Decl p r name ty body'
                inlineCandidates' = if checkHeuristic d name glbs
                                    then dec : inlineCandidates
                                    else inlineCandidates
            decs' <- go decs inlineCandidates' ds
            return $ dec : decs'
        go _ _ _ = failFD4 "Error de inline."

inlineTerm :: MonadFD4 m => Module -> TTerm -> m TTerm -- TODO: acomodar info en terminos
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
            let tzTy = (snd . getInfo) t1
            t1' <- inlineTerm decs t1
            return $ Let i x tzTy t1' sc
        Just (Decl _ _ _ _ (Fix {})) -> do
            t1' <- inlineTerm decs t1
            return $ App i (V p (Global n)) t1'
        Nothing -> return t
        _ -> failFD4 "Error haciendo inline expansion."

inlineTerm decs t@(V _ (Global n)) =
    case find (\d -> declName d == n) decs of
        Just (Decl _ _ _ _ t') -> return t'
        Nothing -> return t

inlineTerm decs t = applyRec t (inlineTerm decs) --TODO chequar terminos abiertos