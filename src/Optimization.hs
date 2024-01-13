{-# OPTIONS_GHC -Wno-unrecognised-pragmas #-}
{-# HLINT ignore "Redundant return" #-}
module Optimization where

import MonadFD4
import Lang
import Subst
import Data.List (find)

optimization :: MonadFD4 m => Int -> Module ->  m ()
optimization 0 d = return ()
optimization n d = go d (analizeModule d) n
  where
    go :: MonadFD4 m => Module -> [Int] -> Int -> m ()
    go decl len 0 = updateGlbDecls decl
    go decl len i = do d' <- moduleOptimization decl len
                       go d' len (i-1)

analizeModule :: Module -> [Int]
analizeModule = map (analizeTerm . declBody)

analizeTerm :: TTerm -> Int
analizeTerm (V i (Global n)) = 1
analizeTerm (V _ _) = 1
analizeTerm (Const _ _) = 1
analizeTerm (Lam _ _ _ (Sc1 t)) = analizeTerm t + 1

analizeTerm (App i t1 t2) =
    analizeTerm t1 + analizeTerm t2 + 1

analizeTerm (Print i s t) =
    analizeTerm t + 1

analizeTerm (BinaryOp i op t1 t2) =
    analizeTerm t1 + analizeTerm t2 + 1

analizeTerm (Fix i f fty x xty (Sc2 t)) =
    analizeTerm t + 1

analizeTerm (IfZ i t1 t2 t3) =
    analizeTerm t1 + analizeTerm t2 + analizeTerm t3 + 1

analizeTerm (Let i x xty def (Sc1 body)) =
    analizeTerm def + analizeTerm body + 1

moduleOptimization :: MonadFD4 m => Module -> [Int] -> m Module
moduleOptimization ts lens = do
    decls1 <- inline ts lens
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
applyRec t@(Const _ _) f = return t
applyRec t@(V _ _) f = return t
applyRec (Lam i n ty (Sc1 t)) f = do
    t' <- f t
    return (Lam i n ty (Sc1 t'))

applyRec (App i t1 t2) f = do
    t1' <- f t1
    t2' <- f t2
    return (App i t1' t2')

applyRec (Print i s t) f= do
    t' <- f t
    return (Print i s t')

applyRec (Fix i n nty m mty (Sc2 t)) f= do
    t' <- f t
    return (Fix i n nty m mty (Sc2 t'))

applyRec (BinaryOp i op t1 t2) f = do
    t1' <- f t1
    t2' <- f t2
    return (BinaryOp i op t1' t2')

applyRec (IfZ i t1 t2 t3) f = do
    t1' <- f t1
    t2' <- f t2
    t3' <- f t3
    return (IfZ i t1' t2' t3')

applyRec (Let i n ty t1 (Sc1 t2)) f = do
    t1' <- f t1
    t2' <- f t2
    return (Let i n ty t1' (Sc1 t2'))

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
    let occursLater = any (globalVarSearch n . declBody) ts
    if occursLater || hasPrint tt
        then do ts' <- deadCodeElim ts
                return $ t : ts'
        else deadCodeElim ts

inline :: MonadFD4 m => Module -> [Int] -> m Module
inline m = go m []
  where go :: MonadFD4 m => Module -> Module -> [Int] -> m Module
        go [] _ _ = return []
        go ((Decl p r name ty body) : ds) shrtDecls (l:ls) = do
            body' <- inlineTerm shrtDecls body
            let dec = Decl p r name ty body'
            let isshort = l < 20
            let shrtDecls' = if l < 20 then dec:shrtDecls else shrtDecls
            ds' <- go ds shrtDecls' ls
            return $ dec : ds'
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