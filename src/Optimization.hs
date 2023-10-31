{-# OPTIONS_GHC -Wno-unrecognised-pragmas #-}
{-# HLINT ignore "Redundant return" #-}
module Optimization where

import MonadFD4
import Lang
import Subst

optimization :: MonadFD4 m => Int -> [Decl TTerm] ->  m ()
optimization 0 d = do
    updateGlbDecls d
optimization n d = do
    d' <- moduleOptimization d
    optimization (n-1) d'

moduleOptimization :: MonadFD4 m => [Decl TTerm] -> m [Decl TTerm]
moduleOptimization ts = do
    decls1 <- inline ts
    decls2 <- deadCodeElim decls1
    decls3 <- mapM constFoldingProp decls2
    return decls3

constFoldingProp :: MonadFD4 m => Decl TTerm -> m (Decl TTerm)
constFoldingProp (Decl p s ty t) = do
    t1 <- propagation t
    t2 <- constFolding t1
    return (Decl p s ty t2)

constFolding :: MonadFD4 m => TTerm -> m TTerm
constFolding (BinaryOp i op t1 t2) = do
    t1' <- constFolding t1
    t2' <- constFolding t2
    case (t1' ,t2', op) of
        (_,(Const _ (CNat 0)),_) -> return t1'
        ((Const _ (CNat 0)),_,Add) -> return t2'
        ((Const _ (CNat 0)),_,Sub) -> return t1'
        ((Const _ (CNat n)),(Const _ (CNat m) ),_ ) -> return (Const i (CNat (semOp op n m)))
        _ -> return (BinaryOp i op t1' t2')
constFolding (IfZ i t1 t2 t3) = do
    t1' <- constFolding t1
    t2' <- constFolding t2
    t3' <- constFolding t3
    case t1' of
        (Const _ (CNat 0)) -> return t2' --posible caso de que t2 y t3 sean el mismo ??
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
applyRec (Lam i n ty (Sc1 t)) f= do
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
    t' <-f t
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

hasPrint :: TTerm -> Bool -- como hago con App?
hasPrint (Print _ _ _) = True
hasPrint (BinaryOp _ _ t1 t2) = hasPrint t1 || hasPrint t2
hasPrint (IfZ _ c t e) = hasPrint c || hasPrint t || hasPrint e
hasPrint (Let _ _ _ def (Sc1 body)) = hasPrint def || hasPrint body
hasPrint _ = False

hasSideEffects :: TTerm -> Bool
hasSideEffects t = hasPrint t

deadCodeElim :: MonadFD4 m => [Decl TTerm] -> m [Decl TTerm]
deadCodeElim [] = return []
deadCodeElim [t] = return [t]
deadCodeElim (t@(Decl _ n _ tt):ts) = do
    let occursLater = any (globalVarSearch n . getBody) ts
    if occursLater || (hasSideEffects tt)
        then do ts' <- deadCodeElim ts
                return $ t : ts'
        else deadCodeElim ts
    where
        getBody (Decl _ _ _ body) = body

inline :: MonadFD4 m => [Decl TTerm] -> m [Decl TTerm]
inline m = inline' m []

inline' :: MonadFD4 m => [Decl TTerm] -> [Decl TTerm] -> m [Decl TTerm]
inline' [] _ = return []
inline' ((Decl p name ty body) : ds) decls = do
    body' <- inlineExpBasic decls body
    let dec = Decl p name ty body'
    ds' <- inline' ds (dec:decls)
    return $ dec : ds'

inlineExpBasic :: MonadFD4 m => [Decl TTerm] -> TTerm -> m TTerm -- TODO: acomodar info en terminos
inlineExpBasic [] t = return t

inlineExpBasic decs t@(App _ (V _ (Global n)) t1@(Const ty (CNat m))) = do
    case filter (\d -> declName d == n) decs of
        [Decl _ _ _ (Lam _ _ _ ct)] -> inlineExpBasic decs (subst t1 ct)
        [Decl _ _ _ (Fix {})] -> return t
        _ -> failFD4 "Error haciendo inline expansion."

inlineExpBasic decs t@(App i (V _ (Global n)) t1) = do
    case filter (\d -> declName d == n) decs of
        [Decl _ _ _ (Lam p x _ sc)] -> do
            let tzTy = getTy t1
            inlineExpBasic decs (Let i x tzTy t1 sc)
        [Decl _ _ _ (Fix {})] -> return t
        _ -> failFD4 "Error haciendo inline expansion."

inlineExpBasic decs t@(V _ (Global n)) =
    case filter (\d -> declName d == n) decs of
        [Decl _ _ _ (Fix {})] -> return t
        [Decl _ _ _ t'] -> return t'
        _ -> failFD4 "Error haciendo inline expansion."

inlineExpBasic decs t = applyRec t (inlineExpBasic decs) ----TODO chequar terminos abiertos