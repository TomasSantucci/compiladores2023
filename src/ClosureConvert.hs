module ClosureConvert where

import IR
import Lang
import Control.Monad.State
import Control.Monad.Writer
import Subst

ty2irty :: Ty -> IrTy
ty2irty (NatTy {}) = IrInt
ty2irty (FunTy {}) = IrClo

freshName :: StateT (Int,Name) (Writer [IrDecl]) Name
freshName = do
    (i,nm) <- get
    modify (\(i',nm') -> (i' + 1, nm'))
    return $ nm ++ show i

recoverFV :: Int -> Name -> Ir -> [(Name,Ty)] -> Ir
recoverFV _ _ t [] = t
recoverFV i fn t ((v,vty):bs) =
    let trec = recoverFV (i+1) fn t bs
    in IrLet v (ty2irty vty) (IrAccess (IrVar fn) (ty2irty vty) i) trec

recoverFVRec :: Name -> Ir -> [(Name, Ty)] -> Ir
recoverFVRec fn t [] = t
recoverFVRec fn t ((clonm,ty):bs) =
    let trec = recoverFV 1 fn t bs
    in IrLet fn (ty2irty ty) (IrVar clonm) trec

closureConvert :: TTerm -> StateT (Int,Name) (Writer [IrDecl]) Ir
closureConvert (V _ (Free n)) = do
    return (IrVar n)
closureConvert (V _ (Global n)) = do
    return (IrVar n)
closureConvert (Const i c) =
    return (IrConst c)
closureConvert (Lam _ x xty sc@(Sc1 t)) = do
    cloName <- freshName
    auxFunName <- freshName
    let fv = freeVars t
    let irfv = map (IrVar . fst) fv
    t' <- closureConvert (open x sc)
    let body = recoverFV 1 cloName t' fv
    tell [IrFun auxFunName ((ty2irty . getTy) t) [(cloName,IrClo),(x,ty2irty xty)] body]
    return (MkClosure auxFunName irfv)

closureConvert (App i t1 t2) = do
    let (FunTy ty1 ty2 _) = getTy t1
    cloName <- freshName
    let v = IrVar cloName
    t1' <- closureConvert t1
    t2' <- closureConvert t2
    return $ IrLet cloName IrClo t1' (IrCall (IrAccess v IrFunTy 0) [v,t2'] (ty2irty ty2))

closureConvert (Print _ str t) = do
    var <- freshName
    t' <- closureConvert t
    return $ IrLet var ((ty2irty . getTy) t) t' (IrPrint str (IrVar var))

closureConvert (BinaryOp _ op t1 t2) = do
    t1' <- closureConvert t1
    t2' <- closureConvert t2
    return (IrBinaryOp op t1' t2')

closureConvert (Fix (_,ty) f fty x xty sc@(Sc2 t)) = do
    cloName <- freshName
    auxFunName <- freshName
    let fv = freeVars t
    let irfv = map (IrVar . fst) fv
    t' <- closureConvert (open2 f x sc)
    let body = recoverFVRec f t' ((cloName,ty):fv)
    tell [IrFun auxFunName ((ty2irty . getTy) t) [(cloName,IrClo),(x,ty2irty xty)] body]
    return $ MkClosure auxFunName irfv

closureConvert (IfZ _ t1 t2 t3) = do
    t1' <- closureConvert t1
    t2' <- closureConvert t2
    t3' <- closureConvert t3
    return (IrIfZ t1' t2' t3')

closureConvert (Let _ x xty t1 c@(Sc1 t2)) = do
    t1' <- closureConvert t1
    t2' <- closureConvert (open x c)
    return (IrLet x (ty2irty xty) t1' t2')

closureConvert _ = return (IrVar "")

runCC :: [Decl TTerm] -> [IrDecl]
runCC ((Decl _ _ n ty t):rs) =
    let ((irt,_),sideeff) = runWriter $ runStateT (closureConvert t) (0,"_" ++ n)
        rs' = runCC rs
        ird = IrVal n (ty2irty ty) irt
    in sideeff ++ (ird:rs')
runCC [] = []