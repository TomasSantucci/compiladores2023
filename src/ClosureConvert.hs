module ClosureConvert where

import IR
import Data.List
import Lang
import Control.Monad.State
import Control.Monad.Writer
import Subst

changeFreeVars :: [Name] -> Ir -> Ir
changeFreeVars fvs (IrVar n) =
    case elemIndex n fvs of
        Just i -> IrAccess (IrVar n) IrInt i
        Nothing -> IrVar n
changeFreeVars fvs (IrCall t ts rty) =
    IrCall (changeFreeVars fvs t) (map (changeFreeVars fvs) ts) rty

changeFreeVars fvs (IrConst c) = IrConst c
changeFreeVars fvs (IrPrint str t) =
    IrPrint str (changeFreeVars fvs t)

changeFreeVars fvs (IrBinaryOp b t1 t2) =
    IrBinaryOp b (changeFreeVars fvs t1) (changeFreeVars fvs t2)

changeFreeVars fvs (IrLet n ty t1 t2) =
    IrLet n ty (changeFreeVars fvs t1) (changeFreeVars fvs t2)

changeFreeVars fvs (IrIfZ c t e) =
    IrIfZ (changeFreeVars fvs c) (changeFreeVars fvs t) (changeFreeVars fvs e)

changeFreeVars fvs (MkClosure n ts) =
    MkClosure n (map (changeFreeVars fvs) ts)

changeFreeVars fvs (IrAccess t ty i) =
    IrAccess (changeFreeVars fvs t) ty i

changeFreeVars _ (IrGlobal n) = IrGlobal n

ty2irty :: Ty -> IrTy
ty2irty (NatTy _) = IrInt
ty2irty (FunTy ty1 ty2 _) = IrClo

freshName :: StateT (Int,Name) (Writer [IrDecl]) Name
freshName = do
    (i,nm) <- get
    modify (\(i',nm') -> (i' + 1, nm'))
    return $ nm ++ show i

letConvert :: Bool -> Name -> Ir -> [(Name,Ty)] -> Ir
letConvert b = letConvert' b 1

letConvert' :: Bool -> Int -> Name -> Ir -> [(Name,Ty)] -> Ir
letConvert' _ _ _ t [] = t
letConvert' False i fn t ((nm,ty):r) =
    let trec = letConvert' False (i+1) fn t r
    in IrLet nm (ty2irty ty) (IrAccess (IrVar fn) (ty2irty ty) i) trec

letConvert' True i fn t ((clonm,ty):r) =
    let trec = letConvert' False i fn t r
    in IrLet fn (ty2irty ty) (IrVar clonm) trec


closureConvert :: TTerm -> StateT (Int,Name) (Writer [IrDecl]) Ir
closureConvert (V _ (Free n)) = do
    return (IrVar n)
closureConvert (V _ (Global n)) = do
    return (IrVar n)
closureConvert (Const i c) =
    return (IrConst c)
closureConvert (Lam _ x xty c@(Sc1 t)) = do
    cloName <- freshName -- puede ser siempre un nombre constante? p.e. "clo"
    auxFunName <- freshName
    let to = open x c
    let fv = freeVars t
    let irfv = map (IrVar . fst) fv
    t' <- closureConvert to
    let body = letConvert False cloName t' fv
    tell [IrFun auxFunName ((ty2irty . getTy) t) [(cloName,IrClo),(x,ty2irty xty)] body]
    return (MkClosure auxFunName irfv)

closureConvert (App i t1 t2) = do
    let (FunTy ty1 ty2 _) = getTy t1
    t1' <- closureConvert t1
    t2' <- closureConvert t2
    return (IrCall (IrAccess t1' IrFunTy 0) [t1',t2'] (ty2irty ty2))

closureConvert (Print _ str t) = do
    t' <- closureConvert t
    return (IrPrint str t')

closureConvert (BinaryOp _ op t1 t2) = do
    t1' <- closureConvert t1
    t2' <- closureConvert t2
    return (IrBinaryOp op t1' t2')

closureConvert (Fix (_,ty) f fty x xty c@(Sc2 t)) = do
    cloName <- freshName
    auxFunName <- freshName
    let to = open2 f x c
    let fv = freeVars t
    let irfv = map (IrVar . fst) fv
    t' <- closureConvert to
    let cfix = MkClosure auxFunName irfv
    let body = letConvert True f t' ((cloName,ty):fv)
    tell [IrFun auxFunName ((ty2irty . getTy) t) [(cloName,IrClo),(x,ty2irty xty)] body]
    return cfix

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
runCC ((Decl _ n ty t):rs) =
    let ((irt,_),sideeff) = runWriter $ runStateT (closureConvert t) (0,"_" ++ n)
        rs' = runCC rs
        ird = IrVal n (ty2irty ty) irt
    in sideeff ++ (ird:rs')
runCC [] = []