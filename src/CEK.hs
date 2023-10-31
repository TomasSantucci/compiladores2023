module CEK where
  
import Lang
import MonadFD4
import Common
import Subst

seek :: MonadFD4 m => TTerm -> CEKEnv -> Kont -> m CEKVal

seek (Print _ str t) env k = do
  stepCEK
  seek t env ((KPrint str) : k)

seek (BinaryOp _ bin t1 t2) env k = do
  stepCEK
  seek t1 env ((KOpL env bin t2) : k)

seek (IfZ _ c t2 t3) env k = do
  stepCEK
  seek c env ((KIfz env t2 t3) : k)

seek (App _ t1 t2) env k = do
  stepCEK
  seek t1 env ((KArg env t2) : k)

seek (V _ (Bound i)) env k = do
  stepCEK
  destroy (env !! i) k

seek (V _ (Global n)) env k = do
  stepCEK
  decl <- lookupDecl n
  case decl of
    Just t -> seek t [] k
    Nothing -> failFD4 ("Variable global" ++ n ++ "no declarada.")

seek (V _ (Free n)) env k =
  failFD4 ("Error por variable libre.")

seek (Const _ (CNat n)) env k = do
  stepCEK
  destroy (NumVal n) k

seek (Lam _ x xty (Sc1 t)) env k = do
  stepCEK
  destroy (ClosV (ClosFun env t x xty)) k

seek (Fix _ f fty x xty (Sc2 t)) env k = do
  stepCEK
  destroy (ClosV (ClosFix env t f fty x xty)) k

seek (Let _ _ _ def (Sc1 body)) env k = do
  stepCEK
  seek def env ((KLet env body) : k)


destroy :: MonadFD4 m => CEKVal -> Kont -> m CEKVal

destroy v [] = do
  stepCEK
  return v

destroy (NumVal n) ((KPrint str):k) = do
  stepCEK
  printFD4 (str ++ (show n))
  destroy (NumVal n) k

destroy (NumVal n) ((KOpL env op u):k) = do
  stepCEK
  seek u env ((KOpR n op) : k)

destroy (NumVal n) ((KOpR m op):k) = do
  stepCEK
  destroy (NumVal (semOp op m n)) k

destroy (NumVal 0) ((KIfz env t _):k) = do
  stepCEK
  seek t env k

destroy (NumVal n) ((KIfz env _ e):k) = do
  stepCEK
  seek e env k

destroy (ClosV clos) ((KArg env t):k) = do
  stepCEK
  seek t env ((KFun clos) : k)

destroy v ((KFun (ClosFun env t x xty)):k) = do
  stepCEK
  seek t (v:env) k

destroy v ((KFun c@(ClosFix env t f fty x xty)):k) = do
  stepCEK
  seek t (v:(ClosV c):env) k 

destroy v ((KLet env t):k) = do
  stepCEK
  seek t (v:env) k

destroy v k =
  failFD4 "Error de runtime."

substRem :: CEKEnv -> TTerm -> Int -> TTerm
substRem [] body scs = body
substRem env body scs = varChanger (\_ p n -> V p (Free n)) bnd body
   where bnd depth p i 
             | i < depth + scs = V p (Bound i)
             | i <= depth + scs + length env = value2Term (env!!(i-depth-1))
             | otherwise  = V p (Bound i)

value2Term :: CEKVal -> TTerm
value2Term (NumVal n) =
  Const (NoPos,NatTy Nothing) (CNat n)

value2Term (ClosV (ClosFun [] body x xty)) =
  Lam (NoPos,(FunTy xty (getTy body) Nothing)) x xty (Sc1 body)

value2Term (ClosV (ClosFun env body x xty)) =
  let body' = substRem env body 1 in
  Lam (NoPos,(FunTy xty (getTy body) Nothing)) x xty (Sc1 body')

value2Term (ClosV (ClosFix env body f fty x xty)) =
  let body' = substRem env body 2 in
  Fix (NoPos,fty) f fty x xty (Sc2 body')

evalCEK :: (MonadFD4 m) => TTerm -> m TTerm
evalCEK t = do v <- seek t [] []
               return (value2Term v)