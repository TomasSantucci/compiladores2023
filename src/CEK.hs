module CEK where
  
import Lang
import MonadFD4
import Common
import Data.Maybe (fromJust)

seek :: MonadFD4 m => TTerm -> CEKEnv -> Kont -> m CEKVal

seek (Print _ str t) env k =
  seek t env ((KPrint str) : k)

seek (BinaryOp _ bin t1 t2) env k =
  seek t1 env ((KOpL env bin t2) : k)

seek (IfZ _ c t2 t3) env k =
  seek c env ((KIfz env t2 t3) : k)

seek (App _ t1 t2) env k =
  seek t1 env ((KArg env t2) : k)

seek (V _ (Bound i)) env k =
  destroy (env !! i) k

seek (V _ (Global n)) env k = do
  decl <- lookupDecl n
  case decl of 
    Just t -> do env' <- lookupEnv n
                 seek t (env ++ fromJust env') k
    Nothing -> failFD4 ("Variable global" ++ n ++ "no declarada.")

seek (V _ (Free n)) env k =
  failFD4 ("Error por variable libre.")

seek (Const _ (CNat n)) env k =
  destroy (NumVal n) k

seek (Lam _ x xty (Sc1 t)) env k =
  destroy (ClosV (ClosFun env t x xty)) k

seek (Fix _ f fty x xty (Sc2 t)) env k =
  destroy (ClosV (ClosFix env t f fty x xty)) k

seek (Let _ _ _ def (Sc1 body)) env k =
  seek def env ((KLet env body) : k)


destroy :: MonadFD4 m => CEKVal -> Kont -> m CEKVal

destroy v [] = 
  return v

destroy (NumVal n) ((KPrint str):k) = do
  printFD4 (str ++ (show n))
  destroy (NumVal n) k

destroy (NumVal n) ((KOpL env op u):k) =
  seek u env ((KOpR n op) : k)

destroy (NumVal n) ((KOpR m op):k) =
  destroy (NumVal (semOp op m n)) k

destroy (NumVal 0) ((KIfz env t _):k) =
  seek t env k

destroy (NumVal n) ((KIfz env _ e):k) =
  seek e env k

destroy (ClosV clos) ((KArg env t):k) =
  seek t env ((KFun clos) : k)

destroy v ((KFun (ClosFun env t x xty)):k) =
  seek t (v:env) k

destroy v ((KFun c@(ClosFix env t f fty x xty)):k) =
  seek t (v:(ClosV c):env) k 

destroy v ((KLet env t):k) =
  seek t (v:env) k

destroy v k =
  failFD4 "Error de runtime."

value2Term :: CEKVal -> (TTerm, CEKEnv)
value2Term (NumVal n) =
  (Const (NoPos,NatTy Nothing) (CNat n), [])

value2Term (ClosV (ClosFun env body x xty)) =
  (Lam (NoPos,(FunTy xty (getTy body) Nothing)) x xty (Sc1 body), env)

value2Term (ClosV (ClosFix env body f fty x xty)) =
  (Fix (NoPos,fty) f fty x xty (Sc2 body), env)

evalCEK :: (MonadFD4 m) => TTerm -> m (TTerm, CEKEnv)
evalCEK t = do v <- seek t [] []
               return (value2Term v)