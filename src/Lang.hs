{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE EmptyDataDeriving #-}

{-|
Module      : Lang
Description : AST de términos, declaraciones y tipos
Copyright   : (c) Mauro Jaskelioff, Guido Martínez, 2020.
License     : GPL-3
Maintainer  : mauro@fceia.unr.edu.ar
Stability   : experimental

Definiciones de distintos tipos de datos:
  - AST de términos
  - Declaraciones
  - Tipos
  - Variables

-}

module Lang where

import           Common                         ( Pos(NoPos) )
import           Data.List.Extra                ( nubSortOn )

-- | AST the términos superficiales
data STm info ty var =
    SV info var
  | SConst info Const
  | SLam info [(var, ty)] (STm info ty var)
  | SApp info (STm info ty var) (STm info ty var)
  | SPrint info String (STm info ty var)
  | SPrintFun info String
  | SBinaryOp info BinaryOp (STm info ty var) (STm info ty var)
  | SFix info (var, ty) [(var, ty)] (STm info ty var)
  | SIfZ info (STm info ty var) (STm info ty var) (STm info ty var)
  | SLet HasParens IsRecursive info (var, ty) [(var,ty)] (STm info ty var) (STm info ty var)
  deriving (Show, Functor)

-- | AST de Tipos
data Ty =
      NatTy (Maybe Name)
    | FunTy Ty Ty (Maybe Name)
    deriving Show
  
compareTypes :: Ty -> Ty -> Bool
compareTypes (NatTy _) (NatTy _) = True
compareTypes (FunTy _ _ _) (NatTy _) = False
compareTypes (NatTy _) (FunTy _ _ _) = False
compareTypes (FunTy t1 t2 _) (FunTy t3 t4 _) =
  compareTypes t1 t3 && compareTypes t2 t4

instance Eq Ty where
  t1 == t2 = compareTypes t1 t2

type HasParens = Bool

type IsRecursive = Bool

type Name = String

data STy =
      SNatTy
    | SFunTy STy STy
    | SSyn Name
  deriving (Show,Eq)

type STerm = STm Pos STy Name -- ^ 'STm' tiene 'Name's como variables ligadas y libres y globales, guarda posición  

newtype Const = CNat Int
  deriving Show

data BinaryOp = Add | Sub
  deriving Show

-- | tipo de datos de declaraciones, parametrizado por el tipo del cuerpo de la declaración
data Decl a = Decl
  { declPos  :: Pos
  , declRule :: Maybe Int
  , declName :: Name
  , declType :: Ty
  , declBody :: a
  }
  deriving (Show, Functor)

data SDecl = SDecl 
  { sDeclPos :: Pos
  , sDeclName :: Name
  , sDeclType :: STy
  , sDeclArgs :: [(Name,STy)]
  , sDeclRec  :: Bool
  , sDeclBody :: STerm}
  | SDefType Pos Name STy
 deriving Show

-- | AST de los términos. 
--   - info es información extra que puede llevar cada nodo. 
--       Por ahora solo la usamos para guardar posiciones en el código fuente.
--   - var es el tipo de la variables. Es 'Name' para fully named y 'Var' para locally closed. 
data Tm info var =
    V info var
  | Const info Const
  | Lam info Name Ty (Scope info var)
  | App info (Tm info var) (Tm info var)
  | Print info String (Tm info var)
  | BinaryOp info BinaryOp (Tm info var) (Tm info var)
  | Fix info Name Ty Name Ty (Scope2 info var)
  | IfZ info (Tm info var) (Tm info var) (Tm info var)
  | Let info Name Ty (Tm info var) (Scope info var)
  deriving (Show, Functor)

type Term = Tm TermInfo Var       -- ^ 'Tm' con índices de De Bruijn como variables ligadas, y nombres para libres y globales, guarda posición y regla de desugar
type TTerm = Tm (TermInfo,Ty) Var -- ^ 'Tm' con índices de De Bruijn como variables ligadas, y nombres para libres y globales, guarda posición, tipo y regla de desugar

data TermInfo = Info {
  pos :: Pos,
  sug :: Maybe Int
} deriving Show

extractInfo :: TermInfo -> (Pos,Maybe Int)
extractInfo (Info p s) = (p,s)

noInfo :: TermInfo
noInfo = Info NoPos Nothing

type Module = [Decl TTerm]

data Var =
    Bound !Int
  | Free Name
  | Global Name
  deriving Show

-- Scope es un término con una o dos variables que escapan.
newtype Scope info var = Sc1 (Tm info var)
  deriving Functor
newtype Scope2 info var = Sc2 (Tm info var)
  deriving Functor
    
instance (Show info, Show var) => Show (Scope info var) where
    show (Sc1 t) = "{"++show t++"}"

instance (Show info, Show var) => Show (Scope2 info var) where
    show (Sc2 t) = "{{"++show t++"}}"

data CEKVal = 
  NumVal Int |
  ClosV Clos
 
data Clos =
  ClosFun CEKEnv TTerm Name Ty |
  ClosFix CEKEnv TTerm Name Ty Name Ty

data Frame = 
  KArg CEKEnv TTerm |
  KFun Clos |
  KIfz CEKEnv TTerm TTerm |
  KOpL CEKEnv BinaryOp TTerm |
  KOpR Int BinaryOp |
  KPrint String |
  KLet CEKEnv TTerm

type CEKEnv = [CEKVal]

type Kont = [Frame]

-- | Semántica de operadores binarios
semOp :: BinaryOp -> Int -> Int -> Int
semOp Add x y=  x + y
semOp Sub x y = max 0 (x - y)

-- | Obtiene la info en la raíz del término.
getInfo :: Tm info var -> info
getInfo (V     i _       ) = i
getInfo (Const i _       ) = i
getInfo (Lam i _ _ _     ) = i
getInfo (App   i _ _     ) = i
getInfo (Print i _ _     ) = i
getInfo (Fix i _ _ _ _ _ ) = i
getInfo (IfZ i _ _ _     ) = i
getInfo (Let i _ _ _ _   ) = i
getInfo (BinaryOp i _ _ _) = i

getTy :: TTerm -> Ty
getTy = snd . getInfo

getPos :: TTerm -> Pos
getPos = pos . fst . getInfo

-- | map para la info de un término
mapInfo :: (a -> b) -> Tm a var -> Tm b var
mapInfo f (V i x) = V (f i) x
mapInfo f (Const i x) = Const (f i) x
mapInfo f (Lam i x ty (Sc1 y)) = Lam (f i) x ty (Sc1 $ mapInfo f y)
mapInfo f (App i x y ) = App (f i) (mapInfo f x) (mapInfo f y)
mapInfo f (Print i msg y) = Print (f i) msg (mapInfo f y)
mapInfo f (BinaryOp i x y z ) = BinaryOp (f i) x (mapInfo f y) (mapInfo f z)
mapInfo f (Fix i x xty y yty (Sc2 z)) = Fix (f i) x xty y yty (Sc2 $ mapInfo f z)
mapInfo f (IfZ i x y z) = IfZ (f i) (mapInfo f x) (mapInfo f y) (mapInfo f z)
mapInfo f (Let i x xty y (Sc1 z)) = Let (f i) x xty (mapInfo f y) (Sc1 $ mapInfo f z)

-- | Obtiene los nombres de variables (abiertas o globales) de un término.
freeVars :: TTerm -> [(Name,Ty)]
freeVars tm = nubSortOn fst $ go tm [] where
  go (V (_,ty) (Free v)       ) xs = (v,ty) : xs
  go (V _ (Global v)          ) xs = xs
  go (V _ _                   ) xs = xs
  go (Lam _ _ _ (Sc1 t)       ) xs = go t xs
  go (App   _ l r             ) xs = go l $ go r xs
  go (Print _ _ t             ) xs = go t xs
  go (BinaryOp _ _ t u        ) xs = go t $ go u xs
  go (Fix _ _ _ _ _ (Sc2 t)   ) xs = go t xs
  go (IfZ _ c t e             ) xs = go c $ go t $ go e xs
  go (Const _ _               ) xs = xs
  go (Let _ _ _ e (Sc1 t)     ) xs = go e (go t xs)


globalVarSearch :: Name -> TTerm -> Bool
globalVarSearch  n (V _ (Global str)) = str == n
globalVarSearch  _ (V _ _) = False
globalVarSearch  _ (Const _ _) = False
globalVarSearch  n (Lam _ _ ty (Sc1 t)) = globalVarSearch n t
globalVarSearch  n (App _ t1 t2) =globalVarSearch n t1 || globalVarSearch n t2
globalVarSearch  n (Print _ _ t) = globalVarSearch n t
globalVarSearch  n (BinaryOp _ _ t1 t2) = globalVarSearch n t1 || globalVarSearch n t2
globalVarSearch  n (Fix _ _ _ _ _ (Sc2 t)) = globalVarSearch n t
globalVarSearch  n (IfZ _ t1 t2 t3) = globalVarSearch n t1 || globalVarSearch n t2 || globalVarSearch n t3
globalVarSearch  n (Let _ _ _ t1 (Sc1 t2)) =globalVarSearch n t1 || globalVarSearch n t2 