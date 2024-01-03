{-# OPTIONS_GHC -Wno-unrecognised-pragmas #-}
{-# HLINT ignore "Use record patterns" #-}
{-|
Module      : PPrint
Description : Pretty printer para FD4.
Copyright   : (c) Mauro Jaskelioff, Guido Martínez, 2020.
License     : GPL-3
Maintainer  : mauro@fceia.unr.edu.ar
Stability   : experimental

-}

module PPrint (
    pp,
    ppTy,
    ppName,
    ppDecl
    ) where

import Lang
import Subst ( open, open2, freshen )
import Common ( Pos )

import Data.Text ( unpack )
import Prettyprinter.Render.Terminal
  ( renderStrict, italicized, color, colorDull, Color (..), AnsiStyle )
import Prettyprinter
    ( (<+>),
      annotate,
      defaultLayoutOptions,
      layoutSmart,
      nest,
      sep,
      parens,
      Doc,
      Pretty(pretty), emptyDoc )
import MonadFD4 ( gets, MonadFD4, failPosFD4 )
import Global ( GlEnv(glb) )

resugarTy :: Ty -> STy
resugarTy (NatTy Nothing) = SNatTy
resugarTy (NatTy (Just n)) = SSyn n
resugarTy (FunTy t1 t2 (Just n)) = SSyn n
resugarTy (FunTy t1 t2 Nothing) = SFunTy (resugarTy t1) (resugarTy t2)


resugar :: STm (Pos,Maybe Int) STy Name -> STerm
-- Casos base
resugar (SV (p, _) var) = SV p var
resugar (SConst (p, _) c) = SConst p c
resugar (SLam (p, Nothing) bs t) = SLam p bs (resugar t)
resugar (SApp (p, _) t1 t2) = SApp p (resugar t1) (resugar t2)
resugar (SPrint (p, _) str t) = SPrint p str (resugar t)
resugar (SPrintFun (p, _) str) = SPrintFun p str
resugar (SBinaryOp (p, _) op t1 t2) = SBinaryOp p op (resugar t1) (resugar t2)
resugar (SFix (p, Nothing) (v, vty) bs t) = SFix p (v, vty) bs (resugar t)
resugar (SIfZ (p, _) t1 t2 t3) = SIfZ p (resugar t1) (resugar t2) (resugar t3)
resugar (SLet _ _ (p, Nothing) (v, vty) bs def body) =
  SLet True False p (v, vty) bs (resugar def) (resugar body)

-- Casos de aplicación de reglas
resugar (SLet _ _ (p, Just 0) (x, xty) [] def body) =
  SLet False False p (x, xty) [] (resugar def) (resugar body)

resugar (SLet _ _ (p, Just 1) (f, fty) [] (SLam _ [(x, xty)] t) body) =
  SLet True False p (f, getReturnSTy fty 1) [(x, xty)] (resugar t) (resugar body)

resugar (SLam (p, Just 2) [(x, xty)] t) =
  let SLam _ bs t' = resugar t
  in SLam p ((x, xty) : bs) t'

resugar (SFix (p, Just 3) (f, fty) [(x, xty)] t) =
  let SLam _ bs t' = resugar t
  in SFix p (f, fty) ((x, xty) : bs) t'

resugar (SLet _ _ (p, Just 4) (f, fty) [] def body) =
  let SLam _ bs t' = resugar def
  in SLet True False p (f, getReturnSTy fty (length bs)) bs t' (resugar body)

resugar (SLet _ _ (p, Just 5) (f, fty) [] def body) =
  let SFix _ _ [(x, xty)] def' = resugar def
  in SLet True True p (f, getReturnSTy fty 1) [(x, xty)] def' (resugar body)

resugar (SLet _ _ (p, Just 6) (f, fty) [] def body) =
  let SFix _ _ bs (SLam _ bs' def') = resugar def
  in SLet True True p (f, getReturnSTy fty (length bs + 1)) (bs ++ bs') def' (resugar body)

resugar _ = undefined


-- Retorna el tipo obtenido al aplicar sus primeros n argumentos
getReturnSTy :: STy -> Int -> STy
getReturnSTy sty 0 = sty
getReturnSTy (SFunTy sty1 sty2) n = getReturnSTy sty2 (n-1)
getReturnSTy sty _ = sty

-- | 'openAll' convierte términos locally nameless
-- a términos fully named abriendo todos las variables de ligadura que va encontrando
-- Debe tener cuidado de no abrir términos con nombres que ya fueron abiertos.
-- Estos nombres se encuentran en la lista ns (primer argumento).
openAll :: (i -> p) -> [Name] -> Tm i Var -> STm p STy Name
openAll gp ns (V p v) = case v of 
      Bound i ->  SV (gp p) $ "(Bound "++show i++")" --este caso no debería aparecer
                                               --si el término es localmente cerrado
      Free x -> SV (gp p) x
      Global x -> SV (gp p) x
openAll gp ns (Const p c) = SConst (gp p) c
openAll gp ns (Lam p x ty t) = 
  let x' = freshen ns x 
  in SLam (gp p) [(x',resugarTy ty)] (openAll gp (x':ns) (open x' t))
openAll gp ns (App p t u) = SApp (gp p) (openAll gp ns t) (openAll gp ns u)
openAll gp ns (Fix p f fty x xty t) = 
  let 
    x' = freshen ns x
    f' = freshen (x':ns) f
  in SFix (gp p) (f',resugarTy fty) [(x',resugarTy xty)] (openAll gp (x:f:ns) (open2 f' x' t))
openAll gp ns (IfZ p c t e) = SIfZ (gp p) (openAll gp ns c) (openAll gp ns t) (openAll gp ns e)
openAll gp ns (Print p str t) = SPrint (gp p) str (openAll gp ns t)
openAll gp ns (BinaryOp p op t u) = SBinaryOp (gp p) op (openAll gp ns t) (openAll gp ns u)
openAll gp ns (Let p v ty m n) = 
    let v'= freshen ns v 
    in  SLet True False (gp p) (v',resugarTy ty) [] (openAll gp ns m) (openAll gp (v':ns) (open v' n))

--Colores
constColor :: Doc AnsiStyle -> Doc AnsiStyle
constColor = annotate (color Red)
opColor :: Doc AnsiStyle -> Doc AnsiStyle
opColor = annotate (colorDull Green)
keywordColor :: Doc AnsiStyle -> Doc AnsiStyle
keywordColor = annotate (colorDull Green) -- <> bold)
typeColor :: Doc AnsiStyle -> Doc AnsiStyle
typeColor = annotate (color Blue <> italicized)
typeOpColor :: Doc AnsiStyle -> Doc AnsiStyle
typeOpColor = annotate (colorDull Blue)
defColor :: Doc AnsiStyle -> Doc AnsiStyle
defColor = annotate (colorDull Magenta <> italicized)
nameColor :: Doc AnsiStyle -> Doc AnsiStyle
nameColor = id

-- | Pretty printer de nombres (Doc)
name2doc :: Name -> Doc AnsiStyle
name2doc n = nameColor (pretty n)

-- |  Pretty printer de nombres (String)
ppName :: Name -> String
ppName = id

ppTypeSyn :: (Maybe Name) -> Doc AnsiStyle -> Doc AnsiStyle
ppTypeSyn Nothing doc = doc
ppTypeSyn (Just n) _ = typeColor $ pretty n

-- | Pretty printer para tipos (Doc)
ty2doc :: Ty -> Doc AnsiStyle
ty2doc (NatTy n) = ppTypeSyn n (typeColor (pretty "Nat"))

ty2doc (FunTy x@(FunTy _ _ Nothing) y n) =
  ppTypeSyn n (sep [parens (ty2doc x), typeOpColor (pretty "->"),ty2doc y])

ty2doc (FunTy x@(FunTy _ _ (Just n1)) y n2) =
  ppTypeSyn n2 (sep [parens (typeColor (pretty n1)), typeOpColor (pretty "->"),ty2doc y])

ty2doc (FunTy x y n) =
  ppTypeSyn n (sep [ty2doc x, typeOpColor (pretty "->"),ty2doc y]) 

sty2doc :: STy -> Doc AnsiStyle
sty2doc SNatTy = typeColor (pretty "Nat")
sty2doc (SFunTy x@(SFunTy _ _) y) =
  sep [parens (sty2doc x), typeOpColor (pretty "->"),sty2doc y]
sty2doc (SFunTy x y) =
  sep [sty2doc x, typeOpColor (pretty "->"),sty2doc y]
sty2doc (SSyn n) = typeColor $ pretty n 

-- | Pretty printer para tipos (String)
ppTy :: Ty -> String
ppTy = render . ty2doc

c2doc :: Const -> Doc AnsiStyle
c2doc (CNat n) = constColor (pretty (show n))

binary2doc :: BinaryOp -> Doc AnsiStyle
binary2doc Add = opColor (pretty "+")
binary2doc Sub = opColor (pretty "-")

collectApp :: STerm -> (STerm, [STerm])
collectApp = go [] where
  go ts (SApp _ h tt) = go (tt:ts) h
  go ts h = (h, ts)

parenIf :: Bool -> Doc a -> Doc a
parenIf True = parens
parenIf _ = id

-- t2doc at t :: Doc
-- at: debe ser un átomo
-- | Pretty printing de términos (Doc)
t2doc :: Bool     -- Debe ser un átomo? 
      -> STerm    -- término a mostrar
      -> Doc AnsiStyle
-- Uncomment to use the Show instance for STerm
{- t2doc at x = text (show x) -}
t2doc at (SV _ x) = name2doc x
t2doc at (SConst _ c) = c2doc c
t2doc at (SLam _ bs t) =
  parenIf at $
  sep [sep [ keywordColor (pretty "fun")
           , sbindings2doc bs
           , opColor(pretty "->")]
      , nest 2 (t2doc False t)]

t2doc at t@(SApp _ _ _) =
  let (h, ts) = collectApp t in
  parenIf at $
  t2doc True h <+> sep (map (t2doc True) ts)

t2doc at (SFix _ (f,fty) bs m) =
  parenIf at $
  sep [ sep [keywordColor (pretty "fix")
                  , sbinding2doc True (f, fty)
                  , sbindings2doc bs
                  , opColor (pretty "->") ]
      , nest 2 (t2doc False m)
      ]
t2doc at (SIfZ _ c t e) =
  parenIf at $
  sep [keywordColor (pretty "ifz"), nest 2 (t2doc False c)
     , keywordColor (pretty "then"), nest 2 (t2doc False t)
     , keywordColor (pretty "else"), nest 2 (t2doc False e) ]

t2doc at (SPrint _ str t) =
  parenIf at $
  sep [keywordColor (pretty "print"), pretty (show str), t2doc True t]

t2doc at (SPrintFun _ str) =
  parenIf at $
  sep [keywordColor (pretty "print"), pretty (show str)]

t2doc at (SLet hasparens _ _ (v,ty) [] t t') =
  parenIf at $
  sep [
    sep [keywordColor (pretty "let")
       , sbinding2doc hasparens (v,ty)
       , opColor (pretty "=") ]
  , nest 2 (t2doc False t)
  , keywordColor (pretty "in")
  , nest 2 (t2doc False t') ]

t2doc at (SLet hasparens isrec _ (v,ty) bs t t') =
  parenIf at $
  sep [
    sep [letop
       , name2doc v
       , sbindings2doc bs
       , pretty ":"
       , sty2doc ty
       , opColor (pretty "=") ]
  , nest 2 (t2doc False t)
  , keywordColor (pretty "in")
  , nest 2 (t2doc False t') ]
  where letop = if isrec then keywordColor (pretty "let rec")
                         else keywordColor (pretty "let")

t2doc at (SBinaryOp _ o a b) =
  parenIf at $
  t2doc True a <+> binary2doc o <+> t2doc True b

binding2doc :: Bool -> (Name, Ty) -> Doc AnsiStyle
binding2doc at (x, ty) =
  parenIf at (sep [name2doc x, pretty ":", ty2doc ty])

sbinding2doc :: Bool -> (Name, STy) -> Doc AnsiStyle
sbinding2doc at (x, ty) =
  parenIf at (sep [name2doc x, pretty ":", sty2doc ty])

sbindings2doc :: [(Name, STy)] -> Doc AnsiStyle
sbindings2doc [] = emptyDoc
sbindings2doc ((x, ty):bs) =
  sep [ sbinding2doc True (x,ty), sbindings2doc bs]

-- | Pretty printing de términos (String)
pp :: MonadFD4 m => TTerm -> m String
-- Uncomment to use the Show instance for Term
{- pp = show -}
pp t = do
       gdecl <- gets glb
       return (render . t2doc False $ openAll (pos . fst) (map declName gdecl) t)

render :: Doc AnsiStyle -> String
render = unpack . renderStrict . layoutSmart defaultLayoutOptions

-- SLam info [(var, ty)] (STm info ty var)
resugarDecl :: MonadFD4 m => Decl TTerm -> [Name] -> m SDecl
resugarDecl (Decl p (Just 0) f fty t) names = do
  let SLam _ [(x,xty)] body = resugar $ openAll (extractInfo . fst) names t
  return $ SDecl p f
           (getReturnSTy (resugarTy fty) 1)
           [(x,xty)] False
           body

resugarDecl (Decl p (Just 1) f fty t) names = do
  let SLam _ bs body = resugar $ openAll (extractInfo . fst) names t
  return $ SDecl p f
           (getReturnSTy (resugarTy fty) (length bs))
           bs False
           body

resugarDecl (Decl p (Just 2) f _ t) names = do
  let SFix _ (_,fty) [(x,xty)] body = resugar $ openAll (extractInfo . fst) names t
  return $ SDecl p f
           (getReturnSTy fty 1)
           [(x,xty)] True
           body

resugarDecl (Decl p (Just 3) f fty t) names = do
  let SFix _ (f',fty') [(x,xty)] (SLam _ bs body) = resugar $ openAll (extractInfo . fst) names t
  return $ SDecl p f
           (getReturnSTy fty' (length bs + 1))
           ((x,xty):bs) True
           body

resugarDecl (Decl p Nothing f fty t) names = do
  let body' = resugar $ openAll (extractInfo . fst) names t
  return $ SDecl p f
           (resugarTy fty)
           [] False
           body'

resugarDecl (Decl p (Just n) f fty t) _ =
  failPosFD4 p ("Regla " ++ show n ++ " no implementada")

-- | Pretty printing de declaraciones
ppDecl :: MonadFD4 m => Decl TTerm -> m String
ppDecl d = do
  gdecl <- gets glb
  sd <- resugarDecl d (map declName gdecl)
  ppSDecl sd

ppSDecl :: MonadFD4 m => SDecl -> m String
ppSDecl (SDecl p v vty [] False body) =
  return (render $ sep [defColor (pretty "let")
                       , sbinding2doc False (v,vty)
                       , defColor (pretty "=")]
                   <+> nest 2 (t2doc False body))

ppSDecl (SDecl p f rty bs isrec body) = do
  let letstr = if isrec then "let rec" else "let"
  return (render $ sep [defColor (pretty letstr)
                       , pretty f
                       , sbindings2doc bs
                       , pretty ":"
                       , sty2doc rty
                       , defColor (pretty "=")]
                   <+> nest 2 (t2doc False body))

ppSDecl (SDefType p _ _) = failPosFD4 p "No es posible imprimir una definición de tipos."