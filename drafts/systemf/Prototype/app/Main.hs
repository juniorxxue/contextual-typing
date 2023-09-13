{-# LANGUAGE GADTs #-}
{-# LANGUAGE InstanceSigs #-}

module Main where
import Data.List (nub)
import Debug.Trace

data Type where
    TVar :: String -> Type
    TInt :: Type
    TTop :: Type
    TArr :: Type -> Type -> Type
    TAll :: String -> Type -> Type
    TExt :: String -> Type

instance Eq Type where
    (==) :: Type -> Type -> Bool
    (==) (TVar a) (TVar b) = a == b
    (==) TInt TInt = True
    (==) TTop TTop = True
    (==) (TArr tyA tyB) (TArr tyC tyD) = tyA == tyC && tyB == tyD
    (==) (TAll a tyA) (TAll b tyB) = a == b && tyA == tyB
    (==) (TExt a) (TExt b) = a == b
    (==) _ _ = False

instance Show Type where
    show :: Type -> String
    show (TVar a) = a
    show TInt = "Int"
    show TTop = "Top"
    show (TArr tyA tyB) = "(" ++ show tyA ++ " → " ++ show tyB ++ ")"
    show (TAll a tyA) = "∀" ++ a ++ "." ++ show tyA
    show (TExt a) = "^" ++ a

data Term where
    Lit :: Int -> Term
    Var :: String -> Term
    Lam :: String -> Term -> Term
    App :: Term -> Term -> Term
    Ann :: Term -> Type -> Term
    TLam :: String -> Term -> Term
    TApp :: Term -> Type -> Term

instance Show Term where
    show :: Term -> String
    show (Lit n) = show n
    show (Var x) = x
    show (Lam x e) = "λ" ++ x ++ "." ++ show e
    show (App e1 e2) = "(" ++ show e1 ++ " " ++ show e2 ++ ")"
    show (Ann e ty) = "(" ++ show e ++ " : " ++ show ty ++ ")"
    show (TLam a e) = "Λ" ++ a ++ "." ++ show e
    show (TApp e ty) = "(" ++ show e ++ " [" ++ show ty ++ "])"

data Hint where
    T :: Type -> Hint
    Hole :: Term -> Hint -> Hint

instance Show Hint where
    show :: Hint -> String
    show (T ty) = show ty
    show (Hole e h) = "[" ++ show e ++ "]" ++ " → " ++ show h

data Context where
    Empty :: Context
    TmVar :: String -> Type -> Context -> Context
    TyVar :: String -> Context -> Context
    ExVar :: String -> Context -> Context
    ChVar :: String -> Type -> Context -> Context

instance Show Context where
    show :: Context -> String
    show Empty = "·"
    show (TmVar x tyA ctx) = show ctx ++ ", " ++ x ++ " : " ++ show tyA
    show (TyVar a ctx) = show ctx ++ ", " ++ a
    show (ExVar a ctx) = show ctx ++ ", ^" ++ a
    show (ChVar a tyA ctx) = show ctx ++ ", ^" ++ a ++ " : " ++ show tyA

typeof :: Context -> Hint -> Term -> Maybe Type
typeof ctx (T TTop) (Lit _) = Just TInt
typeof ctx (T TTop) (Var x) = lookupTmVar ctx x
typeof ctx (T TTop) (Ann e tyA) = case typeof ctx (T tyA) e of
    Just tyB -> Just tyA
    Nothing -> Nothing
typeof ctx (T TTop) (TLam a e) = case typeof (TyVar a ctx) (T TTop) e of
    Just tyA -> Just (TAll a tyA)
    Nothing -> Nothing
typeof ctx h (App e1 e2) = case typeof ctx (Hole e2 h) e1 of
    Just (TArr tyA tyB) -> Just tyB
    _ -> Nothing
typeof ctx (T (TArr tyA tyB)) (Lam x e) = case typeof (TmVar x tyA ctx) (T tyB) e of
    Just tyC -> Just (TArr tyA tyC)
    Nothing -> Nothing
typeof ctx (Hole e2 h) (Lam x e) = case typeof ctx (T TTop) e2 of
    Just tyA -> case typeof (TmVar x tyA ctx) h e of
        Just tyB -> Just (TArr tyA tyB)
        Nothing -> Nothing
    Nothing -> Nothing
typeof ctx h (TApp e tyA) = case typeof ctx h e of
    Just (TAll a tyB) -> Just (subst a tyA tyB)
    Nothing -> Nothing
typeof ctx h e | pv e = case typeof ctx (T TTop) e of
    Just tyA -> case refine ctx tyA h of
        Just (ctx', tyB) -> Just tyB
        Nothing -> Nothing

pv :: Term -> Bool
pv (Lit _) = True
pv (Var _) = True
pv (Ann _ _) = True
pv (TLam _ _) = True
pv _ = False

-- subst a type var with a type
-- [a/A]T
subst :: String -> Type -> Type -> Type
subst a (TVar b) newTy | a == b = newTy
subst a (TArr tyA tyB) newTy = TArr (subst a tyA newTy) (subst a tyB newTy)
subst a (TAll b tyA) newTy = TAll b (subst a tyA newTy) -- suppose we never repeat binding names
subst a oldTy newTy = oldTy

freeExVars :: Type -> [String]
freeExVars = nub . freeExVarsWithDups
    where
        freeExVarsWithDups :: Type -> [String]
        freeExVarsWithDups (TVar a) = []
        freeExVarsWithDups TInt = []
        freeExVarsWithDups TTop = []
        freeExVarsWithDups (TArr tyA tyB) = freeExVarsWithDups tyA ++ freeExVarsWithDups tyB
        freeExVarsWithDups (TAll a tyA) =  freeExVarsWithDups tyA
        freeExVarsWithDups (TExt a) = [a]

substEx :: String -> Type -> Context -> Context
substEx a newTy Empty = Empty
substEx a newTy (TmVar x tyA ctx) = TmVar x tyA (substEx a newTy ctx)
substEx a newTy (TyVar x ctx) = TyVar x (substEx a newTy ctx)
substEx a newTy (ExVar b ctx) | a == b = ChVar a newTy (substEx a newTy ctx)
substEx a newTy (ExVar b ctx) | a /= b = ExVar b (substEx a newTy ctx)
substEx a newTy (ChVar b tyA ctx) | a == b = if newTy == tyA then ChVar b tyA ctx else error "context subst inconsistency"

notNull :: [a] -> Bool
notNull = not . null

notTop :: Type -> Bool
notTop TTop = False
notTop _ = True

refine :: Context -> Type -> Hint -> Maybe (Context, Type)
refine ctx TInt (T TInt) = do
    trace ("[S-Int]: " ++ show ctx ++ " ⊢ " ++ show TInt ++ " <: " ++ show TInt) $ return ()
    return (ctx, TInt)
refine ctx (TExt a) (T tyA) | null (freeExVars tyA) = do
    trace ("[S-Ext-L]: " ++ show ctx ++ " ⊢ " ++ show (TExt a) ++ " <: " ++ show (T tyA)) $ return ()
    return (substEx a tyA ctx, tyA)
refine ctx tyA (T (TExt a)) | null (freeExVars tyA) = do
    trace ("[S-Ext-R]: " ++ show ctx ++ " ⊢ " ++ show (T tyA) ++ " <: " ++ show (TExt a)) $ return ()
    return (substEx a tyA ctx, tyA)
refine ctx tyA (T TTop) = do
    trace ("[S-Top]: " ++ show ctx ++ " ⊢ " ++ show (T tyA) ++ " <: " ++ show TTop) $ return ()
    return (ctx, tyA)
refine ctx1 (TArr tyA tyB) (T (TArr tyC tyD)) = do
    trace ("[S-Arr]: " ++ show ctx1 ++ " ⊢ " ++ show (TArr tyA tyB) ++ " <: " ++ show (TArr tyC tyD)) $ return ()
    (ctx2, tyA') <- refine ctx1 tyC (T tyA)
    (ctx3, tyB') <- refine ctx2 tyB (T tyD)
    return (ctx3, TArr tyA' tyB')
refine ctx1 (TArr tyA tyB) (Hole e h) | null (freeExVars tyA) = do
    trace ("[S-Hole-NoEx]: " ++ show ctx1 ++ " ⊢ " ++ show (TArr tyA tyB) ++ " <: " ++ show (Hole e h)) $ return ()
    tyC <- typeof ctx1 (T tyA) e
    (ctx2, tyB') <- refine ctx1 tyB h
    return (ctx2, TArr tyA tyB')
refine ctx1 (TArr tyA tyB) (Hole e h) | notNull (freeExVars tyA) = do
    trace ("[S-Hole-Ex]: " ++ show ctx1 ++ " ⊢ " ++ show (TArr tyA tyB) ++ " <: " ++ show (Hole e h)) $ return ()
    tyC <- typeof ctx1 (T TTop) e
    (ctx2, tyA') <- refine ctx1 tyC (T tyA)
    (ctx3, tyB') <- refine ctx2 tyB h
    return (ctx3, TArr tyA' tyB')
refine ctx1 (TAll a tyA) (T (TAll b tyB)) | a == b = do
    trace ("[S-All]: " ++ show ctx1 ++ " ⊢ " ++ show (TAll a tyA) ++ " <: " ++ show (TAll b tyB)) $ return ()
    (ctx2, tyA') <- refine (TyVar a ctx1) tyA (T tyB)
    return (cleanTyCtx a ctx2, TAll a tyA')
refine ctx1 (TAll a tyA) (Hole e h) = do
    trace ("[S-Hole-All]: " ++ show ctx1 ++ " ⊢ " ++ show (TAll a tyA) ++ " <: " ++ show (Hole e h)) $ return ()
    (ctx2, tyA') <- refine (ExVar a ctx1) (subst a tyA (TExt a)) (Hole e h)
    return (cleanExCtx a ctx2, tyA')

-- 2 options available, should be careful
cleanTyCtx :: String -> Context -> Context
cleanTyCtx a Empty = Empty
cleanTyCtx a (TmVar b tyA ctx) = TmVar b tyA (cleanTyCtx a ctx)
cleanTyCtx a (TyVar b ctx) | a == b = Empty
cleanTyCtx a (TyVar b ctx) | a /= b = TyVar b (cleanTyCtx a ctx)
cleanTyCtx a (ExVar b ctx) = ExVar b (cleanTyCtx a ctx)
cleanTyCtx a (ChVar b tyA ctx) = ChVar b tyA (cleanTyCtx a ctx)

cleanExCtx :: String -> Context -> Context
cleanExCtx a Empty = Empty
cleanExCtx a (TmVar b tyA ctx) = TmVar b tyA (cleanExCtx a ctx)
cleanExCtx a (TyVar b ctx) = TyVar b (cleanExCtx a ctx)
cleanExCtx a (ExVar b ctx) | a == b = Empty
cleanExCtx a (ExVar b ctx) | a /= b = ExVar b (cleanExCtx a ctx)
cleanExCtx a (ChVar b tyA ctx) = ChVar b tyA (cleanExCtx a ctx)

lookupTmVar :: Context -> String -> Maybe Type
lookupTmVar Empty _ = Nothing
lookupTmVar (TmVar x ty ctx) y = if x == y then Just ty else lookupTmVar ctx y
lookupTmVar (TyVar _ ctx) y = lookupTmVar ctx y
lookupTmVar (ExVar _ ctx) y = lookupTmVar ctx y
lookupTmVar (ChVar _ _ ctx) y = lookupTmVar ctx y

main :: IO ()
main = do
    -- print $ subst "a" (TArr (TVar "a") (TVar "b")) TInt
    -- print $ subst "a" (TArr (TVar "a") (TVar "a")) (TExt "a")
    -- print $ freeExVars (TArr (TVar "a") (TExt "a"))
    -- print $ freeExVars (TArr (TExt "a") (TExt "b"))
    -- print $ typeof Empty (T TTop) (App (Lam "x" (Var "x")) (Lit 1))
    print $ refine Empty (TAll "a" (TArr (TVar "a") (TVar "a"))) (Hole (Lit 1) (T TTop))