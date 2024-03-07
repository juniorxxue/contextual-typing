{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE InstanceSigs #-}

module Main where

-- we have two choices for the type application:
-- (1) push them to the context, and instantiate it in the subtyping
-- (2) direct instantiate it in the typing rule (simpler way, try this one first)

-- worklist impl
data Type where
  TVar :: String -> Type
  TInt :: Type
  TArr :: Type -> Type -> Type
  TAll :: String -> Type -> Type
  TExt :: String -> Type

instance Eq Type where
  (==) :: Type -> Type -> Bool
  (==) (TVar a) (TVar b) = a == b
  (==) TInt TInt = True
  (==) (TArr tyA tyB) (TArr tyC tyD) = tyA == tyC && tyB == tyD
  (==) (TAll a tyA) (TAll b tyB) = a == b && tyA == tyB
  (==) (TExt a) (TExt b) = a == b
  (==) _ _ = False

instance Show Type where
  show :: Type -> String
  show (TVar a) = a
  show TInt = "Int"
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
  No :: Hint
  T :: Type -> Hint
  Hole :: Term -> Hint -> Hint

instance Show Hint where
  show :: Hint -> String
  show No = "[]"
  show (T ty) = show ty
  show (Hole e h) = "[" ++ show e ++ "]" ++ " → " ++ show h

-- Worklist Algorithms
type Worklist = ([Work], [Type])

data Work where
  WTVar :: String -> Work -- T, a
  WEVar :: String -> Work
  WBind :: String -> Type -> Work
  WSub :: Type -> Hint -> Work

instance {-# OVERLAPPING #-} Show [Work] where
  show :: [Work] -> String
  show [] = "."
  show (WTVar x : w) = show w ++ ", " ++ x
  show (WEVar x : w) = show w ++ ", ^" ++ x
  show (WBind x ty : w) = show w ++ ", " ++ x ++ " : " ++ show ty
  show (WSub ty h : w) = show w ++ ", " ++ show ty ++ " <: " ++ show h

instance {-# OVERLAPPING #-} Show [Type] where
  show :: [Type] -> String
  show [] = "."
  show (ty : s) = show s ++ ", " ++ show ty

-- w[^a/A]
subst :: [Work] -> String -> Type -> [Work]
subst ws exa tyA = undefined

-- A[a/^a]
substTy :: Type -> String -> Type -> Type
substTy = undefined

type Context = [(String, Type)]

infer :: Context -> Hint -> Term -> Maybe Type
infer ctx h e = undefined

-- context

step :: Worklist -> Worklist
-- step ([], []) = []
step (WSub TInt (T TInt) : w, s) = (w, TInt : s)
step ((WSub (TExt a) (T tyA)) : w, s) = (subst w a tyA, tyA : s)
step ((WSub tyA (T (TExt a))) : w, s) = (subst w a tyA, tyA : s)
-- step ((WSub tyA (T TTop)) : w, s) = (w, TTop : s) -- do we include top in poly system?
step ((WSub (TArr tyA tyB) (T (TArr tyC tyD))) : w, s) = (WSub tyC (T tyA) : WSub tyB (T tyD) : w, s)
step ([], tyA : tyB : s) = ([], TArr tyA tyB : s) -- a bit worried about order of tyA and tyB
-- deal with holes
step (WSub (TArr tyA tyB) (Hole e h) : w, s) = (WSub tyB h : w, tyA : s) -- side condition, if checkable
step (WSub (TArr tyA tyB) (Hole e h) : w, s) = (WSub tyC (T tyA) : WSub tyB h : w, tyB : s) -- what's the context here?
step (WSub (TAll a tyA) (T (TAll b tyB)) : w, s) | a == b = (WSub tyA (T tyB) : WTVar a : w, s)
step (WTVar a : w, tyA : s) = (w, TAll a tyA : s)
step (WSub (TAll a tyA) (Hole e h) : w, s) = (WSub (substTy tyA a (TExt a)) (Hole e h) : WEVar a : w, s)

main :: IO ()
main = putStrLn "Hello, Haskell!"
