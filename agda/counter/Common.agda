module Common where

open import Data.String using (String)
open import Data.Bool using (Bool; true; false; T; not)
open import Data.Nat using (ℕ; zero; suc; pred; _+_; _*_; _^_; _∸_; _≤?_; _≤_; s≤s)
open import Data.Nat.Properties using (m≤n⇒m≤1+n; ≤-pred)
open import Relation.Nullary using (yes; no; Dec)
open import Relation.Nullary.Decidable using (True; toWitness; fromWitness)
open import Function.Base using (case_of_; case_return_of_)
open import Relation.Binary using (Decidable)
import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; cong)
open import Data.Empty

open import Data.Product using (_×_; proj₁; proj₂; ∃; ∃-syntax) renaming (_,_ to ⟨_,_⟩)

Id : Set
Id = String

infixr 5  ƛ_
infixl 7  _·_
infix  9  `_
infix  5  _⦂_
infixr 8 _⇒_

data Type : Set where
  Int : Type
  Top : Type
  _⇒_ : Type → Type → Type

data Term : Set where
  lit      : ℕ → Term
  `_       : ℕ → Term
  ƛ_       : Term → Term
  _·_      : Term → Term → Term
  _⦂_      : Term → Type → Term

infixl 5  _,_

data Context : Set where
  ∅     : Context
  _,_   : Context → Type → Context

infix  4  _∋_⦂_

data _∋_⦂_ : Context → ℕ → Type → Set where

  Z : ∀ {Γ A}
      ------------------
    → Γ , A ∋ zero ⦂ A

  S : ∀ {Γ A B n}
    → Γ ∋ n ⦂ A
      ------------------
    → Γ , B ∋ (suc n) ⦂ A

----------------------------------------------------------------------
--+                                                                +--
--+                             Shift                              +--
--+                                                                +--
----------------------------------------------------------------------

↑-var : ℕ → ℕ → ℕ
↑-var n x with n ≤? x
... | yes n≤x = suc x
... | no  n>x = x

infixl 7 _↑_
_↑_ : Term → ℕ → Term
lit i ↑ n = lit i
` x ↑ n = ` (↑-var n x)
(ƛ e) ↑ n = ƛ (e ↑ (suc n))
e₁ · e₂ ↑ n = (e₁ ↑ n) · (e₂ ↑ n)
(e ⦂ A) ↑ n = (e ↑ n) ⦂ A

↓-var : ℕ → ℕ → ℕ
↓-var n x with (suc n) ≤? x
... | yes n+1≤x = pred x
... | no n+1>x   = x

infixl 7 _↓_
_↓_ : Term → ℕ → Term
lit i ↓ n = lit i
` x ↓ n = ` (↓-var n x)
(ƛ e) ↓ n = ƛ (e ↓ (suc n))
e₁ · e₂ ↓ n = (e₁ ↓ n) · (e₂ ↓ n)
(e ⦂ A) ↓ n = (e ↓ n) ⦂ A

↓-↑-var : ∀ x n → ↓-var n (↑-var n x) ≡ x
↓-↑-var x n with n ≤? x
...         | yes n≤x with suc n ≤? suc x
...                   | yes n+1≤x+1 = pred-suc x
                            where pred-suc : ∀ n → pred (suc n) ≡ n
                                  pred-suc zero = refl
                                  pred-suc (suc n) = refl
...                   | no  n+1>x+1 = ⊥-elim (n+1>x+1 (s≤s n≤x))
↓-↑-var x n | no n>x with suc n ≤? x
...                   | yes n+1≤x = ⊥-elim (n>x (n+1≤x→n≤x n+1≤x))
                            where n+1≤x→n≤x : ∀ {n x} → suc n ≤ x → n ≤ x
                                  n+1≤x→n≤x n+1≤x = ≤-pred (m≤n⇒m≤1+n n+1≤x)
...                   | no  n+1>x = refl


postulate

  ↑-↑-comm : ∀ e m n → m ≤ n → e ↑ m ↑ suc n ≡ e ↑ n ↑ m

{-
↑-↑-comm (lit _) m n m≤n = refl
↑-↑-comm (` x) m n m≤n with n ≤? x | m ≤? x
... | yes n≤x | yes m≤x = {!!}
... | yes n≤x | no  m>x = {!!}
... | no  n>x | yes m≤x = {!!}
... | no  n>x | no  m>x = {!!} 
↑-↑-comm (ƛ e) m n m≤n rewrite ↑-↑-comm e (suc m) (suc n) (s≤s m≤n) = refl
↑-↑-comm (e₁ · e₂) m n m≤n rewrite ↑-↑-comm e₁ m n m≤n | ↑-↑-comm e₂ m n m≤n = refl
↑-↑-comm (e ⦂ A) m n m≤n rewrite ↑-↑-comm e m n m≤n = refl
-}
