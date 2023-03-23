module Common where

open import Data.Nat using (ℕ; zero; suc; _+_; _*_; _^_; _∸_)
open import Data.String using (String)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl)

Id : Set
Id = String

infixr  5  ƛ_
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
  ƛ_     : Term → Term
  _·_      : Term → Term → Term
  _⦂_      : Term → Type → Term

infixl 5  _,_

data Context : Set where
  ∅     : Context
  _,_ : Context → Type → Context

infix  4  _∋_⦂_

data _∋_⦂_ : Context → ℕ → Type → Set where

  Z : ∀ {Γ A}
      ------------------
    → Γ , A ∋ zero ⦂ A

  S : ∀ {Γ A B n}
    → Γ ∋ n ⦂ A
      ------------------
    → Γ , B ∋ (suc n) ⦂ A

infix 4 _⊨e_

data _⊨e_ : Context → Term → Set where

  ⊨e-lit : ∀ {Γ n}
    → Γ ⊨e (lit n)
  
  ⊨e-var : ∀ {Γ x A}
    → Γ ∋ x ⦂ A
    → Γ ⊨e ` x

  ⊨e-lam : ∀ {Γ A e}
    → Γ , A ⊨e e
    → Γ ⊨e ƛ e

  ⊨e-app : ∀ {Γ e₁ e₂}
    → Γ ⊨e e₁
    → Γ ⊨e e₂
    → Γ ⊨e e₁ · e₂

  ⊨e-ann : ∀ {Γ e A}
    → Γ ⊨e e
    → Γ ⊨e e ⦂ A
