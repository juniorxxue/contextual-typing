module Common where

open import Data.Nat using (ℕ)
open import Data.String using (String)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl)

Id : Set
Id = String

infixr  5  ƛ_⇒_
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
  `_       : Id → Term
  ƛ_⇒_     : Id → Term → Term
  _·_      : Term → Term → Term
  _⦂_      : Term → Type → Term

infixl 5  _,_⦂_

data Context : Set where
  ∅     : Context
  _,_⦂_ : Context → Id → Type → Context

infix  4  _∋_⦂_

data _∋_⦂_ : Context → Id → Type → Set where

  Z : ∀ {Γ x A}
      ------------------
    → Γ , x ⦂ A ∋ x ⦂ A

  S : ∀ {Γ x y A B}
    → x ≢ y
    → Γ ∋ x ⦂ A
      ------------------
    → Γ , y ⦂ B ∋ x ⦂ A

infix 4 _⊨e_

data _⊨e_ : Context → Term → Set where

  ⊨e-lit : ∀ {Γ n}
    → Γ ⊨e (lit n)
  
  ⊨e-var : ∀ {Γ x A}
    → Γ ∋ x ⦂ A
    → Γ ⊨e ` x

  ⊨e-lam : ∀ {Γ x A e}
    → Γ , x ⦂ A ⊨e e
    → Γ ⊨e ƛ x ⇒ e

  ⊨e-app : ∀ {Γ e₁ e₂}
    → Γ ⊨e e₁
    → Γ ⊨e e₂
    → Γ ⊨e e₁ · e₂

  ⊨e-ann : ∀ {Γ e A}
    → Γ ⊨e e
    → Γ ⊨e e ⦂ A
