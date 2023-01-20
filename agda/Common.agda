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

infix 4 _⊢_

data _⊢_ : Context → Term → Set where

  wf-lit : ∀ {Γ n}
    → Γ ⊢ (lit n)
  
  wf-var : ∀ {Γ x A}
    → Γ ∋ x ⦂ A
    → Γ ⊢ ` x

  wf-lam : ∀ {Γ x A e}
    → Γ , x ⦂ A ⊢ e
    → Γ ⊢ ƛ x ⇒ e

  wf-app : ∀ {Γ e₁ e₂}
    → Γ ⊢ e₁
    → Γ ⊢ e₂
    → Γ ⊢ e₁ · e₂

  wf-ann : ∀ {Γ e A}
    → Γ ⊢ e
    → Γ ⊢ e ⦂ A
