module Common where

open import Data.Nat using (ℕ)
open import Data.String using (String)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl)

Id : Set
Id = String

infixr 5  ƛ_⇒_
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

----------------------------------------------------------------------
--+                                                                +--
--+                         Free Variables                         +--
--+                                                                +--
----------------------------------------------------------------------

data free : Term → Id → Set where

  fr-var : ∀ {x}
    → free (` x) x

  fr-lam : ∀ {x y e}
    → free e x
    → x ≢ y
    → free (ƛ y ⇒ e) x

  fr-app-l : ∀ {x e₁ e₂}
    → free e₁ x
    → free (e₁ · e₂) x

  fr-app-r : ∀ {x e₁ e₂}
    → free e₂ x
    → free (e₁ · e₂) x

  free-ann : ∀ {x e A}
    → free e x
    → free (e ⦂ A) x
