module Algo where

open import Data.Nat using (ℕ)
open import Data.String using (String)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl)

Id : Set
Id = String

infixr 5 ƛ_⇒_
infixl 7 _·_
infix  9 `_
infix  5 _⦂_
infixr 8 _⇒_
infixr 8 _⇛_
infixr 8 ⟦_⟧⇛_

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

data Hype : Set where
  Hnt : Hype
  Hop : Hype
  _⇛_  : Hype → Hype → Hype
  ⟦_⟧⇛_ : Term → Hype → Hype


_ : Hype
_ = ⟦ lit 1 ⟧⇛ Hnt

data Mode : Set where
  ⇛ : Mode
  ⇚ : Mode

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

infix 5 _⊢_≤_

data _⊢_≤_ : Context → Hype → Hype → Set
data _⊢_⇛_⇛_ : Context → Hype → Term → Type → Set

data _⊢_≤_ where
  ≤-int : ∀ {Γ}
    → Γ ⊢ Hnt ≤ Hnt
  ≤-top : ∀ {Γ A}
    → Γ ⊢ A ≤ Hop
  ≤-arr : ∀ {Γ A B C D}
    → Γ ⊢ C ≤ A
    → Γ ⊢ B ≤ D
    → Γ ⊢ (A ⇛ B) ≤ (C ⇛ D)
  ≤-hole : ∀ {Γ e A B C}
    → Γ ⊢ B ≤ C
    → Γ ⊢ Hop ⇛ e ⇛ A'
    → Γ ⊢ A' ≤ A
    → A ⇛ B ≤ ⟦ e ⟧⇛ C
