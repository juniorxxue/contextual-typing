module Algo2 where

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
infixr 8 _*⇒_
infixr 8 ⟦_⟧

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
  _*⇒_  : Hype → Hype → Hype
  ⟦_⟧ : Term → Hype


_ : Hype
_ = ⟦ lit 1 ⟧ *⇒ Hnt

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
infix 4 _⊢_⇛_⇛_ 

data _⊢_≤_ : Context → Hype → Hype → Set
data _⊢_⇛_⇛_ : Context → Hype → Term → Type → Set

h : Type → Hype
h Int = Hnt
h Top = Hnt
h (A ⇒ B) = (h A) *⇒ (h B)

-- unh : Hype → Type
-- unh Hnt = Int
-- unh Hop = Top
-- unh (A *⇒ B) = (unh A) ⇒ (unh B)

data _⊢_≤_ where
  ≤-int : ∀ {Γ}
    → Γ ⊢ Hnt ≤ Hnt
  ≤-top : ∀ {Γ A}
    → Γ ⊢ A ≤ Hop
  ≤-arr : ∀ {Γ A B C D}
    → Γ ⊢ C ≤ A
    → Γ ⊢ B ≤ D
    → Γ ⊢ (A *⇒ B) ≤ (C *⇒ D)
  ≤-hole : ∀ {Γ A B e}
    → Γ ⊢ A ⇛ e ⇛ B
    → Γ ⊢ ⟦ e ⟧ ≤ A

data _⊢_⇛_⇛_ where

  ty-lit : ∀ {Γ A n}
    → Γ ⊢ Hnt ≤ A
    → Γ ⊢ A ⇛ lit n ⇛ Int

  ty-var : ∀ {Γ A B x}
    → Γ ∋ x ⦂ B
    → Γ ⊢ h B ≤ A
    → Γ ⊢ A ⇛ ` x ⇛ B

  ty-app : ∀ {Γ e₁ e₂ A C D}
    → Γ ⊢ ⟦ e₂ ⟧ *⇒ A ⇛ e₁ ⇛ (C ⇒ D)
    → Γ ⊢ A ⇛ e₁ · e₂ ⇛ D

  ty-ann : ∀ {Γ e A B}
    → Γ ⊢ h B ⇛ e ⇛ B
    → Γ ⊢ h B ≤ A
    → Γ ⊢ A ⇛ e ⦂ B ⇛ B

  ty-lam₁ : ∀ {Γ e₁ e x A B C}
    → Γ ⊢ Hop ⇛ e₁ ⇛ A
    → Γ , x ⦂ A ⊢ B ⇛ e ⇛ C
    → Γ ⊢ ⟦ e₁ ⟧ *⇒ B ⇛ ƛ x ⇒ e ⇛ A ⇒ C

  ty-lam₂ : ∀ {Γ x e A B C}
    → Γ , x ⦂ A ⊢ B ⇛ e ⇛ C
    → Γ ⊢ h A *⇒ B ⇛ ƛ x ⇒ e ⇛ A ⇒ C


_ : ∅ ⊢ Hop ⇛ (ƛ "x" ⇒ ` "x") · lit 1 ⇛ Int
_ = ty-app (ty-lam₁ (ty-lit ≤-top) (ty-var Z ≤-top))

_ : ∅ ⊢ Hop ⇛ ((ƛ "f" ⇒ ` "f" · (lit 1)) ⦂ (Int ⇒ Int) ⇒ Int) · (ƛ "x" ⇒ ` "x") ⇛ Int
_ = ty-app (ty-ann (ty-lam₂ (ty-app (ty-var Z (≤-arr (≤-hole (ty-lit ≤-int)) ≤-int)))) (≤-arr (≤-hole (ty-lam₂ {A = Int} (ty-var Z ≤-int))) ≤-top))
