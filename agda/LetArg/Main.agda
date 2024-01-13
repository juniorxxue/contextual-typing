module LetArg.Main where

open import LetArg.Prelude

Id : Set
Id = String

infixr 5  ƛ_⇒_
infixl 7  _·_
infix  9  `_
infixr 6  _⦂_
infixr 8 _⇒_

data Type : Set where
  Int : Type
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
--+                     Let Argument Go First                      +--
--+                                                                +--
----------------------------------------------------------------------

data AppContext : Set where
  ∅     : AppContext
  _,,_   : AppContext → Type → AppContext

infix 3 _~_⊢_⇒_

data _~_⊢_⇒_ : Context → AppContext → Term → Type → Set where

  ⊢int : ∀ {Γ n}
    → Γ ~ ∅ ⊢ lit n ⇒ Int

  ⊢var : ∀ {Γ x A}
    → Γ ∋ x ⦂ A
    → Γ ~ ∅ ⊢ ` x ⇒ A

  ⊢lam : ∀ {Γ : Context} {Ψ : AppContext} {e x A B}
    → (Γ , x ⦂ A) ~ Ψ ⊢ e ⇒ B
    → Γ ~ (Ψ ,, A) ⊢ (ƛ x ⇒ e) ⇒ (A ⇒ B)

  ⊢app : ∀ {Γ Ψ e₁ e₂ A B}
    → Γ ~ ∅ ⊢ e₂ ⇒ A
    → Γ ~ Ψ ,, A ⊢ e₁ ⇒ (A ⇒ B)
    → Γ ~ Ψ ⊢ e₁ · e₂ ⇒ B


