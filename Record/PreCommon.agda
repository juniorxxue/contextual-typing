module Record.PreCommon where
-- this module is intended to share with TAS

open import Record.Prelude hiding (_≤?_)

Label = ℕ

infixr 8 _`→_
infixr 8 _&_

data Type : Set where
  Int : Type
  Float : Type
  Top : Type
  _`→_ : Type → Type → Type
  _&_ : Type → Type → Type
  τ⟦_↦_⟧ : Label → Type → Type

data Constant : Set where
  lit      : ℕ → Constant
  flt      : 𝔽 → Constant
  +s       : Constant
  +i       : ℕ → Constant
  +f       : 𝔽 → Constant

c-τ : Constant → Type
c-τ (lit n) = Int
c-τ (flt n) = Float
c-τ +s = (Int `→ Int `→ Int) & (Float `→ Float `→ Float)
c-τ (+i n) = Int `→ Int
c-τ (+f n) = Float `→ Float

infixl 5  _,_

data Env : Set where
  ∅     : Env
  _,_   : Env → Type → Env

infix  4  _∋_⦂_

data _∋_⦂_ : Env → ℕ → Type → Set where

  Z : ∀ {Γ A}
      ------------------
    → Γ , A ∋ zero ⦂ A

  S : ∀ {Γ A B n}
    → Γ ∋ n ⦂ A
      ------------------
    → Γ , B ∋ (suc n) ⦂ A
