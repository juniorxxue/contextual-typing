module Common where

open import Data.Nat using (ℕ; zero; suc; _+_; _*_; _^_; _∸_; _<?_)
open import Data.String using (String)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl)
open import Relation.Nullary using (Dec; yes; no)

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

shift : ℕ → ℕ → Term → Term
shift c d (lit n) = lit n
shift c d (` k) with k <? c
... | yes k<c = ` k
... | no k≥c = ` (k + d)
shift c d (ƛ e) = ƛ (shift (suc c) d e)
shift c d (e₁ · e₂) = (shift c d e₁) · (shift c d e₂)
shift c d (e ⦂ A) = (shift c d e) ⦂ A

infix 6 _↑_
_↑_ : ℕ → Term → Term
d ↑ e = shift 0 d e
