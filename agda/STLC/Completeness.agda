module STLC.Completeness where

open import STLC.Prelude hiding (_≤?_) renaming (_≤_ to _≤n_)
open import STLC.Common
open import STLC.Decl
open import STLC.Algo
open import STLC.Algo.Properties

----------------------------------------------------------------------
--+                                                                +--
--+                          Subsumption                           +--
--+                                                                +--
----------------------------------------------------------------------


----------------------------------------------------------------------
--+                                                                +--
--+                          Completeness                          +--
--+                                                                +--
----------------------------------------------------------------------
infix 4 _⊩a_⇛_

data _⊩a_⇛_ : Context → List Term → List Type → Set where

  ⊩a-none : ∀ {Γ}
    → Γ ⊩a [] ⇛ []

  ⊩a-cons : ∀ {Γ es As e A}
    → Γ ⊩a es ⇛ As
    → Γ ⊢a □ ⇛ e ⇛ A
    → Γ ⊩a (e ∷ es) ⇛ (A ∷ As)

infix 4 _⇴_≗_

data _⇴_≗_ : List Term → Hint → Hint → Set where

  cht-none-□ :
      [] ⇴ □ ≗ □

  cht-none-τ : ∀ {A}
    → [] ⇴ τ A ≗ (τ A)

  cht-cons : ∀ {e es H H'}
    → es ⇴ H ≗ H'
    → (e ∷ es) ⇴ H ≗ ⟦ e ⟧⇒ H'


infix 4 _↪_❪_,_,_❫

data _↪_❪_,_,_❫ : Type → Counter → List Type → Type → Counter → Set where

  n-z : ∀ {A}
    → A ↪ Z ❪ [] , A , Z ❫

  n-∞ : ∀ {A}
    → A ↪ ∞ ❪ [] , A , ∞ ❫

  n-s : ∀ {A B T j Bs j'}
    → B ↪ j ❪ Bs , T , j' ❫
    → (A ⇒ B) ↪ (S j) ❪ A ∷ Bs , T , j' ❫

complete-chk : ∀ {Γ e A j es As T H}
  → Γ ⊢d j # e ⦂ A
  → A ↪ j ❪ As , T , ∞ ❫
  → Γ ⊩a es ⇛ As
  → es ⇴ τ T ≗ H
  → Γ ⊢a H ⇛ e ⇛ A

complete-inf : ∀ {Γ e A j es As T H}
  → Γ ⊢d j # e ⦂ A
  → A ↪ j ❪ As , T , Z ❫
  → Γ ⊩a es ⇛ As
  → es ⇴ □ ≗ H
  → Γ ⊢a H ⇛ e ⇛ A

complete-chk (⊢d-lam-∞ ⊢e) Aj ⊩es newH = {!newH!}
complete-chk (⊢d-lam-n ⊢e) Aj ⊩es newH = {!!}
complete-chk (⊢d-app₂ ⊢e ⊢e₁) Aj ⊩es newH = {!!}
complete-chk (⊢d-sub ⊢e x) Aj ⊩es newH = {!!}

complete-inf ⊢d-int n-z ⊩a-none cht-none-□ = ⊢a-lit
complete-inf (⊢d-var x) n-z ⊩es newH = {!!}
complete-inf (⊢d-ann ⊢e) Aj ⊩es newH = {!!}
complete-inf (⊢d-lam-n ⊢e) Aj ⊩es newH = {!!}
complete-inf (⊢d-app₁ ⊢e ⊢e₁) Aj ⊩es newH = {!!}
complete-inf (⊢d-app₂ ⊢e ⊢e₁) Aj ⊩es newH = {!!}
complete-inf (⊢d-sub ⊢e x) Aj ⊩es newH = {!!}
