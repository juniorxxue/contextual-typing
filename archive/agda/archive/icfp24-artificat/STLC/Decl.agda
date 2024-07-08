module STLC.Decl where

open import STLC.Prelude
open import STLC.Common

----------------------------------------------------------------------
--+                                                                +--
--+                             Typing                             +--
--+                                                                +--
----------------------------------------------------------------------

data Counter : Set where
  ∞ : Counter
  ‶_ : ℕ → Counter

infix 4 _⊢d_#_⦂_

data _⊢d_#_⦂_ : Context → Counter → Term → Type → Set where

  ⊢d-int : ∀ {Γ i}
    → Γ ⊢d ‶ 0 # (lit i) ⦂ Int

  ⊢d-var : ∀ {Γ x A}
    → Γ ∋ x ⦂ A
    → Γ ⊢d ‶ 0 # ` x ⦂ A

  ⊢d-ann : ∀ {Γ e A}
    → Γ ⊢d ∞ # e ⦂ A
    → Γ ⊢d ‶ 0 # (e ⦂ A) ⦂ A

  ⊢d-lam-∞ : ∀ {Γ e A B}
    → Γ , A ⊢d ∞ # e ⦂ B
    → Γ ⊢d ∞ # (ƛ e) ⦂ A ⇒ B

  ⊢d-lam-n : ∀ {Γ e A B n}
    → Γ , A ⊢d ‶ n # e ⦂ B
    → Γ ⊢d ‶ (suc n) # (ƛ e) ⦂ A ⇒ B

  ⊢d-app₁ : ∀ {Γ e₁ e₂ A B}
    → Γ ⊢d ‶ 0 # e₁ ⦂ A ⇒ B
    → Γ ⊢d ∞ # e₂ ⦂ A
    → Γ ⊢d ‶ 0 # e₁ · e₂ ⦂ B

  ⊢d-app₂ : ∀ {Γ e₁ e₂ A B n}
    → Γ ⊢d ‶ (suc n) # e₁ ⦂ A ⇒ B
    → Γ ⊢d ‶ 0 # e₂ ⦂ A
    → Γ ⊢d ‶ n # e₁ · e₂ ⦂ B

  ⊢d-app₃ : ∀ {Γ e₁ e₂ A B}
    → Γ ⊢d ∞ # e₁ ⦂ A ⇒ B
    → Γ ⊢d ‶ 0 # e₂ ⦂ A
    → Γ ⊢d ∞ # e₁ · e₂ ⦂ B

  ⊢d-sub : ∀ {Γ e A j}
    → Γ ⊢d ‶ 0 # e ⦂ A
    → j ≢ ‶ 0
    → Γ ⊢d j # e ⦂ A
