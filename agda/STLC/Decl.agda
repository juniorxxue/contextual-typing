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
  c_ : ℕ → Counter

succ : Counter → Counter
succ ∞ = ∞
succ (c n) = c (suc n)

infix 4 _⊢d_#_⦂_

data _⊢d_#_⦂_ : Context → Counter → Term → Type → Set where
  ⊢d-int : ∀ {Γ i}
    → Γ ⊢d (c 0) # (lit i) ⦂ Int

  ⊢d-var : ∀ {Γ x A}
    → Γ ∋ x ⦂ A
    → Γ ⊢d (c 0) # ` x ⦂ A

  ⊢d-lam-∞ : ∀ {Γ e A B}
    → Γ , A ⊢d ∞ # e ⦂ B
    → Γ ⊢d ∞ # (ƛ e) ⦂ A ⇒ B

  ⊢d-lam-n : ∀ {Γ e A B n}
    → Γ , A ⊢d c n # e ⦂ B
    → Γ ⊢d c (suc n) # (ƛ e) ⦂ A ⇒ B

  ⊢d-app₁ : ∀ {Γ e₁ e₂ A B}
    → Γ ⊢d (c 0) # e₁ ⦂ A ⇒ B
    → Γ ⊢d ∞ # e₂ ⦂ A
    → Γ ⊢d (c 0) # e₁ · e₂ ⦂ B

  ⊢d-app₂ : ∀ {Γ e₁ e₂ A B n}
    → Γ ⊢d (c (suc n)) # e₁ ⦂ A ⇒ B
    → Γ ⊢d (c 0) # e₂ ⦂ A
    → Γ ⊢d (c n) # e₁ · e₂ ⦂ B

  ⊢d-app₃ : ∀ {Γ e₁ e₂ A B}
    → Γ ⊢d ∞ # e₁ ⦂ A ⇒ B
    → Γ ⊢d (c 0) # e₂ ⦂ A
    → Γ ⊢d ∞ # e₁ · e₂ ⦂ B

  ⊢d-ann : ∀ {Γ e A n}
    → Γ ⊢d ∞ # e ⦂ A
    → Γ ⊢d (c n) # (e ⦂ A) ⦂ A

  ⊢d-sub : ∀ {Γ e A}
    → Γ ⊢d c 0 # e ⦂ A
    → Γ ⊢d ∞ # e ⦂ A
