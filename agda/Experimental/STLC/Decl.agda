module STLC.Decl where

open import STLC.Prelude
open import STLC.Common

----------------------------------------------------------------------
--+                                                                +--
--+                             Typing                             +--
--+                                                                +--
----------------------------------------------------------------------

Counter : Set
Counter = ℕ

infix 4 _⊢d_#_⦂_

data _⊢d_#_⦂_ : Context → Counter → Term → Type → Set where

  ⊢d-int : ∀ {Γ i}
    → Γ ⊢d 0 # (lit i) ⦂ Int

  ⊢d-var : ∀ {Γ x A}
    → Γ ∋ x ⦂ A
    → Γ ⊢d 0 # ` x ⦂ A

  ⊢d-ann : ∀ {Γ e A j}
    → Γ ⊢d j # e ⦂ A
    → Γ ⊢d 0 # (e ⦂ A) ⦂ A
    
  ⊢d-lam : ∀ {Γ e A B j}
    → Γ , A ⊢d j # e ⦂ B
    → Γ ⊢d suc j # (ƛ e) ⦂ A ⇒ B

  ⊢d-app₁ : ∀ {Γ e₁ e₂ A B j}
    → Γ ⊢d 0 # e₁ ⦂ A ⇒ B
    → Γ ⊢d j # e₂ ⦂ A
    → Γ ⊢d 0 # e₁ · e₂ ⦂ B

  ⊢d-app₂ : ∀ {Γ e₁ e₂ A B j}
    → Γ ⊢d (suc j) # e₁ ⦂ A ⇒ B
    → Γ ⊢d 0 # e₂ ⦂ A
    → Γ ⊢d j # e₁ · e₂ ⦂ B

  ⊢d-sub : ∀ {Γ e A j}
    → Γ ⊢d 0 # e ⦂ A
    → Γ ⊢d (suc j) # e ⦂ A


ex1 : ∅ ⊢d 0 # ((lit 2) ⦂ Int) ⦂ Int
ex1 = ⊢d-ann ⊢d-int
