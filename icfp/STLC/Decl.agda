module STLC.Decl where

open import STLC.Prelude
open import STLC.Common

----------------------------------------------------------------------
--+                                                                +--
--+                             Typing                             +--
--+                                                                +--
----------------------------------------------------------------------

-- counter, different from n in paper, we use j to represent
data Counter : Set where
  ∞ : Counter
  Z : Counter
  S : Counter → Counter

-- nonZero counter, used in subsumption rule
data ¬Z : Counter → Set where
  ¬Z-∞ : ¬Z ∞
  ¬Z-S : ∀ {j} → ¬Z (S j)

infix 4 _⊢_#_⦂_

data _⊢_#_⦂_ : Env → Counter → Term → Type → Set where

  ⊢int : ∀ {Γ i}
    → Γ ⊢ Z # (lit i) ⦂ Int

  ⊢var : ∀ {Γ x A}
    → Γ ∋ x ⦂ A
    → Γ ⊢ Z # ` x ⦂ A

  ⊢ann : ∀ {Γ e A}
    → Γ ⊢ ∞ # e ⦂ A
    → Γ ⊢ Z # (e ⦂ A) ⦂ A

  -- instead of meta-operations on paper, we split it into two rules in Agda
  -- to make it more structrual
  ⊢lam-∞ : ∀ {Γ e A B}
    → Γ , A ⊢ ∞ # e ⦂ B
    → Γ ⊢ ∞ # (ƛ e) ⦂ A `→ B

  ⊢lam-n : ∀ {Γ e A B j}
    → Γ , A ⊢ j # e ⦂ B
    → Γ ⊢ S j # (ƛ e) ⦂ A `→ B

  ⊢app₁ : ∀ {Γ e₁ e₂ A B}
    → Γ ⊢ Z # e₁ ⦂ A `→ B
    → Γ ⊢ ∞ # e₂ ⦂ A
    → Γ ⊢ Z # e₁ · e₂ ⦂ B

  ⊢app₂ : ∀ {Γ e₁ e₂ A B j}
    → Γ ⊢ (S j) # e₁ ⦂ A `→ B
    → Γ ⊢ Z # e₂ ⦂ A
    → Γ ⊢ j # e₁ · e₂ ⦂ B

  ⊢sub : ∀ {Γ e A j}
    → Γ ⊢ Z # e ⦂ A
    → ¬Z j
    → Γ ⊢ j # e ⦂ A
