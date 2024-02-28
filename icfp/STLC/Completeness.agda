module STLC.Completeness where

open import STLC.Prelude hiding (_≤?_) renaming (_≤_ to _≤n_)
open import STLC.Common
open import STLC.Decl
open import STLC.Algo
open import STLC.Algo.Properties
open import STLC.Properties

infix 3 _⊢_~_

data _⊢_~_ : Context → Counter × Type → Hint → Set

data _⊢_~_ where

  ~Z : ∀ {Γ A}
    → Γ ⊢ ⟨ Z , A ⟩ ~ □

  ~∞ : ∀ {Γ A }
    → Γ ⊢ ⟨ ∞ , A ⟩ ~ τ A

  ~S⇒ : ∀ {Γ j A B H e}
    → Γ ⊢a □ ⇛ e ⇛ A
    → Γ ⊢ ⟨ j , B ⟩ ~ H
    → Γ ⊢ ⟨ S j , A ⇒ B ⟩ ~ (⟦ e ⟧⇒ H)

~weaken : ∀ {Γ A j B H n n≤l}
  → Γ ⊢ ⟨ j , B ⟩ ~ H
  → Γ ↑ n [ n≤l ] A ⊢ ⟨ j , B ⟩ ~ (H ⇧ n)
~weaken ~Z = ~Z
~weaken ~∞ = ~∞
~weaken (~S⇒ ⊢e j~H) = ~S⇒ (⊢a-weaken ⊢e) (~weaken j~H)

complete : ∀ {Γ H j e A}
  → Γ ⊢d j # e ⦂ A
  → Γ ⊢ ⟨ j , A ⟩ ~ H
  → Γ ⊢a H ⇛ e ⇛ A

complete-≈ : ∀ {Γ A j H}
  → Γ ⊢ ⟨ j , A ⟩ ~ H
  → Γ ⊢a A ≈ H

complete-≈ ~Z = ≈□
complete-≈ ~∞ = ≈τ
complete-≈ (~S⇒ ⊢e j~H) = ≈hole (subsumption-0 ⊢e ≈τ) (complete-≈ j~H)

complete ⊢d-int ~Z = ⊢a-lit
complete (⊢d-var x) ~Z = ⊢a-var x
complete (⊢d-ann ⊢e) ~Z = ⊢a-ann (complete ⊢e ~∞)
complete (⊢d-lam-∞ x) ~∞ = ⊢a-lam₁ (complete x ~∞)
complete (⊢d-lam-n x) (~S⇒ ⊢e A~j) = ⊢a-lam₂ ⊢e (complete x (~weaken {n≤l = z≤n} A~j))
complete (⊢d-app₁ ⊢e ⊢e₁) A~j = ⊢a-app (subsumption-0 (complete ⊢e ~Z) (≈hole (complete ⊢e₁ ~∞) (complete-≈ A~j)))
complete (⊢d-app₂ ⊢e ⊢e₁) A~j = ⊢a-app (complete ⊢e (~S⇒ (complete ⊢e₁ ~Z) A~j))
complete (⊢d-sub ⊢e neq) A~j = subsumption-0 (complete ⊢e ~Z) (complete-≈ A~j)

-- corollaries

complete-inf : ∀ {Γ e A}
  → Γ ⊢d Z # e ⦂ A
  → Γ ⊢a □ ⇛ e ⇛ A
complete-inf ⊢e = complete ⊢e ~Z


complete-chk : ∀ {Γ e A}
  → Γ ⊢d ∞ # e ⦂ A
  → Γ ⊢a τ A ⇛ e ⇛ A
complete-chk ⊢e = complete ⊢e ~∞
