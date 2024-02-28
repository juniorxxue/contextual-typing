module STLC.Completeness where

open import STLC.Prelude hiding (_≤?_) renaming (_≤_ to _≤n_)
open import STLC.Common
open import STLC.Decl
open import STLC.Properties
open import STLC.Algo
open import STLC.Algo.Properties

infix 3 _⊢_~_

data _⊢_~_ : Context → Counter × Type → Hint → Set

data _⊢_~_ where

  ~Z : ∀ {Γ A}
    → Γ ⊢ ⟨ ‶ 0 , A ⟩ ~ □

  ~∞ : ∀ {Γ A }
    → Γ ⊢ ⟨ ∞ , A ⟩ ~ τ A

  ~∞⇒ : ∀ {Γ A B e H}
    → Γ ⊢a □ ⇛ e ⇛ A
    → Γ ⊢ ⟨ ∞ , B ⟩ ~ H
    → Γ ⊢ ⟨ ∞ , A ⇒ B ⟩ ~ ⟦ e ⟧⇒ H

  ~S⇒ : ∀ {Γ j A B H e}
    → Γ ⊢a □ ⇛ e ⇛ A
    → Γ ⊢ ⟨ ‶ j , B ⟩ ~ H
    → Γ ⊢ ⟨ ‶ suc j , A ⇒ B ⟩ ~ (⟦ e ⟧⇒ H)

~weaken : ∀ {Γ A j B H n n≤l}
  → Γ ⊢ ⟨ j , B ⟩ ~ H
  → Γ ↑ n [ n≤l ] A ⊢ ⟨ j , B ⟩ ~ (H ⇧ n)
~weaken ~Z = ~Z
~weaken ~∞ = ~∞
~weaken (~∞⇒ ⊢e j~H) = ~∞⇒ (⊢a-weaken ⊢e) (~weaken j~H)
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
complete-≈ (~∞⇒ ⊢e j~H) = ≈hole (subsumption-0 ⊢e ≈τ) (complete-≈ j~H)
complete-≈ (~S⇒ ⊢e j~H) = ≈hole (subsumption-0 ⊢e ≈τ) (complete-≈ j~H)

complete ⊢d-int ~Z = ⊢a-lit
complete (⊢d-var x) ~Z = ⊢a-var x
complete (⊢d-ann ⊢e) ~Z = ⊢a-ann (complete ⊢e ~∞)
complete (⊢d-lam-∞ ⊢e) ~∞ = ⊢a-lam₁ (complete ⊢e ~∞)
complete (⊢d-lam-∞ ⊢e) (~∞⇒ ⊢e' A~j) = ⊢a-lam₂ ⊢e' (complete ⊢e (~weaken {n≤l = z≤n} A~j))
complete (⊢d-lam-n ⊢e) (~S⇒ ⊢e' j~H)= ⊢a-lam₂ ⊢e' (complete ⊢e (~weaken {n≤l = z≤n} j~H))
complete (⊢d-app₁ ⊢e ⊢e₁) A~j = ⊢a-app (subsumption-0 (complete ⊢e ~Z) (≈hole (complete ⊢e₁ ~∞) (complete-≈ A~j)))
complete (⊢d-app₂ ⊢e ⊢e₁) A~j = ⊢a-app (complete ⊢e (~S⇒ (complete ⊢e₁ ~Z) A~j))
complete (⊢d-app₃ ⊢e ⊢e₁) A~j = ⊢a-app (complete ⊢e (~∞⇒ (complete ⊢e₁ ~Z) A~j))
complete (⊢d-sub ⊢e _) A~j = subsumption-0 (complete ⊢e ~Z) (complete-≈ A~j)
