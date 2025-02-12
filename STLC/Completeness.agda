module STLC.Completeness where

open import STLC.Prelude hiding (_≤?_) renaming (_≤_ to _≤n_)
open import STLC.Common
open import STLC.Decl
open import STLC.Algo
open import STLC.Algo.Properties
open import STLC.Properties

infix 3 _⊢_~_

data _⊢_~_ : Env → Counter × Type → Context → Set

data _⊢_~_ where

  ~Z : ∀ {Γ A}
    → Γ ⊢ ⟨ Z , A ⟩ ~ □

  ~∞ : ∀ {Γ A }
    → Γ ⊢ ⟨ ∞ , A ⟩ ~ τ A

  ~S⇒ : ∀ {Γ j A B H e}
    → Γ ⊢ □ ⇒ e ⇒ A
    → Γ ⊢ ⟨ j , B ⟩ ~ H
    → Γ ⊢ ⟨ S j , A `→ B ⟩ ~ ([ e ]↝ H)

~weaken : ∀ {Γ A j B H n n≤l}
  → Γ ⊢ ⟨ j , B ⟩ ~ H
  → Γ ↑ n [ n≤l ] A ⊢ ⟨ j , B ⟩ ~ (H ⇧ n)
~weaken ~Z = ~Z
~weaken ~∞ = ~∞
~weaken (~S⇒ ⊢e j~H) = ~S⇒ (⊢weaken ⊢e) (~weaken j~H)


complete-≈ : ∀ {Γ A j H}
  → Γ ⊢ ⟨ j , A ⟩ ~ H
  → Γ ⊢ A ≈ H
complete-≈ ~Z = ≈□
complete-≈ ~∞ = ≈τ
complete-≈ (~S⇒ ⊢e j~H) = ≈term (subsumption-0 ⊢e ≈τ) (complete-≈ j~H)

complete : ∀ {Γ H j e A}
  → Γ ⊢ j # e ⦂ A
  → Γ ⊢ ⟨ j , A ⟩ ~ H
  → Γ ⊢ H ⇒ e ⇒ A
complete ⊢int ~Z = ⊢lit
complete (⊢var x) ~Z = ⊢var x
complete (⊢ann ⊢e) ~Z = ⊢ann (complete ⊢e ~∞)
complete (⊢lam-∞ x) ~∞ = ⊢lam₁ (complete x ~∞)
complete (⊢lam-n x) (~S⇒ ⊢e A~j) = ⊢lam₂ ⊢e (complete x (~weaken {n≤l = z≤n} A~j))
complete (⊢app₁ ⊢e ⊢e₁) A~j = ⊢app (subsumption-0 (complete ⊢e ~Z) (≈term (complete ⊢e₁ ~∞) (complete-≈ A~j)))
complete (⊢app₂ ⊢e ⊢e₁) A~j = ⊢app (complete ⊢e (~S⇒ (complete ⊢e₁ ~Z) A~j))
complete (⊢sub ⊢e neq) A~j = subsumption-0 (complete ⊢e ~Z) (complete-≈ A~j)

-- corollaries
complete-inf : ∀ {Γ e A}
  → Γ ⊢ Z # e ⦂ A
  → Γ ⊢ □ ⇒ e ⇒ A
complete-inf ⊢e = complete ⊢e ~Z


complete-chk : ∀ {Γ e A}
  → Γ ⊢ ∞ # e ⦂ A
  → Γ ⊢ τ A ⇒ e ⇒ A
complete-chk ⊢e = complete ⊢e ~∞
