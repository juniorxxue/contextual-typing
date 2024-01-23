module Record.Completeness where

open import Record.Prelude hiding (_≤?_) renaming (_≤_ to _≤n_)
open import Record.Common
open import Record.Decl
open import Record.Algo
open import Record.Algo.Properties

infix 3 _⊢_~_
infix 3 _⊢_~j_

data _⊢_~_ : Context → Counter × Type → Hint → Set
data _⊢_~j_ : Context → CCounter × Type → Hint → Set

data _⊢_~_ where

  ~j : ∀ {Γ j A H}
    → Γ ⊢ ⟨ j , A ⟩ ~j H
    → Γ ⊢ ⟨ ♭ j , A ⟩ ~ H

  ~S⇒ : ∀ {Γ i A B H e}
    → Γ ⊢a □ ⇛ e ⇛ A
    → Γ ⊢ ⟨ i , B ⟩ ~ H
    → Γ ⊢ ⟨ S⇒ i , A ⇒ B ⟩ ~ (⟦ e ⟧⇒ H)
    
data _⊢_~j_ where

  ~Z : ∀ {Γ A}
    → Γ ⊢ ⟨ Z , A ⟩ ~j □

  ~∞ : ∀ {Γ A}
    → Γ ⊢ ⟨ ∞ , A ⟩ ~j (τ A)

  ~S⇐ : ∀ {Γ j A B e H}
    → Γ ⊢a τ A ⇛ e ⇛ A
    → Γ ⊢ ⟨ j , B ⟩ ~j H
    → Γ ⊢ ⟨ S⇐ j , A ⇒ B ⟩ ~j (⟦ e ⟧⇒ H)

  ~Sl : ∀ {Γ j A l H}
    → Γ ⊢ ⟨ j , A ⟩ ~j H
    → Γ ⊢ ⟨ Sl j , τ⟦ l ↦ A ⟧ ⟩ ~j (⌊ l ⌋⇒ H)

complete : ∀ {Γ H i e A}
  → Γ ⊢d i # e ⦂ A
  → Γ ⊢ ⟨ i , A ⟩ ~ H
  → Γ ⊢a H ⇛ e ⇛ A
complete ⊢d-int (~j ~Z) = ⊢a-lit
complete (⊢d-var x) (~j ~Z) = ⊢a-var x
complete (⊢d-ann ⊢e) (~j ~Z) = ⊢a-ann (complete ⊢e (~j ~∞))
complete (⊢d-lam₁ ⊢e) (~j ~∞) = ⊢a-lam₁ (complete ⊢e (~j ~∞))
complete (⊢d-lam₂ ⊢e) (~S⇒ ⊢e' newH) = ⊢a-lam₂ ⊢e' (complete ⊢e {!!})
complete (⊢d-app⇐ ⊢e ⊢e₁) (~j x) = ⊢a-app (complete ⊢e (~j (~S⇐ (complete ⊢e₁ (~j ~∞)) x)))
complete (⊢d-app⇒ ⊢e ⊢e₁) (~j x) = ⊢a-app (complete ⊢e (~S⇒ (complete ⊢e₁ (~j ~Z)) (~j x)))
complete (⊢d-app⇒ ⊢e ⊢e₁) (~S⇒ x newH) = ⊢a-app (complete ⊢e (~S⇒ (complete ⊢e₁ (~j ~Z)) (~S⇒ x newH)))
complete (⊢d-sub ⊢e x x₁) newH = {!!}
complete (⊢d-& ⊢e ⊢e₁) (~j ~∞) = ⊢a-& (complete ⊢e (~j ~∞)) (complete ⊢e₁ (~j ~∞))
complete (⊢d-rcd x) (~j ~Z) = ⊢a-rcd {!!}
complete (⊢d-prj ⊢e) (~j x) = ⊢a-prj (complete ⊢e (~j (~Sl x)))
