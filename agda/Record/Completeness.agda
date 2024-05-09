module Record.Completeness where

open import Record.Prelude hiding (_≤?_) renaming (_≤_ to _≤n_)
open import Record.Common
open import Record.Decl
open import Record.Properties
open import Record.Algo
open import Record.Algo.Properties

infix 3 _⊢_~_

data _⊢_~_ : Context → Counter × Type → Hint → Set where

  ~S : ∀ {Γ i A B H e}
    → Γ ⊢a □ ⇛ e ⇛ A
    → Γ ⊢ ⟨ i , B ⟩ ~ H
    → Γ ⊢ ⟨ S i , A ⇒ B ⟩ ~ (⟦ e ⟧⇒ H)    

  ~Z : ∀ {Γ A}
    → Γ ⊢ ⟨ Z , A ⟩ ~ □

  ~∞ : ∀ {Γ A}
    → Γ ⊢ ⟨ ∞ , A ⟩ ~ (τ A)

~weaken : ∀ {Γ A i B H n n≤l}
  → Γ ⊢ ⟨ i , B ⟩ ~ H
  → (Γ ↑ n [ n≤l ] A) ⊢ ⟨ i , B ⟩ ~ (H ⇧ n)
  
complete : ∀ {Γ H i e A}
  → Γ ⊢d i # e ⦂ A
  → Γ ⊢ ⟨ i , A ⟩ ~ H
  → Γ ⊢a H ⇛ e ⇛ A

complete-≤ : ∀ {Γ H i A B}
  → B ≤d A
  → Γ ⊢ ⟨ i , A ⟩ ~ H
  → Γ ⊢a B ≤ H ⇝ A

complete-r : ∀ {Γ rs A}
  → Γ ⊢r Z # rs ⦂ A
  → Γ ⊢r □ ⇛ rs ⇛ A
complete-r ⊢r-nil = ⊢a-nil
complete-r (⊢r-one x) = ⊢a-one (complete x ~Z)
complete-r (⊢r-cons x ⊢r neq) = ⊢a-cons (complete x ~Z) (complete-r ⊢r) neq
  
complete ⊢d-c ~Z = ⊢a-c
complete (⊢d-var x) ~Z = ⊢a-var x
complete (⊢d-ann ⊢e) ~Z = ⊢a-ann (complete ⊢e ~∞)
complete (⊢d-lam₁ ⊢e) ~∞ = ⊢a-lam₁ (complete ⊢e ~∞)
complete (⊢d-lam₂ ⊢e) (~S x j~H) = ⊢a-lam₂ x (complete ⊢e {!!}) -- weaken
complete (⊢d-app⇐ ⊢e ⊢e₁) ~Z = ⊢a-app (subsumption (complete ⊢e ~Z) none-□ ch-none (≤a-hint (complete ⊢e₁ ~∞) ≤a-□))
complete (⊢d-app⇒ ⊢e ⊢e₁) j~H = ⊢a-app (complete ⊢e (~S (complete ⊢e₁ ~Z) j~H))
complete (⊢d-sub ⊢e x x₁) j~H = {!!}
complete (⊢d-rcd x) j~H = {!!}
complete (⊢d-prj ⊢e) j~H = {!!}

complete-≤ s j~H = {!!}


complete-inf : ∀ {Γ e A}
  → Γ ⊢d Z # e ⦂ A
  → Γ ⊢a □ ⇛ e ⇛ A
complete-inf ⊢e = complete ⊢e ~Z


complete-chk : ∀ {Γ e A}
  → Γ ⊢d ∞ # e ⦂ A
  → Γ ⊢a τ A ⇛ e ⇛ A
complete-chk ⊢e = complete ⊢e ~∞
