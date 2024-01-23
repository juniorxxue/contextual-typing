module Record.Completeness where

open import Record.Prelude hiding (_≤?_) renaming (_≤_ to _≤n_)
open import Record.Common
open import Record.Decl
open import Record.Properties
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

~weaken : ∀ {Γ A i B H n n≤l}
  → Γ ⊢ ⟨ i , B ⟩ ~ H
  → (Γ ↑ n [ n≤l ] A) ⊢ ⟨ i , B ⟩ ~ (H ⇧ n)
  
~jweaken : ∀ {Γ A j B H n n≤l}
  → Γ ⊢ ⟨ j , B ⟩ ~j H
  → (Γ ↑ n [ n≤l ] A) ⊢ ⟨ j , B ⟩ ~j (H ⇧ n)

~weaken (~j x) = ~j (~jweaken x)
~weaken (~S⇒ x i~H) = ~S⇒ (⊢a-weaken x) (~weaken i~H)

~jweaken ~Z = ~Z
~jweaken ~∞ = ~∞
~jweaken (~S⇐ x j~H) = ~S⇐ (⊢a-weaken x) (~jweaken j~H)
~jweaken (~Sl j~H) = ~Sl (~jweaken j~H)

H≢□→i≢Z : ∀ {Γ H i A}
  → i ≢ ♭ Z
  → Γ ⊢ ⟨ i , A ⟩ ~ H
  → H ≢ □
H≢□→i≢Z {i = ♭ Z} i≢Z i~H = ⊥-elim (i≢Z refl)
H≢□→i≢Z {i = ♭ ∞} i≢Z (~j ~∞) = λ ()
H≢□→i≢Z {i = ♭ (S⇐ x)} i≢Z (~j (~S⇐ x₁ x₂)) = λ ()
H≢□→i≢Z {i = ♭ (Sl x)} i≢Z (~j (~Sl x₁)) = λ ()
H≢□→i≢Z {i = S⇒ i} i≢Z (~S⇒ x i~H) = λ ()

complete : ∀ {Γ H i e A}
  → Γ ⊢d i # e ⦂ A
  → Γ ⊢ ⟨ i , A ⟩ ~ H
  → Γ ⊢a H ⇛ e ⇛ A

complete-≤ : ∀ {Γ H i A B}
  → B ≤d i # A
--  → i ≢ ♭ Z
  → Γ ⊢ ⟨ i , A ⟩ ~ H
  → Γ ⊢a B ≤ H ⇝ A

complete-r : ∀ {Γ rs A}
  → Γ ⊢r ♭ Z # rs ⦂ A
  → Γ ⊢r □ ⇛ rs ⇛ A
complete-r ⊢r-nil = ⊢a-nil
complete-r (⊢r-one x) = ⊢a-one (complete x (~j ~Z))
complete-r (⊢r-cons x ⊢r) = ⊢a-cons (complete x (~j ~Z)) (complete-r ⊢r)
  
complete ⊢d-int (~j ~Z) = ⊢a-lit
complete (⊢d-var x) (~j ~Z) = ⊢a-var x
complete (⊢d-ann ⊢e) (~j ~Z) = ⊢a-ann (complete ⊢e (~j ~∞))
complete (⊢d-lam₁ ⊢e) (~j ~∞) = ⊢a-lam₁ (complete ⊢e (~j ~∞))
complete (⊢d-lam₂ ⊢e) (~S⇒ ⊢e' newH) = ⊢a-lam₂ ⊢e' (complete ⊢e (~weaken {n≤l = z≤n} newH))
complete (⊢d-app⇐ ⊢e ⊢e₁) (~j x) = ⊢a-app (complete ⊢e (~j (~S⇐ (complete ⊢e₁ (~j ~∞)) x)))
complete (⊢d-app⇒ ⊢e ⊢e₁) (~j x) = ⊢a-app (complete ⊢e (~S⇒ (complete ⊢e₁ (~j ~Z)) (~j x)))
complete (⊢d-app⇒ ⊢e ⊢e₁) (~S⇒ x newH) = ⊢a-app (complete ⊢e (~S⇒ (complete ⊢e₁ (~j ~Z)) (~S⇒ x newH)))
complete (⊢d-sub ⊢e x x₁) newH = subsumption-0 (complete ⊢e (~j ~Z)) (complete-≤ x newH )
complete (⊢d-& ⊢e ⊢e₁) (~j ~∞) = ⊢a-& (complete ⊢e (~j ~∞)) (complete ⊢e₁ (~j ~∞))
complete (⊢d-rcd x) (~j ~Z) = ⊢a-rcd (complete-r x)
complete (⊢d-prj ⊢e) (~j x) = ⊢a-prj (complete ⊢e (~j (~Sl x)))

complete-≤ ≤d-Z (~j ~Z) = ≤a-□
complete-≤ ≤d-int∞ (~j ~∞) = ≤a-int
complete-≤ ≤d-base∞ (~j ~∞) = ≤a-base
complete-≤ ≤d-top (~j ~∞) = ≤a-top
complete-≤ (≤d-arr-∞ B≤A B≤A₁) (~j ~∞) = ≤a-arr (complete-≤ B≤A (~j ~∞)) (complete-≤ B≤A₁ (~j ~∞))
complete-≤ (≤d-rcd∞ B≤A) (~j ~∞) = ≤a-rcd (complete-≤ B≤A (~j ~∞))
complete-≤ (≤d-arr-S⇐ B≤A B≤A₁) (~j (~S⇐ x x₁)) = ≤a-hint x (complete-≤ B≤A₁ (~j x₁))
complete-≤ (≤d-rcd-Sl B≤A) (~j (~Sl x)) = ≤a-hint-l (complete-≤ B≤A (~j x))
complete-≤ (≤d-and₁ B≤A x) newH = ≤a-and-l (complete-≤ B≤A newH) (H≢□→i≢Z x newH)
complete-≤ (≤d-and₂ B≤A x) newH = ≤a-and-r (complete-≤ B≤A newH) (H≢□→i≢Z x newH)
complete-≤ (≤d-and B≤A B≤A₁) (~j ~∞) = ≤a-and (complete-≤ B≤A (~j ~∞)) (complete-≤ B≤A₁ (~j ~∞))
