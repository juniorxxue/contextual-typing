module Record.Completeness where

open import Record.Prelude hiding (_≤?_) renaming (_≤_ to _≤n_)
open import Record.Common
open import Record.Decl
open import Record.Properties
open import Record.Algo
open import Record.Algo.Properties

infix 3 _⊢_~_
infix 3 _⊢_~j_

data _⊢_~_ : Env → Counter × Type → Context → Set
data _⊢_~j_ : Env → CCounter × Type → Context → Set

data _⊢_~_ where

  ~j : ∀ {Γ j A H}
    → Γ ⊢ ⟨ j , A ⟩ ~j H
    → Γ ⊢ ⟨ ♭ j , A ⟩ ~ H

  ~S⇒ : ∀ {Γ i A B H e}
    → Γ ⊢ □ ⇒ e ⇒ A
    → Γ ⊢ ⟨ i , B ⟩ ~ H
    → Γ ⊢ ⟨ S⇒ i , A `→ B ⟩ ~ (⟦ e ⟧⇒ H)
    
data _⊢_~j_ where

  ~Z : ∀ {Γ A}
    → Γ ⊢ ⟨ Z , A ⟩ ~j □

  ~∞ : ∀ {Γ A}
    → Γ ⊢ ⟨ ∞ , A ⟩ ~j (τ A)

  ~S⇐ : ∀ {Γ j A B e H}
    → Γ ⊢ τ A ⇒ e ⇒ A
    → Γ ⊢ ⟨ j , B ⟩ ~j H
    → Γ ⊢ ⟨ S⇐ j , A `→ B ⟩ ~j (⟦ e ⟧⇒ H)

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
~weaken (~S⇒ x i~H) = ~S⇒ (⊢weaken x) (~weaken i~H)

~jweaken ~Z = ~Z
~jweaken ~∞ = ~∞
~jweaken (~S⇐ x j~H) = ~S⇐ (⊢weaken x) (~jweaken j~H)
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
  → Γ ⊢ i # e ⦂ A
  → Γ ⊢ ⟨ i , A ⟩ ~ H
  → Γ ⊢ H ⇒ e ⇒ A

complete-≤ : ∀ {Γ H i A B}
  → B ≤ i # A
  → Γ ⊢ ⟨ i , A ⟩ ~ H
  → Γ ⊢ B ≤ H ⇝ A

complete-r : ∀ {Γ rs A}
  → Γ ⊢r ♭ Z # rs ⦂ A
  → Γ ⊢r □ ⇒ rs ⇒ A
complete-r ⊢r-nil = ⊢nil
complete-r (⊢r-one x) = ⊢one (complete x (~j ~Z))
complete-r (⊢r-cons x ⊢r neq) = ⊢cons (complete x (~j ~Z)) (complete-r ⊢r) neq
  
complete ⊢c (~j ~Z) = ⊢c
complete (⊢var x) (~j ~Z) = ⊢var x
complete (⊢ann ⊢e) (~j ~Z) = ⊢ann (complete ⊢e (~j ~∞))
complete (⊢lam₁ ⊢e) (~j ~∞) = ⊢lam₁ (complete ⊢e (~j ~∞))
complete (⊢lam₂ ⊢e) (~S⇒ ⊢e' newH) = ⊢lam₂ ⊢e' (complete ⊢e (~weaken {n≤l = z≤n} newH))
complete (⊢app⇐ ⊢e ⊢e₁) (~j x) = ⊢app (complete ⊢e (~j (~S⇐ (complete ⊢e₁ (~j ~∞)) x)))
complete (⊢app⇒ ⊢e ⊢e₁) (~j x) = ⊢app (complete ⊢e (~S⇒ (complete ⊢e₁ (~j ~Z)) (~j x)))
complete (⊢app⇒ ⊢e ⊢e₁) (~S⇒ x newH) = ⊢app (complete ⊢e (~S⇒ (complete ⊢e₁ (~j ~Z)) (~S⇒ x newH)))
complete (⊢sub ⊢e x x₁) newH = subsumption-0 (complete ⊢e (~j ~Z)) (complete-≤ x newH )
complete (⊢rcd x) (~j ~Z) = ⊢rcd (complete-r x)
complete (⊢prj ⊢e) (~j x) = ⊢prj (complete ⊢e (~j (~Sl x)))

complete-≤ ≤Z (~j ~Z) = ≤□
complete-≤ ≤int∞ (~j ~∞) = ≤int
complete-≤ ≤float∞ (~j ~∞) = ≤float
complete-≤ ≤top (~j ~∞) = ≤top
complete-≤ (≤arr-∞ B≤A B≤A₁) (~j ~∞) = ≤arr (complete-≤ B≤A (~j ~∞)) (complete-≤ B≤A₁ (~j ~∞))
complete-≤ (≤rcd∞ B≤A) (~j ~∞) = ≤rcd (complete-≤ B≤A (~j ~∞))
complete-≤ (≤arr-S⇐ B≤A B≤A₁) (~j (~S⇐ x x₁)) = ≤hint x (complete-≤ B≤A₁ (~j x₁))
complete-≤ (≤arr-S⇒ x x₃) (~S⇒ x₁ x₂) = ≤hint (subsumption-0 x₁ ≤refl) (complete-≤ x₃ x₂)
complete-≤ (≤rcd-Sl B≤A) (~j (~Sl x)) = ≤hint-l (complete-≤ B≤A (~j x))
complete-≤ (≤and₁ B≤A x) newH = ≤and-l (complete-≤ B≤A newH) (H≢□→i≢Z x newH)
complete-≤ (≤and₂ B≤A x) newH = ≤and-r (complete-≤ B≤A newH) (H≢□→i≢Z x newH)
complete-≤ (≤and B≤A B≤A₁) (~j ~∞) = ≤and (complete-≤ B≤A (~j ~∞)) (complete-≤ B≤A₁ (~j ~∞))

complete-inf : ∀ {Γ e A}
  → Γ ⊢ ♭ Z # e ⦂ A
  → Γ ⊢ □ ⇒ e ⇒ A
complete-inf ⊢e = complete ⊢e (~j ~Z)

complete-chk : ∀ {Γ e A}
  → Γ ⊢ ♭ ∞ # e ⦂ A
  → Γ ⊢ τ A ⇒ e ⇒ A
complete-chk ⊢e = complete ⊢e (~j ~∞)
