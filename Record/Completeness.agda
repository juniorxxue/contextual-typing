module Record.Completeness where

open import Record.Prelude hiding (_≤?_) renaming (_≤_ to _≤n_)
open import Record.Common
open import Record.Decl
open import Record.Properties
open import Record.Algo
open import Record.Algo.Properties

-- mapping <counter, type> to a context
infix 3 _⊢_~_
infix 3 _⊢_~j_

data _⊢_~_ : Env → Counter × Type → Context → Set
data _⊢_~j_ : Env → CCounter × Type → Context → Set

data _⊢_~_ where

  ~j : ∀ {Γ j A Σ}
    → Γ ⊢ ⟨ j , A ⟩ ~j Σ
    → Γ ⊢ ⟨ ♭ j , A ⟩ ~ Σ

  ~S⇒ : ∀ {Γ i A B Σ e}
    → Γ ⊢ □ ⇒ e ⇒ A
    → Γ ⊢ ⟨ i , B ⟩ ~ Σ
    → Γ ⊢ ⟨ S⇒ i , A `→ B ⟩ ~ (⟦ e ⟧⇒ Σ)

data _⊢_~j_ where

  ~Z : ∀ {Γ A}
    → Γ ⊢ ⟨ Z , A ⟩ ~j □

  ~∞ : ∀ {Γ A}
    → Γ ⊢ ⟨ ∞ , A ⟩ ~j (τ A)

  ~S⇐ : ∀ {Γ j A B e Σ}
    → Γ ⊢ τ A ⇒ e ⇒ A
    → Γ ⊢ ⟨ j , B ⟩ ~j Σ
    → Γ ⊢ ⟨ S⇐ j , A `→ B ⟩ ~j (⟦ e ⟧⇒ Σ)

  ~Sl : ∀ {Γ j A l Σ}
    → Γ ⊢ ⟨ j , A ⟩ ~j Σ
    → Γ ⊢ ⟨ Sl j , τ⟦ l ↦ A ⟧ ⟩ ~j (⌊ l ⌋⇒ Σ)

~weaken : ∀ {Γ A i B Σ n n≤l}
  → Γ ⊢ ⟨ i , B ⟩ ~ Σ
  → (Γ ↑ n [ n≤l ] A) ⊢ ⟨ i , B ⟩ ~ (Σ ⇧ n)

~jweaken : ∀ {Γ A j B Σ n n≤l}
  → Γ ⊢ ⟨ j , B ⟩ ~j Σ
  → (Γ ↑ n [ n≤l ] A) ⊢ ⟨ j , B ⟩ ~j (Σ ⇧ n)

~weaken (~j x) = ~j (~jweaken x)
~weaken (~S⇒ x i~Σ) = ~S⇒ (⊢weaken x) (~weaken i~Σ)

~jweaken ~Z = ~Z
~jweaken ~∞ = ~∞
~jweaken (~S⇐ x j~Σ) = ~S⇐ (⊢weaken x) (~jweaken j~Σ)
~jweaken (~Sl j~Σ) = ~Sl (~jweaken j~Σ)

Σ≢□→i≢Z : ∀ {Γ Σ i A}
  → i ≢ ♭ Z
  → Γ ⊢ ⟨ i , A ⟩ ~ Σ
  → Σ ≢ □
Σ≢□→i≢Z {i = ♭ Z} i≢Z i~Σ = ⊥-elim (i≢Z refl)
Σ≢□→i≢Z {i = ♭ ∞} i≢Z (~j ~∞) = λ ()
Σ≢□→i≢Z {i = ♭ (S⇐ x)} i≢Z (~j (~S⇐ x₁ x₂)) = λ ()
Σ≢□→i≢Z {i = ♭ (Sl x)} i≢Z (~j (~Sl x₁)) = λ ()
Σ≢□→i≢Z {i = S⇒ i} i≢Z (~S⇒ x i~Σ) = λ ()


complete-≤ : ∀ {Γ Σ i A B}
  → B ≤ i # A
  → Γ ⊢ ⟨ i , A ⟩ ~ Σ
  → Γ ⊢ B ≤ Σ ⇝ A
complete-≤ ≤Z (~j ~Z) = ≤□
complete-≤ ≤int∞ (~j ~∞) = ≤int
complete-≤ ≤float∞ (~j ~∞) = ≤float
complete-≤ ≤top (~j ~∞) = ≤top
complete-≤ (≤arr-∞ B≤A B≤A₁) (~j ~∞) = ≤arr (complete-≤ B≤A (~j ~∞)) (complete-≤ B≤A₁ (~j ~∞))
complete-≤ (≤rcd∞ B≤A) (~j ~∞) = ≤rcd (complete-≤ B≤A (~j ~∞))
complete-≤ (≤arr-S⇐ B≤A B≤A₁) (~j (~S⇐ x x₁)) = ≤hint x (complete-≤ B≤A₁ (~j x₁))
complete-≤ (≤arr-S⇒ x x₃) (~S⇒ x₁ x₂) = ≤hint (subsumption-0 x₁ ≤refl) (complete-≤ x₃ x₂)
complete-≤ (≤rcd-Sl B≤A) (~j (~Sl x)) = ≤hint-l (complete-≤ B≤A (~j x))
complete-≤ (≤and₁ B≤A x) newΣ = ≤and-l (complete-≤ B≤A newΣ) (Σ≢□→i≢Z x newΣ)
complete-≤ (≤and₂ B≤A x) newΣ = ≤and-r (complete-≤ B≤A newΣ) (Σ≢□→i≢Z x newΣ)
complete-≤ (≤and B≤A B≤A₁) (~j ~∞) = ≤and (complete-≤ B≤A (~j ~∞)) (complete-≤ B≤A₁ (~j ~∞))

-- the most general form of completeness theorem
complete : ∀ {Γ Σ i e A}
  → Γ ⊢ i # e ⦂ A
  → Γ ⊢ ⟨ i , A ⟩ ~ Σ
  → Γ ⊢ Σ ⇒ e ⇒ A

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
complete (⊢lam₂ ⊢e) (~S⇒ ⊢e' newΣ) = ⊢lam₂ ⊢e' (complete ⊢e (~weaken {n≤l = z≤n} newΣ))
complete (⊢app⇐ ⊢e ⊢e₁) (~j x) = ⊢app (complete ⊢e (~j (~S⇐ (complete ⊢e₁ (~j ~∞)) x)))
complete (⊢app⇒ ⊢e ⊢e₁) (~j x) = ⊢app (complete ⊢e (~S⇒ (complete ⊢e₁ (~j ~Z)) (~j x)))
complete (⊢app⇒ ⊢e ⊢e₁) (~S⇒ x newΣ) = ⊢app (complete ⊢e (~S⇒ (complete ⊢e₁ (~j ~Z)) (~S⇒ x newΣ)))
complete (⊢sub ⊢e x x₁) newΣ = subsumption-0 (complete ⊢e (~j ~Z)) (complete-≤ x newΣ )
complete (⊢rcd x) (~j ~Z) = ⊢rcd (complete-r x)
complete (⊢prj ⊢e) (~j x) = ⊢prj (complete ⊢e (~j (~Sl x)))

-- two corollaries
complete-inf : ∀ {Γ e A}
  → Γ ⊢ ♭ Z # e ⦂ A
  → Γ ⊢ □ ⇒ e ⇒ A
complete-inf ⊢e = complete ⊢e (~j ~Z)

complete-chk : ∀ {Γ e A}
  → Γ ⊢ ♭ ∞ # e ⦂ A
  → Γ ⊢ τ A ⇒ e ⇒ A
complete-chk ⊢e = complete ⊢e (~j ~∞)
