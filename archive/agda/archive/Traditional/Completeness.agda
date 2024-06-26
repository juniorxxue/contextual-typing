module Traditional.Completeness where

open import Traditional.Prelude hiding (_≤?_) renaming (_≤_ to _≤n_)
open import Traditional.Common
open import Traditional.Decl
open import Traditional.Algo
open import Traditional.Algo.Properties


----------------------------------------------------------------------
--+                                                                +--
--+                          Completeness                          +--
--+                                                                +--
----------------------------------------------------------------------
infix 4 _⊩a_⇛_

data _⊩a_⇛_ : Context → List Term → List Type → Set where

  ⊩a-none : ∀ {Γ}
    → Γ ⊩a [] ⇛ []

  ⊩a-cons : ∀ {Γ es As e A}
    → Γ ⊩a es ⇛ As
    → Γ ⊢a □ ⇛ e ⇛ A
    → Γ ⊩a (e ∷ es) ⇛ (A ∷ As)

⊩a-weaken : ∀ {Γ es As A}
  → Γ ⊩a es ⇛ As
  → Γ , A ⊩a (map (_↑ 0) es) ⇛ As
⊩a-weaken ⊩a-none = ⊩a-none
⊩a-weaken (⊩a-cons ⊩es ⊢e) = ⊩a-cons (⊩a-weaken ⊩es) (⊢a-weaken-0-0 ⊢e)
  where
    ⊢a-weaken-0-0 : ∀ {Γ e A B}
      → Γ ⊢a □ ⇛ e ⇛ A
      → Γ , B ⊢a □ ⇛ e ↑ 0 ⇛ A
    ⊢a-weaken-0-0 ⊢e = ⊢a-weaken {n≤l = z≤n} ⊢e
    
infix 4 _⇴_≗_

data _⇴_≗_ : List Term → Hint → Hint → Set where

  cht-none-□ :
      [] ⇴ □ ≗ □

  cht-none-τ : ∀ {A}
    → [] ⇴ τ A ≗ (τ A)

  cht-cons : ∀ {e es H H'}
    → es ⇴ H ≗ H'
    → (e ∷ es) ⇴ H ≗ ⟦ e ⟧⇒ H'


≗-shift : ∀ {es H H'}
  → es ⇴ H ≗ H'
  → map (_↑ 0) es ⇴ H ⇧ 0 ≗ H' ⇧ 0
≗-shift cht-none-□ = cht-none-□
≗-shift cht-none-τ = cht-none-τ
≗-shift (cht-cons newH) = cht-cons (≗-shift newH)

infix 4 _↪_⟦_,_,_⟧

data _↪_⟦_,_,_⟧ : Type → Counter → List Type → Type → Counter → Set where

  n-z : ∀ {A}
    → A ↪ Z ⟦ [] , A , Z ⟧

  n-∞ : ∀ {A}
    → A ↪ ∞ ⟦ [] , A , ∞ ⟧

  n-s : ∀ {A B T j Bs j'}
    → B ↪ j ⟦ Bs , T , j' ⟧
    → (A ⇒ B) ↪ (S j) ⟦ A ∷ Bs , T , j' ⟧

complete-wf-z : ∀ {Γ A H es As j T}
  → A ↪ j ⟦ As , T , Z ⟧
  → Γ ⊩a es ⇛ As
  → es ⇴ □ ≗ H
  → Γ ⊢a A ≈ H

complete-wf-∞ : ∀ {Γ A H es As j T}
  → A ↪ j ⟦ As , T , ∞ ⟧
  → Γ ⊩a es ⇛ As
  → es ⇴ τ T ≗ H
  → Γ ⊢a A ≈ H

complete-chk : ∀ {Γ e A j es As T H}
  → Γ ⊢d j # e ⦂ A
  → A ↪ j ⟦ As , T , ∞ ⟧
  → Γ ⊩a es ⇛ As
  → es ⇴ τ T ≗ H
  → Γ ⊢a H ⇛ e ⇛ A

complete-inf : ∀ {Γ e A j es As T H}
  → Γ ⊢d j # e ⦂ A
  → A ↪ j ⟦ As , T , Z ⟧
  → Γ ⊩a es ⇛ As
  → es ⇴ □ ≗ H
  → Γ ⊢a H ⇛ e ⇛ A

complete-wf-z n-z ⊩a-none cht-none-□ = ≈□
complete-wf-z (n-s x) (⊩a-cons x₁ x₃) (cht-cons x₂) = ≈hole (subsumption-0 x₃ ≈τ) (complete-wf-z x x₁ x₂)

complete-wf-∞ n-∞ ⊩a-none cht-none-τ = ≈τ
complete-wf-∞ (n-s Aj) (⊩a-cons ⊢es x) (cht-cons newH) = ≈hole (subsumption-0 x ≈τ) (complete-wf-∞ Aj ⊢es newH)

complete-chk (⊢d-lam-∞ ⊢e) n-∞ ⊩a-none cht-none-τ = ⊢a-lam₁ (complete-chk ⊢e n-∞ ⊩a-none cht-none-τ)

complete-chk (⊢d-app₂ ⊢e ⊢e₁) Aj ⊩es newH =
  ⊢a-app (complete-chk ⊢e (n-s Aj) (⊩a-cons ⊩es (complete-inf ⊢e₁ n-z ⊩a-none cht-none-□)) (cht-cons newH))
  
complete-chk (⊢d-sub ⊢e x) Aj ⊩es newH = subsumption-0 (complete-inf ⊢e n-z ⊩a-none cht-none-□) (complete-wf-∞ Aj ⊩es newH)

-- trivial cases
complete-inf ⊢d-int n-z ⊩a-none cht-none-□ = ⊢a-lit
complete-inf (⊢d-var x) n-z ⊩a-none cht-none-□ = ⊢a-var x
complete-inf (⊢d-ann ⊢e) n-z ⊩a-none cht-none-□ = ⊢a-ann (complete-chk ⊢e n-∞ ⊩a-none cht-none-τ)


complete-inf (⊢d-app₁ ⊢e ⊢e₁) n-z ⊩a-none cht-none-□ =
  ⊢a-app (subsumption-0 (complete-inf ⊢e n-z ⊩a-none cht-none-□) (≈hole (complete-chk ⊢e₁ n-∞ ⊩a-none cht-none-τ) ≈□))
  
complete-inf (⊢d-app₂ ⊢e ⊢e₁) Aj ⊩es newH =
  ⊢a-app (complete-inf ⊢e (n-s Aj) (⊩a-cons ⊩es (complete-inf ⊢e₁ n-z ⊩a-none cht-none-□)) (cht-cons newH))
  
complete-inf (⊢d-sub ⊢e j≢Z) Aj ⊩es newH = subsumption-0 (complete-inf ⊢e n-z ⊩a-none cht-none-□) (complete-wf-z Aj ⊩es newH)

-- corollaries

complete-inf-0 : ∀ {Γ e A}
  → Γ ⊢d Z # e ⦂ A
  → Γ ⊢a □ ⇛ e ⇛ A
complete-inf-0 ⊢e = complete-inf ⊢e n-z ⊩a-none cht-none-□

complete-chk-0 : ∀ {Γ e A}
  → Γ ⊢d ∞ # e ⦂ A
  → Γ ⊢a τ A ⇛ e ⇛ A
complete-chk-0 ⊢e = complete-chk ⊢e n-∞ ⊩a-none cht-none-τ
