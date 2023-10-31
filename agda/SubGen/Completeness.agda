module SubGen.Completeness where

open import SubGen.Prelude hiding (_≤?_) renaming (_≤_ to _≤n_)
open import SubGen.Common
open import SubGen.Decl
open import SubGen.Algo
open import SubGen.Algo.Properties

infix 4 _⊩a_⇛_
infix 4 _⊩a_⇚_

data _⊩a_⇛_ : Context → List Term → List Type → Set where

  ⊩a-none : ∀ {Γ}
    → Γ ⊩a [] ⇛ []

  ⊩a-cons : ∀ {Γ es As e A}
    → Γ ⊩a es ⇛ As
    → Γ ⊢a □ ⇛ e ⇛ A
    → Γ ⊩a (e ∷ es) ⇛ (A ∷ As)

data _⊩a_⇚_ : Context → List Term → List Type → Set where

  ⊩a-none : ∀ {Γ}
    → Γ ⊩a [] ⇚ []

  ⊩a-cons : ∀ {Γ es As e A}
    → Γ ⊩a es ⇚ As
    → Γ ⊢a τ A ⇛ e ⇛ A
    → Γ ⊩a (e ∷ es) ⇚ (A ∷ As)

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

infix 4 _↪_❪_,_,_❫

data _↪_❪_,_,_❫ : Type → Counter → List Type → Type → Counter → Set where

  n-z : ∀ {A}
    → A ↪ Z ❪ [] , A , Z ❫

  n-∞ : ∀ {A}
    → A ↪ ∞ ❪ [] , A , ∞ ❫

  n-s : ∀ {A B T j Bs j'}
    → B ↪ j ❪ Bs , T , j' ❫
    → (A ⇒ B) ↪ (S j) ❪ A ∷ Bs , T , j' ❫

complete-≤-Z : ∀ {Γ A H es As j T B}
  → B ≤d j # A
  → A ↪ j ❪ As , T , Z ❫
  → Γ ⊩a es ⇛ As
  → es ⇴ □ ≗ H
  → Γ ⊢a B ≤ H ⇝ A

complete-≤-∞ : ∀ {Γ A H es As j T B}
  → B ≤d j # A
  → A ↪ j ❪ As , T , ∞ ❫
  → Γ ⊩a es ⇛ As
  → es ⇴ τ T ≗ H
  → Γ ⊢a B ≤ H ⇝ A

complete-≤-∞-0 : ∀ {Γ A B}
  → B ≤d ∞ # A
  → Γ ⊢a B ≤ τ A ⇝ A
complete-≤-∞-0 B≤A = complete-≤-∞ B≤A n-∞ ⊩a-none cht-none-τ  

complete-chk : ∀ {Γ e A j es As T H}
  → Γ ⊢d j # e ⦂ A
  → A ↪ j ❪ As , T , ∞ ❫
  → Γ ⊩a es ⇛ As
  → es ⇴ τ T ≗ H
  → Γ ⊢a H ⇛ e ⇛ A

complete-inf : ∀ {Γ e A j es As T H}
  → Γ ⊢d j # e ⦂ A
  → A ↪ j ❪ As , T , Z ❫
  → Γ ⊩a es ⇛ As
  → es ⇴ □ ≗ H
  → Γ ⊢a H ⇛ e ⇛ A

complete-chk-0 : ∀ {Γ e A}
  → Γ ⊢d ∞ # e ⦂ A
  → Γ ⊢a τ A ⇛ e ⇛ A
complete-chk-0 ⊢e = complete-chk ⊢e n-∞ ⊩a-none cht-none-τ

complete-inf-0 : ∀ {Γ e A}
  → Γ ⊢d Z # e ⦂ A
  → Γ ⊢a □ ⇛ e ⇛ A
complete-inf-0 ⊢e = complete-inf ⊢e n-z ⊩a-none cht-none-□  

complete-chk (⊢d-lam₁ ⊢e) n-∞ ⊩a-none cht-none-τ = ⊢a-lam₁ (complete-chk-0 ⊢e)
complete-chk (⊢d-lam₂ ⊢e) (n-s Aj) (⊩a-cons ⊢es x) (cht-cons newH) = ⊢a-lam₂ x (complete-chk ⊢e Aj (⊩a-weaken ⊢es) (≗-shift newH))
complete-chk (⊢d-app₂ ⊢e ⊢e₁) Aj ⊢es newH = ⊢a-app (complete-chk ⊢e (n-s Aj) (⊩a-cons ⊢es (complete-inf-0 ⊢e₁)) (cht-cons newH))
complete-chk (⊢d-sub ⊢e x x₁) Aj ⊢es newH = subsumption-0 (complete-inf-0 ⊢e) (complete-≤-∞ x Aj ⊢es newH)
complete-chk (⊢d-and-& ⊢e ⊢e₁) n-∞ ⊩a-none cht-none-τ = ⊢a-& (complete-chk ⊢e n-∞ ⊩a-none cht-none-τ)
                                                             (complete-chk ⊢e₁ n-∞ ⊩a-none cht-none-τ)

complete-inf ⊢d-int n-z ⊩a-none cht-none-□ = ⊢a-lit
complete-inf (⊢d-var x) n-z ⊩a-none cht-none-□ = ⊢a-var x
complete-inf (⊢d-ann ⊢e) n-z ⊩a-none cht-none-□ = ⊢a-ann (complete-chk ⊢e n-∞ ⊩a-none cht-none-τ)
complete-inf (⊢d-lam₂ ⊢e) (n-s Aj) (⊩a-cons ⊢es x) (cht-cons newH) = ⊢a-lam₂ x (complete-inf ⊢e Aj (⊩a-weaken ⊢es) (≗-shift newH))
complete-inf (⊢d-app₁ ⊢e ⊢e₁) n-z ⊩a-none cht-none-□ = ⊢a-app (subsumption-0 (complete-inf-0 ⊢e) (≤a-hint (complete-chk-0 ⊢e₁) ≤a-□))
complete-inf (⊢d-app₂ ⊢e ⊢e₁) Aj ⊢es newH = ⊢a-app (complete-inf ⊢e (n-s Aj) (⊩a-cons ⊢es (complete-inf-0 ⊢e₁)) (cht-cons newH))
complete-inf (⊢d-sub ⊢e x x₁) Aj ⊢es newH = subsumption-0 (complete-inf-0 ⊢e) (complete-≤-Z x Aj ⊢es newH)

complete-≤-Z ≤d-Z n-z ⊩a-none cht-none-□ = ≤a-□
complete-≤-Z (≤d-arr-S B≤A B≤A₁) (n-s Aj) (⊩a-cons ⊢es x) (cht-cons newH) = ≤a-hint (subsumption-0 x ≤a-refl) (complete-≤-Z B≤A₁ Aj ⊢es newH)
complete-≤-Z (≤d-and₁ B≤A) Aj ⊢es newH = ≤a-and-l (complete-≤-Z B≤A Aj ⊢es newH)
complete-≤-Z (≤d-and₂ B≤A) Aj ⊢es newH = ≤a-and-r (complete-≤-Z B≤A Aj ⊢es newH)

complete-≤-∞ ≤d-int∞ n-∞ ⊩a-none cht-none-τ = ≤a-int
complete-≤-∞ ≤d-base∞ n-∞ ⊩a-none cht-none-τ = ≤a-base
complete-≤-∞ ≤d-top n-∞ ⊩a-none cht-none-τ = ≤a-top
complete-≤-∞ (≤d-arr-∞ B≤A B≤A₁) n-∞ ⊩a-none cht-none-τ = ≤a-arr (complete-≤-∞-0 B≤A) (complete-≤-∞-0 B≤A₁)
complete-≤-∞ (≤d-arr-S B≤A B≤A₁) (n-s Aj) (⊩a-cons ⊢es x) (cht-cons newH) = ≤a-hint (subsumption-0 x ≤a-refl) (complete-≤-∞ B≤A₁ Aj ⊢es newH)
complete-≤-∞ (≤d-and₁ B≤A) Aj ⊢es newH = ≤a-and-l (complete-≤-∞ B≤A Aj ⊢es newH)
complete-≤-∞ (≤d-and₂ B≤A) Aj ⊢es newH = ≤a-and-r (complete-≤-∞ B≤A Aj ⊢es newH)
complete-≤-∞ (≤d-and B≤A B≤A₁) n-∞ ⊩a-none cht-none-τ = ≤a-and (complete-≤-∞ B≤A n-∞ ⊩a-none cht-none-τ)
                                                               (complete-≤-∞ B≤A₁ n-∞ ⊩a-none cht-none-τ)

-- subsumption-0 (complete-inf-0 ⊢e) {!!}
-- (complete-≤ x Aj ⊢es newH)
