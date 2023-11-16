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

⊩a-weaken⇚ : ∀ {Γ es As A}
  → Γ ⊩a es ⇚ As
  → Γ , A ⊩a (map (_↑ 0) es) ⇚ As
⊩a-weaken⇚ ⊩a-none = ⊩a-none
⊩a-weaken⇚ (⊩a-cons ⊩es ⊢e) = ⊩a-cons (⊩a-weaken⇚ ⊩es) (⊢a-weaken-0-0 ⊢e)
  where
    ⊢a-weaken-0-0 : ∀ {Γ e A B}
      → Γ ⊢a τ A ⇛ e ⇛ A
      → Γ , B ⊢a τ A ⇛ e ↑ 0 ⇛ A
    ⊢a-weaken-0-0 ⊢e = ⊢a-weaken {n≤l = z≤n} ⊢e

infix 4 _↠_↠_≗_

data _↠_↠_≗_ : List Term → List Term → Hint → Hint → Set where

  cht-none : ∀ {H}
    → [] ↠ [] ↠ H ≗ H

  cht-none-r : ∀ {e es H H'}
    → [] ↠ es ↠ H ≗ H'
    → [] ↠ (e ∷ es) ↠ H ≗ ⟦ e ⟧⇒ H'

  cht-cons : ∀ {e es es' H H'}
    → es ↠ es' ↠ H ≗ H'
    → (e ∷ es) ↠ es' ↠ H ≗ ⟦ e ⟧⇒ H'


≗-shift : ∀ {es⇒ es⇐ H H'}
  → es⇒ ↠ es⇐ ↠ H ≗ H'
  → map (_↑ 0) es⇒ ↠ map (_↑ 0) es⇐ ↠ H ⇧ 0 ≗ H' ⇧ 0
≗-shift cht-none = cht-none
≗-shift (cht-none-r newH) = cht-none-r (≗-shift newH)
≗-shift (cht-cons newH) = cht-cons (≗-shift newH)

infix 4 _↪_❪_,_,_,_❫

data _↪_❪_,_,_,_❫ : Type → Counter → List Type → List Type → Type → Counter → Set where

  n-z : ∀ {A}
    → A ↪ Z ❪ [] , [] , A , Z ❫

  n-∞ : ∀ {A}
    → A ↪ ∞ ❪ [] , [] , A , ∞ ❫

  n-s⇒ : ∀ {A B T j B⇒s B⇐s j'}
    → B ↪ j ❪ B⇒s , B⇐s , T , j' ❫
    → (A ⇒ B) ↪ (S⇒ j) ❪ A ∷ B⇒s , B⇐s , T , j' ❫
    
  n-s⇐ : ∀ {A B T j B⇒s B⇐s j'}
    → B ↪ j ❪ B⇒s , B⇐s , T , j' ❫
    → (A ⇒ B) ↪ (S⇐ j) ❪ B⇒s , A ∷ B⇐s , T , j' ❫


complete-≤-Z : ∀ {Γ A H e⇒s e⇐s A⇒s A⇐s j T B}
  → B ≤d j # A
  → A ↪ j ❪ A⇒s , A⇐s , T , Z ❫
  → Γ ⊩a e⇒s ⇛ A⇒s
  → Γ ⊩a e⇐s ⇚ A⇐s
  → e⇒s ↠ e⇐s ↠ □ ≗ H
  → Γ ⊢a B ≤ H ⇝ A

complete-≤-∞ : ∀ {Γ A H e⇒s e⇐s A⇒s A⇐s j T B}
  → B ≤d j # A
  → A ↪ j ❪ A⇒s , A⇐s , T , ∞ ❫
  → Γ ⊩a e⇒s ⇛ A⇒s
  → Γ ⊩a e⇐s ⇚ A⇐s
  → e⇒s ↠ e⇐s ↠ τ T ≗ H
  → Γ ⊢a B ≤ H ⇝ A

complete-≤-∞-0 : ∀ {Γ A B}
  → B ≤d ∞ # A
  → Γ ⊢a B ≤ τ A ⇝ A
complete-≤-∞-0 B≤A = complete-≤-∞ B≤A n-∞ ⊩a-none ⊩a-none cht-none

complete-chk : ∀ {Γ e A j e⇒s e⇐s A⇒s A⇐s T H}
  → Γ ⊢d j # e ⦂ A
  → A ↪ j ❪ A⇒s , A⇐s , T , ∞ ❫
  → Γ ⊩a e⇒s ⇛ A⇒s
  → Γ ⊩a e⇐s ⇚ A⇐s
  → e⇒s ↠ e⇐s ↠ τ T ≗ H
  → Γ ⊢a H ⇛ e ⇛ A

complete-inf : ∀ {Γ e A j e⇒s e⇐s A⇒s A⇐s T H}
  → Γ ⊢d j # e ⦂ A
  → A ↪ j ❪ A⇒s , A⇐s , T , Z ❫
  → Γ ⊩a e⇒s ⇛ A⇒s
  → Γ ⊩a e⇐s ⇚ A⇐s
  → e⇒s ↠ e⇐s ↠ □ ≗ H
  → Γ ⊢a H ⇛ e ⇛ A

complete-chk-0 : ∀ {Γ e A}
  → Γ ⊢d ∞ # e ⦂ A
  → Γ ⊢a τ A ⇛ e ⇛ A
complete-chk-0 ⊢e = complete-chk ⊢e n-∞ ⊩a-none ⊩a-none cht-none

complete-inf-0 : ∀ {Γ e A}
  → Γ ⊢d Z # e ⦂ A
  → Γ ⊢a □ ⇛ e ⇛ A
complete-inf-0 ⊢e = complete-inf ⊢e n-z ⊩a-none ⊩a-none cht-none

complete-chk (⊢d-lam₁ ⊢e) Aj ⊩e⇒ ⊩e⇐ newH = {!!}
complete-chk (⊢d-lam₂ ⊢e) Aj ⊩e⇒ ⊩e⇐ newH = {!!}
complete-chk (⊢d-app⇐ ⊢e ⊢e₁) Aj ⊩e⇒ ⊩e⇐ newH = {!!}
complete-chk (⊢d-app⇒ ⊢e ⊢e₁) Aj ⊩e⇒ ⊩e⇐ newH = {!!}
complete-chk (⊢d-sub ⊢e x x₁) Aj ⊩e⇒ ⊩e⇐ newH = {!!}
complete-chk (⊢d-& ⊢e ⊢e₁) Aj ⊩e⇒ ⊩e⇐ newH = {!!}

complete-inf ⊢d-int n-z ⊩a-none ⊩a-none cht-none = ⊢a-lit
complete-inf (⊢d-var x) n-z ⊩a-none ⊩a-none cht-none = ⊢a-var x
complete-inf (⊢d-ann ⊢e) n-z ⊩a-none ⊩a-none cht-none = ⊢a-ann (complete-chk-0 ⊢e)
complete-inf (⊢d-lam₂ ⊢e) (n-s⇒ Aj) (⊩a-cons ⊩e⇒ x) ⊩e⇐ (cht-cons newH) =
  ⊢a-lam₂ x (complete-inf ⊢e Aj (⊩a-weaken ⊩e⇒) (⊩a-weaken⇚ ⊩e⇐) (≗-shift newH))
complete-inf (⊢d-app⇐ ⊢e ⊢e₁) Aj ⊩e⇒ ⊩e⇐ newH = ⊢a-app {!complete-inf ⊢e (n-s⇐ Aj) ⊩e⇒ (⊩a-cons ⊩e⇐ (complete-chk-0 ⊢e₁)) !}
  where ind-e = complete-inf ⊢e (n-s⇐ Aj) ⊩e⇒ (⊩a-cons ⊩e⇐ (complete-chk-0 ⊢e₁)) {!!}
complete-inf (⊢d-app⇒ ⊢e ⊢e₁) Aj ⊩e⇒ ⊩e⇐ newH = {!!}
complete-inf (⊢d-sub ⊢e x x₁) Aj ⊩e⇒ ⊩e⇐ newH = subsumption-0 (complete-inf-0 ⊢e) {!!}

-- S⇒ S⇒ S⇒ S⇐ S⇐ S⇐ Z/∞
