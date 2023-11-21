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

infix 4 _⇒_≣_
data _⇒_≣_ : List Term → Hint → Hint → Set where

  ⇒≣-none : ∀ {H}
    → [] ⇒ H ≣ H

  ⇒≣-cons : ∀ {e es H H'}
    → es ⇒ H ≣ H'
    → (e ∷ es) ⇒ H ≣ ⟦ e ⟧⇒ H'

-- es ⇒ H ≣ H'
-- es ⇒ (⟦ e ⟧⇒ H) ≣ 

≣-shift : ∀ {es H H'}
  → es ⇒ H ≣ H'
  → (map (_↑ 0) es ) ⇒ H ⇧ 0 ≣ H' ⇧ 0
≣-shift ⇒≣-none = ⇒≣-none
≣-shift (⇒≣-cons newH) = ⇒≣-cons (≣-shift newH)

≗-shift : ∀ {es⇒ es⇐ H H'}
  → es⇒ ↠ es⇐ ↠ H ≗ H'
  → map (_↑ 0) es⇒ ↠ map (_↑ 0) es⇐ ↠ H ⇧ 0 ≗ H' ⇧ 0
≗-shift cht-none = cht-none
≗-shift (cht-none-r newH) = cht-none-r (≗-shift newH)
≗-shift (cht-cons newH) = cht-cons (≗-shift newH)

infix 4 ❪_,_❫↪❪_,_,_❫

data ❪_,_❫↪❪_,_,_❫ : Type → Counter → List Type → Type → Counter → Set where

  ↪z : ∀ {A j}
    → ❪ A , ♭ j ❫↪❪ [] , A , ♭ j ❫

  ↪s : ∀ {A B As T i i'}
    → ❪ B , i ❫↪❪ As , T , i' ❫
    → ❪ A ⇒ B , S⇒ i ❫↪❪ A ∷ As , T , i' ❫

infix 4 ❪_,_❫↪♭❪_,_,_❫

data ❪_,_❫↪♭❪_,_,_❫ : Type → CCounter → List Type → Type → CCounter → Set where

  ↪♭z : ∀ {A}
    → ❪ A , Z ❫↪♭❪ [] , A , Z ❫

  ↪♭∞ : ∀ {A}
    → ❪ A , ∞ ❫↪♭❪ [] , A , ∞ ❫

  ↪♭s : ∀ {A B As T j j'}
    → ❪ B , j ❫↪♭❪ As , T , j' ❫
    → ❪ A ⇒ B , S⇐ j ❫↪♭❪ A ∷ As , T , j' ❫

complete-≤-i : ∀ {Γ A B j As T es H}
  → B ≤d ♭ j # A
  → ❪ A , j ❫↪♭❪ As , T , Z ❫
  → Γ ⊩a es ⇚ As
  → es ⇒ □ ≣ H
  → Γ ⊢a B ≤ H ⇝ A
complete-≤-i ≤d-Z ↪♭z ⊩a-none ⇒≣-none = ≤a-□
complete-≤-i (≤d-arr-S⇐ B≤A B≤A₁) (↪♭s Aj) (⊩a-cons ⊢es x) (⇒≣-cons newH) = ≤a-hint x (complete-≤-i B≤A₁ Aj ⊢es newH)
complete-≤-i (≤d-and₁ B≤A) Aj ⊢es newH = ≤a-and-l (complete-≤-i B≤A Aj ⊢es newH)
complete-≤-i (≤d-and₂ B≤A) Aj ⊢es newH = ≤a-and-r (complete-≤-i B≤A Aj ⊢es newH)

complete-inf : ∀ {Γ e i j A As T es H}
  → Γ ⊢d i # e ⦂ A
  → ❪ A , i ❫↪❪ As , T , ♭ j ❫
  → Γ ⊩a es ⇛ As
  → es ⇒ τ T ≣ H
  → Γ ⊢a H ⇛ e ⇛ A

complete-chk-i : ∀ {Γ e j A As T es H}
  → Γ ⊢d ♭ j # e ⦂ A
  → ❪ A , j ❫↪♭❪ As , T , Z ❫
  → Γ ⊩a es ⇚ As
  → es ⇒ □ ≣ H
  → Γ ⊢a H ⇛ e ⇛ A

complete-chk-c : ∀ {Γ e j A As T es H}
  → Γ ⊢d ♭ j # e ⦂ A
  → ❪ A , j ❫↪♭❪ As , T , ∞ ❫
  → Γ ⊩a es ⇚ As
  → es ⇒ τ T ≣ H
  → Γ ⊢a H ⇛ e ⇛ A

complete-chk-c-0 : ∀ {Γ e A}
  → Γ ⊢d ♭ ∞ # e ⦂ A
  → Γ ⊢a τ A ⇛ e ⇛ A
complete-chk-c-0 ⊢e = complete-chk-c ⊢e ↪♭∞ ⊩a-none ⇒≣-none

complete-chk-i-0 : ∀ {Γ e A}
  → Γ ⊢d ♭ Z # e ⦂ A
  → Γ ⊢a □ ⇛ e ⇛ A
complete-chk-i-0 ⊢e = complete-chk-i ⊢e ↪♭z ⊩a-none ⇒≣-none
  
complete-chk-i ⊢d-int ↪♭z ⊩a-none ⇒≣-none = ⊢a-lit
complete-chk-i (⊢d-var x) ↪♭z ⊩a-none ⇒≣-none = ⊢a-var x
complete-chk-i (⊢d-ann ⊢e) ↪♭z ⊩a-none ⇒≣-none = ⊢a-ann (complete-chk-c-0 ⊢e)
complete-chk-i (⊢d-app⇐ ⊢e ⊢e₁) Aj ⊢es newH = ⊢a-app ind-e 
  where ind-e = complete-chk-i ⊢e (↪♭s Aj) (⊩a-cons ⊢es (complete-chk-c-0 ⊢e₁)) (⇒≣-cons newH)
complete-chk-i (⊢d-app⇒ ⊢e ⊢e₁) Aj ⊢es newH =
  ⊢a-app (subsumption ind-e (have {!!}) (ch-cons ch-none)
                            (≤a-hint (subsumption-0 (complete-chk-i-0 ⊢e₁) ≤a-refl) (es-□-A Aj ⊢es newH)))
  where ind-e = complete-inf ⊢e (↪s ↪z) (⊩a-cons ⊩a-none (complete-chk-i-0 ⊢e₁)) (⇒≣-cons ⇒≣-none)
        es-□-A : ∀ {Γ j A T es As H}
          → ❪ A , j ❫↪♭❪ As , T , Z ❫
          → Γ ⊩a es ⇚ As
          → es ⇒ □ ≣ H
          → Γ ⊢a A ≤ H ⇝ A
        es-□-A Aj ⊩a-none ⇒≣-none = ≤a-□
        es-□-A (↪♭s Aj) (⊩a-cons ⊢es x) (⇒≣-cons newH) = ≤a-hint x (es-□-A Aj ⊢es newH)

complete-chk-i (⊢d-sub ⊢e x x₁) Aj ⊢es newH = subsumption-0 (complete-chk-i-0 ⊢e ) (complete-≤-i x Aj ⊢es newH)

complete-inf ⊢e Aj ⊢es newH = {!!}
complete-chk-c ⊢e Aj ⊢es newH = {!!}


  
