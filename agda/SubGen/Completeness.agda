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

complete-≤-s : ∀ {Γ A B i j T T' es es' H H' As Ts}
  → B ≤d i # A
  → ❪ A , i ❫↪❪ As , T , ♭ j ❫
  → ❪ T , j ❫↪♭❪ Ts , T' , Z ❫
  → Γ ⊩a es ⇛ As
  → Γ ⊩a es' ⇚ Ts
  → es' ⇒ □ ≣ H'
  → es ⇒ H' ≣ H
  → Γ ⊢a B ≤ H ⇝ A
complete-≤-s ≤d-Z ↪z ↪♭z ⊩a-none ⊩a-none ⇒≣-none ⇒≣-none = ≤a-□
complete-≤-s ≤d-int∞ ↪z () ⊢es ⊢es' newH' newH
complete-≤-s ≤d-base∞ ↪z () ⊢es ⊢es' newH' newH
complete-≤-s ≤d-top ↪z () ⊢es ⊢es' newH' newH
complete-≤-s (≤d-arr-∞ B≤A B≤A₁) ↪z () ⊢es ⊢es' newH' newH
complete-≤-s (≤d-arr-S⇒ B≤A B≤A₁) (↪s Aj) Tj (⊩a-cons ⊢es x) ⊢es' newH' (⇒≣-cons newH) =
  ≤a-hint (subsumption-0 x ≤a-refl) (complete-≤-s B≤A₁ Aj Tj ⊢es ⊢es' newH' newH)
complete-≤-s (≤d-arr-S⇐ B≤A B≤A₁) ↪z (↪♭s Tj) ⊩a-none (⊩a-cons ⊢es' x) (⇒≣-cons newH') ⇒≣-none =
  ≤a-hint x (complete-≤-s B≤A₁ ↪z Tj ⊩a-none ⊢es' newH' ⇒≣-none)
complete-≤-s (≤d-and₁ B≤A) Aj Tj ⊢es ⊢es' newH' newH = ≤a-and-l (complete-≤-s B≤A Aj Tj ⊢es ⊢es' newH' newH)
complete-≤-s (≤d-and₂ B≤A) Aj Tj ⊢es ⊢es' newH' newH = ≤a-and-r (complete-≤-s B≤A Aj Tj ⊢es ⊢es' newH' newH)
complete-≤-s (≤d-and B≤A B≤A₁) ↪z () ⊢es ⊢es' newH' newH


complete-≤-s-∞ : ∀ {Γ A B i j T T' es es' H H' As Ts}
  → B ≤d i # A
  → ❪ A , i ❫↪❪ As , T , ♭ j ❫
  → ❪ T , j ❫↪♭❪ Ts , T' , ∞ ❫
  → Γ ⊩a es ⇛ As
  → Γ ⊩a es' ⇚ Ts
  → es' ⇒ τ T' ≣ H'
  → es ⇒ H' ≣ H
  → Γ ⊢a B ≤ H ⇝ A

complete-≤-0 : ∀ {Γ A B}
  → B ≤d ♭ ∞ # A
  → Γ ⊢a B ≤ τ A ⇝ A
complete-≤-0 B≤A = complete-≤-s-∞ B≤A ↪z ↪♭∞ ⊩a-none ⊩a-none ⇒≣-none ⇒≣-none

complete-≤-s-∞ ≤d-Z ↪z () ⊢es ⊢es' newH' newH
complete-≤-s-∞ ≤d-int∞ ↪z ↪♭∞ ⊩a-none ⊩a-none ⇒≣-none ⇒≣-none = ≤a-int
complete-≤-s-∞ ≤d-base∞ ↪z ↪♭∞ ⊩a-none ⊩a-none ⇒≣-none ⇒≣-none = ≤a-base
complete-≤-s-∞ ≤d-top ↪z ↪♭∞ ⊩a-none ⊩a-none ⇒≣-none ⇒≣-none = ≤a-top
complete-≤-s-∞ (≤d-arr-∞ B≤A B≤A₁) ↪z ↪♭∞ ⊩a-none ⊩a-none ⇒≣-none ⇒≣-none = ≤a-arr (complete-≤-0 B≤A) (complete-≤-0 B≤A₁)
complete-≤-s-∞ (≤d-arr-S⇒ B≤A B≤A₁) (↪s Aj) Tj (⊩a-cons ⊢es x) ⊢es' newH' (⇒≣-cons newH) =
  ≤a-hint (subsumption-0 x ≤a-refl) (complete-≤-s-∞ B≤A₁ Aj Tj ⊢es ⊢es' newH' newH)
complete-≤-s-∞ (≤d-arr-S⇐ B≤A B≤A₁) ↪z (↪♭s Tj) ⊩a-none (⊩a-cons ⊢es' x) (⇒≣-cons newH') ⇒≣-none =
  ≤a-hint x (complete-≤-s-∞ B≤A₁ ↪z Tj ⊩a-none ⊢es' newH' ⇒≣-none)
complete-≤-s-∞ (≤d-and₁ B≤A) Aj Tj ⊢es ⊢es' newH' newH = ≤a-and-l (complete-≤-s-∞ B≤A Aj Tj ⊢es ⊢es' newH' newH)
complete-≤-s-∞ (≤d-and₂ B≤A) Aj Tj ⊢es ⊢es' newH' newH = ≤a-and-r (complete-≤-s-∞ B≤A Aj Tj ⊢es ⊢es' newH' newH)
complete-≤-s-∞ (≤d-and B≤A B≤A₁) ↪z ↪♭∞ ⊩a-none ⊩a-none ⇒≣-none ⇒≣-none = ≤a-and (complete-≤-s-∞ B≤A ↪z ↪♭∞ ⊩a-none ⊩a-none ⇒≣-none ⇒≣-none)
                                                                                 (complete-≤-s-∞ B≤A₁ ↪z ↪♭∞ ⊩a-none ⊩a-none ⇒≣-none ⇒≣-none)
  
complete-inf : ∀ {Γ e i j A As T Ts T' es' es H H'}
  → Γ ⊢d i # e ⦂ A
  → ❪ A , i ❫↪❪ As , T , ♭ j ❫
  → ❪ T , j ❫↪♭❪ Ts , T' , Z ❫
  → Γ ⊩a es ⇛ As
  → Γ ⊩a es' ⇚ Ts
  → es' ⇒ □ ≣ H'
  → es ⇒ H' ≣ H
  → Γ ⊢a H ⇛ e ⇛ A

complete-inf-∞ : ∀ {Γ e i j A As T Ts T' es' es H H'}
  → Γ ⊢d i # e ⦂ A
  → ❪ A , i ❫↪❪ As , T , ♭ j ❫
  → ❪ T , j ❫↪♭❪ Ts , T' , ∞ ❫
  → Γ ⊩a es ⇛ As
  → Γ ⊩a es' ⇚ Ts
  → es' ⇒ τ T' ≣ H'
  → es ⇒ H' ≣ H
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
complete-chk-i (⊢d-app⇒ ⊢e ⊢e₁) Aj ⊢es newH = ⊢a-app ind-e
  where ind-e = complete-inf ⊢e (↪s ↪z) Aj (⊩a-cons ⊩a-none (complete-chk-i-0 ⊢e₁)) ⊢es newH (⇒≣-cons ⇒≣-none)

complete-chk-i (⊢d-sub ⊢e x x₁) Aj ⊢es newH = subsumption-0 (complete-chk-i-0 ⊢e ) (complete-≤-i x Aj ⊢es newH)

complete-inf ⊢d-int ↪z ↪♭z ⊩a-none ⊩a-none ⇒≣-none ⇒≣-none = ⊢a-lit
complete-inf (⊢d-var x) ↪z ↪♭z ⊩a-none ⊩a-none ⇒≣-none ⇒≣-none = ⊢a-var x
complete-inf (⊢d-ann ⊢e) ↪z ↪♭z ⊩a-none ⊩a-none ⇒≣-none ⇒≣-none = ⊢a-ann (complete-chk-c-0 ⊢e)
complete-inf (⊢d-lam₁ ⊢e) ↪z () ⊢es ⊢es' newH' newH
complete-inf (⊢d-lam₂ ⊢e) (↪s Aj) Tj (⊩a-cons ⊢es x) ⊢es' newH' (⇒≣-cons newH) =
  ⊢a-lam₂ x (complete-inf ⊢e Aj Tj (⊩a-weaken ⊢es) (⊩a-weaken⇚ ⊢es') (≣-shift newH') (≣-shift newH))
complete-inf (⊢d-app⇐ ⊢e ⊢e₁) ↪z Tj ⊩a-none ⊢es' newH' ⇒≣-none = ⊢a-app ind-e
  where ind-e = complete-inf ⊢e ↪z (↪♭s Tj) ⊩a-none (⊩a-cons ⊢es' (complete-chk-c-0 ⊢e₁)) (⇒≣-cons newH') ⇒≣-none
complete-inf (⊢d-app⇒ ⊢e ⊢e₁) Aj Tj ⊢es ⊢es' newH' newH = ⊢a-app ind-e
  where ind-e = complete-inf ⊢e (↪s Aj) Tj (⊩a-cons ⊢es (complete-chk-i-0 ⊢e₁)) ⊢es' newH' (⇒≣-cons newH)
complete-inf (⊢d-sub ⊢e x x₁) Aj Tj ⊢es ⊢es' newH' newH = subsumption-0 (complete-chk-i-0 ⊢e) (complete-≤-s x Aj Tj ⊢es ⊢es' newH' newH)
complete-inf (⊢d-& ⊢e ⊢e₁) ↪z () ⊢es ⊢es' newH' newH

complete-inf-∞ ⊢d-int ↪z () ⊢es ⊢es' newH' newH
complete-inf-∞ (⊢d-var x) ↪z () ⊢es ⊢es' newH' newH
complete-inf-∞ (⊢d-ann ⊢e) ↪z () ⊢es ⊢es' newH' newH
complete-inf-∞ (⊢d-lam₁ ⊢e) ↪z ↪♭∞ ⊩a-none ⊩a-none ⇒≣-none ⇒≣-none = ⊢a-lam₁ (complete-inf-∞ ⊢e ↪z ↪♭∞ ⊩a-none ⊩a-none ⇒≣-none ⇒≣-none)
complete-inf-∞ (⊢d-lam₂ ⊢e) (↪s Aj) Tj (⊩a-cons ⊢es x) ⊢es' newH' (⇒≣-cons newH) =
  ⊢a-lam₂ x (complete-inf-∞ ⊢e Aj Tj (⊩a-weaken ⊢es) (⊩a-weaken⇚ ⊢es') (≣-shift newH') (≣-shift newH))
complete-inf-∞ (⊢d-app⇐ ⊢e ⊢e₁) ↪z Tj ⊩a-none ⊢es' newH' ⇒≣-none = ⊢a-app ind-e
  where ind-e = complete-inf-∞ ⊢e ↪z (↪♭s Tj) ⊩a-none (⊩a-cons ⊢es' (complete-chk-c-0 ⊢e₁)) (⇒≣-cons newH') ⇒≣-none
complete-inf-∞ (⊢d-app⇒ ⊢e ⊢e₁) Aj Tj ⊢es ⊢es' newH' newH = ⊢a-app ind-e
  where ind-e = complete-inf-∞ ⊢e (↪s Aj) Tj (⊩a-cons ⊢es (complete-chk-i-0 ⊢e₁)) ⊢es' newH' (⇒≣-cons newH)
complete-inf-∞ (⊢d-sub ⊢e x x₁) Aj Tj ⊢es ⊢es' newH' newH = subsumption-0 (complete-chk-i-0 ⊢e) (complete-≤-s-∞ x Aj Tj ⊢es ⊢es' newH' newH)
complete-inf-∞ (⊢d-& ⊢e ⊢e₁) ↪z ↪♭∞ ⊩a-none ⊩a-none ⇒≣-none ⇒≣-none = ⊢a-& (complete-chk-c-0 ⊢e) (complete-chk-c-0 ⊢e₁)

complete-chk-c (⊢d-lam₁ ⊢e) ↪♭∞ ⊩a-none ⇒≣-none = ⊢a-lam₁ (complete-chk-c-0 ⊢e)
complete-chk-c (⊢d-app⇐ ⊢e ⊢e₁) Aj ⊢es newH = ⊢a-app ind-e
  where ind-e = complete-chk-c ⊢e (↪♭s Aj) (⊩a-cons ⊢es (complete-chk-c-0 ⊢e₁)) (⇒≣-cons newH)
complete-chk-c (⊢d-app⇒ ⊢e ⊢e₁) Aj ⊢es newH = ⊢a-app ind-e
  where ind-e = complete-inf-∞ ⊢e (↪s ↪z) Aj (⊩a-cons ⊩a-none (complete-chk-i-0 ⊢e₁)) ⊢es newH (⇒≣-cons ⇒≣-none)
complete-chk-c (⊢d-sub ⊢e x x₁) Aj ⊢es newH = subsumption-0 (complete-chk-i-0 ⊢e) (complete-≤-s-∞ x ↪z Aj ⊩a-none ⊢es newH ⇒≣-none)
complete-chk-c (⊢d-& ⊢e ⊢e₁) ↪♭∞ ⊩a-none ⇒≣-none = ⊢a-& (complete-chk-c ⊢e ↪♭∞ ⊩a-none ⇒≣-none)
                                                        (complete-chk-c ⊢e₁ ↪♭∞ ⊩a-none ⇒≣-none)


  
