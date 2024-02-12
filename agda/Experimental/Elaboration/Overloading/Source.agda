module Elaboration.Overloading.Source where

open import Elaboration.Overloading.Common

infixr 5  ƛ_⇒_
infixl 7  _·_
infix  9  `_
infix  5  _⦂_

data Term : Set where
  lit      : ℕ → Term
  flt      : 𝔽 → Term
  `_       : Id → Term
  ƛ_⇒_     : Id → Term → Term
  _·_      : Term → Term → Term
  _⦂_      : Term → Type → Term
  +        : Term
  +i       : ℕ → Term
  +f       : 𝔽 → Term

data CCounter : Set where
   Z : CCounter
   S⇐ : CCounter → CCounter
   
data ICounter : Set where
   𝕔_ : CCounter → ICounter
   S⇒ : ICounter → ICounter

data Counter : Set where
  ∞ : Counter
  ‶_ : ICounter → Counter

ℤ : Counter
ℤ = ‶ 𝕔 Z

ℂ : CCounter → Counter
ℂ c = ‶ (𝕔 c)

infix 5 _≤d_#_
data _≤d_#_ : Type → Counter → Type → Set where
  ≤d-Z : ∀ {A}
    → A ≤d ℤ # A
  ≤d-int∞ :
      Int ≤d ∞ # Int
  ≤d-float∞ :
      Float ≤d ∞ # Float
  ≤d-top : ∀ {A}
    → A ≤d ∞ # Top
  ≤d-arr-∞ : ∀ {A B C D}
    → C ≤d ∞ # A
    → B ≤d ∞ # D
    → A ⇒ B ≤d ∞ # C ⇒ D
  ≤d-arr-S⇐ : ∀ {A B C D j}
    → C ≤d ∞ # A
    → B ≤d ℂ j # D
    → A ⇒ B ≤d ℂ (S⇐ j) # A ⇒ D
  ≤d-arr-S⇒ : ∀ {A B C D i}
    → C ≤d ∞ # A
    → B ≤d ‶ i # D
    → A ⇒ B ≤d ‶ (S⇒ i) # A ⇒ D
  ≤d-and₁ : ∀ {A B C j}
    → A ≤d j # C
    → j ≢ ℤ
    → A & B ≤d j # C
  ≤d-and₂ : ∀ {A B C j}
    → B ≤d j # C
    → j ≢ ℤ
    → A & B ≤d j # C
  ≤d-and : ∀ {A B C}
    → A ≤d ∞ # B
    → A ≤d ∞ # C
    → A ≤d ∞ # B & C

infix 4 _⊢d_#_⦂_

data _⊢d_#_⦂_ : Context → Counter → Term → Type → Set where
  ⊢d-int : ∀ {Γ n}
    → Γ ⊢d ℤ # (lit n) ⦂ Int

  ⊢d-flt : ∀ {Γ n}
    → Γ ⊢d ℤ # (flt n) ⦂ Float

  ⊢d-var : ∀ {Γ x A}
    → Γ ∋ x ⦂ A
    → Γ ⊢d ℤ # ` x ⦂ A

  ⊢d-ann : ∀ {Γ e A}
    → Γ ⊢d ∞ # e ⦂ A
    → Γ ⊢d ℤ # (e ⦂ A) ⦂ A

  ⊢d-lam₁ : ∀ {Γ e x A B}
    → Γ , x ⦂ A ⊢d ∞ # e ⦂ B
    → Γ ⊢d ∞ # (ƛ x ⇒ e) ⦂ A ⇒ B

  ⊢d-lam₂ : ∀ {Γ e x A B i}
    → Γ , x ⦂ A ⊢d ‶ i # e ⦂ B
    → Γ ⊢d ‶ (S⇒ i) # (ƛ x ⇒ e) ⦂ A ⇒ B

  ⊢d-app⇐ : ∀ {Γ e₁ e₂ A B j}
    → Γ ⊢d ℂ (S⇐ j) # e₁ ⦂ A ⇒ B
    → Γ ⊢d ∞ # e₂ ⦂ A
    → Γ ⊢d ℂ j # e₁ · e₂ ⦂ B

  ⊢d-app⇒ : ∀ {Γ e₁ e₂ A B j}
    → Γ ⊢d ‶ (S⇒ j) # e₁ ⦂ A ⇒ B
    → Γ ⊢d ℤ # e₂ ⦂ A
    → Γ ⊢d ‶ j # e₁ · e₂ ⦂ B

  ⊢d-app∞ : ∀ {Γ e₁ e₂ A B}
    → Γ ⊢d ∞ # e₁ ⦂ A ⇒ B
    → Γ ⊢d ℤ # e₂ ⦂ A
    → Γ ⊢d ∞ # e₁ · e₂ ⦂ B

  ⊢d-sub : ∀ {Γ e A B i}
    → Γ ⊢d ℤ # e ⦂ B
    → B ≤d i # A
    → i ≢ ℤ
    → Γ ⊢d i # e ⦂ A

  ⊢d-+ : ∀ {Γ}
    → Γ ⊢d ℤ # + ⦂ (Int ⇒ Int ⇒ Int) & (Float ⇒ Float ⇒ Float)

  ⊢d-+i : ∀ {Γ n}
    → Γ ⊢d ℤ # (+i n) ⦂ Int ⇒ Int

  ⊢d-+f : ∀ {Γ m}
    → Γ ⊢d ℤ # (+f m) ⦂ Float ⇒ Float


≤d-refl∞ : ∀ {A} → A ≤d ∞ # A
≤d-refl∞ {A = Int} = ≤d-int∞
≤d-refl∞ {Float}  = ≤d-float∞
≤d-refl∞ {A = Top} = ≤d-top
≤d-refl∞ {A = A ⇒ A₁} = ≤d-arr-∞ ≤d-refl∞ ≤d-refl∞
≤d-refl∞ {A = A & A₁} = ≤d-and (≤d-and₁ ≤d-refl∞ λ ()) (≤d-and₂ ≤d-refl∞ λ ())

⊢d-sub' : ∀ {Γ e i A B}
  → Γ ⊢d ℤ # e ⦂ B
  → B ≤d i # A
  → Γ ⊢d i # e ⦂ A
⊢d-sub' {i = ∞} ⊢e B≤A = ⊢d-sub ⊢e B≤A (λ ())
⊢d-sub' {i = ‶ (𝕔 Z)} ⊢e ≤d-Z = ⊢e
⊢d-sub' {i = ‶ (𝕔 Z)} ⊢e (≤d-and₁ B≤A x) = ⊥-elim (x refl)
⊢d-sub' {i = ‶ (𝕔 Z)} ⊢e (≤d-and₂ B≤A x) = ⊥-elim (x refl)
⊢d-sub' {i = ‶ (𝕔 S⇐ x)} ⊢e B≤A = ⊢d-sub ⊢e B≤A (λ ())
⊢d-sub' {i = ‶ S⇒ x} ⊢e B≤A = ⊢d-sub ⊢e B≤A (λ ())

infix 3 _~_
data _~_ : CCounter → ICounter → Set where

  ~Z : ∀ {j}
    → j ~ 𝕔 j

  ~SC : ∀ {j j'}
    → j ~ 𝕔 j'
    → j ~ 𝕔 (S⇐ j')

  ~SI : ∀ {j i}
    → j ~ i
    → j ~ S⇒ i

≤d-∞ : ∀ {A B i}
  → B ≤d i # A
  → B ≤d ∞ # A
≤d-∞ {i = ∞} B≤A = B≤A
≤d-∞ {i = ‶ .(𝕔 Z)} ≤d-Z = ≤d-refl∞
≤d-∞ {i = ‶ .(𝕔 S⇐ _)} (≤d-arr-S⇐ B≤A B≤A₁) = ≤d-arr-∞ (≤d-∞ ≤d-Z) (≤d-∞ B≤A₁)
≤d-∞ {i = ‶ .(S⇒ _)} (≤d-arr-S⇒ B≤A B≤A₁) = ≤d-arr-∞ (≤d-∞ ≤d-Z) (≤d-∞ B≤A₁)
≤d-∞ {i = ‶ x} (≤d-and₁ B≤A x₁) = ≤d-and₁ (≤d-∞ B≤A) (λ ())
≤d-∞ {i = ‶ x} (≤d-and₂ B≤A x₁) = ≤d-and₂ (≤d-∞ B≤A) (λ ())

⊢d-∞ : ∀ {Γ e i A}
  → Γ ⊢d i # e ⦂ A
  → Γ ⊢d ∞ # e ⦂ A
⊢d-∞ {i = ∞} ⊢e = ⊢e
⊢d-∞ {i = ‶ (𝕔 Z)} ⊢e = ⊢d-sub' ⊢e ≤d-refl∞
⊢d-∞ {i = ‶ (𝕔 S⇐ x)} (⊢d-app⇐ ⊢e ⊢e₁) = {!!}
-- ⊢d-sub-gen (⊢d-app⇐ ⊢e ⊢e₁) ≤d-refl∞
⊢d-∞ {i = ‶ (𝕔 S⇐ x)} (⊢d-app⇒ ⊢e ⊢e₁) = ⊢d-app∞ (⊢d-∞ ⊢e) ⊢e₁
⊢d-∞ {i = ‶ (𝕔 S⇐ x)} (⊢d-sub ⊢e x₁ x₂) = ⊢d-sub' ⊢e (≤d-∞ x₁)
⊢d-∞ {i = ‶ S⇒ x} (⊢d-lam₂ ⊢e) = ⊢d-lam₁ (⊢d-∞ ⊢e)
⊢d-∞ {i = ‶ S⇒ x} (⊢d-app⇒ ⊢e ⊢e₁) = ⊢d-app∞ (⊢d-∞ ⊢e) ⊢e₁
⊢d-∞ {i = ‶ S⇒ x} (⊢d-sub ⊢e x₁ x₂) = ⊢d-sub' ⊢e (≤d-∞ x₁)

----------------------------------------------------------------------
--+                                                                +--
--+                            Examples                            +--
--+                                                                +--
----------------------------------------------------------------------

_ : ∅ ⊢d ℤ # + · (lit 1) ⦂ Int ⇒ Int
_ = ⊢d-app⇐ (⊢d-sub ⊢d-+ (≤d-and₁ (≤d-arr-S⇐ ≤d-int∞ ≤d-Z) λ ()) λ ()) (⊢d-sub ⊢d-int ≤d-int∞ (λ ()))
