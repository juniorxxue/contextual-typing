module Elaboration.Overloading.Source where

open import Elaboration.Overloading.Common

infixr 5  ƛ_⇒_
infixl 7  _·_
infix  9  `_
infix  5  _⦂_
-- infix  5  _+_

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
   ∞ : CCounter
   S⇐ : CCounter → CCounter
   
data Counter : Set where
   ♭ : CCounter → Counter
   S⇒ : Counter → Counter

infix 5 _≤d_#_
data _≤d_#_ : Type → Counter → Type → Set where
  ≤d-Z : ∀ {A}
    → A ≤d ♭ Z # A
  ≤d-S⇒ : ∀ {A B i}
    → A ≤d i # B
    → A ≤d (S⇒ i) # B
  ≤d-int∞ :
      Int ≤d ♭ ∞ # Int
  ≤d-float∞ :
      Float ≤d ♭ ∞ # Float
  ≤d-top : ∀ {A}
    → A ≤d ♭ ∞ # Top
  ≤d-arr-∞ : ∀ {A B C D}
    → C ≤d ♭ ∞ # A
    → B ≤d ♭ ∞ # D
    → A ⇒ B ≤d ♭ ∞ # C ⇒ D
  ≤d-arr-S⇐ : ∀ {A B C D j}
    → C ≤d ♭ ∞ # A
    → B ≤d ♭ j # D
    → A ⇒ B ≤d ♭ (S⇐ j) # A ⇒ D  
  ≤d-and₁ : ∀ {A B C j}
    → A ≤d j # C
    → j ≢ ♭ Z
    → A & B ≤d j # C
  ≤d-and₂ : ∀ {A B C j}
    → B ≤d j # C
    → j ≢ ♭ Z
    → A & B ≤d j # C
  ≤d-and : ∀ {A B C}
    → A ≤d ♭ ∞ # B
    → A ≤d ♭ ∞ # C
    → A ≤d ♭ ∞ # B & C

infix 4 _⊢d_#_⦂_

data _⊢d_#_⦂_ : Context → Counter → Term → Type → Set where
  ⊢d-int : ∀ {Γ n}
    → Γ ⊢d ♭ Z # (lit n) ⦂ Int

  ⊢d-flt : ∀ {Γ n}
    → Γ ⊢d ♭ Z # (flt n) ⦂ Float

  ⊢d-var : ∀ {Γ x A}
    → Γ ∋ x ⦂ A
    → Γ ⊢d ♭ Z # ` x ⦂ A

  ⊢d-ann : ∀ {Γ e A}
    → Γ ⊢d ♭ ∞ # e ⦂ A
    → Γ ⊢d ♭ Z # (e ⦂ A) ⦂ A

  ⊢d-lam₁ : ∀ {Γ e x A B}
    → Γ , x ⦂ A ⊢d ♭ ∞ # e ⦂ B
    → Γ ⊢d ♭ ∞ # (ƛ x ⇒ e) ⦂ A ⇒ B

  ⊢d-lam₂ : ∀ {Γ e x A B i}
    → Γ , x ⦂ A ⊢d i # e ⦂ B
    → Γ ⊢d S⇒ i # (ƛ x ⇒ e) ⦂ A ⇒ B

  ⊢d-app⇐ : ∀ {Γ e₁ e₂ A B j}
    → Γ ⊢d ♭ (S⇐ j) # e₁ ⦂ A ⇒ B
    → Γ ⊢d ♭ ∞ # e₂ ⦂ A
    → Γ ⊢d ♭ j # e₁ · e₂ ⦂ B

  ⊢d-app⇒ : ∀ {Γ e₁ e₂ A B j}
    → Γ ⊢d S⇒ j # e₁ ⦂ A ⇒ B
    → Γ ⊢d ♭ Z # e₂ ⦂ A
    → Γ ⊢d j # e₁ · e₂ ⦂ B

  ⊢d-sub : ∀ {Γ e A B i}
    → Γ ⊢d ♭ Z # e ⦂ B
    → B ≤d i # A
    → i ≢ ♭ Z
    → Γ ⊢d i # e ⦂ A

  ⊢d-+ : ∀ {Γ}
    → Γ ⊢d ♭ Z # + ⦂ (Int ⇒ Int ⇒ Int) & (Float ⇒ Float ⇒ Float)

  ⊢d-+i : ∀ {Γ n}
    → Γ ⊢d ♭ Z # (+i n) ⦂ Int ⇒ Int

  ⊢d-+f : ∀ {Γ m}
    → Γ ⊢d ♭ Z # (+f m) ⦂ Float ⇒ Float


≤d-refl∞ : ∀ {A} → A ≤d ♭ ∞ # A
≤d-refl∞ {A = Int} = ≤d-int∞
≤d-refl∞ {Float}  = ≤d-float∞
≤d-refl∞ {A = Top} = ≤d-top
≤d-refl∞ {A = A ⇒ A₁} = ≤d-arr-∞ ≤d-refl∞ ≤d-refl∞
≤d-refl∞ {A = A & A₁} = ≤d-and (≤d-and₁ ≤d-refl∞ λ ()) (≤d-and₂ ≤d-refl∞ λ ())

data plusS : Counter → Set where

  plusS-base :
    plusS (♭ ∞)

  plusS-S⇐ : ∀ {j}
    → plusS (♭ j)
    → plusS (♭ (S⇐ j))

  plusS-S⇒ : ∀ {i}
    → plusS i
    → plusS (S⇒ i)

{-
⊢d-∞-weaken : ∀ {Γ e i i' A}
  → Γ ⊢d i # e ⦂ A
  → plusS i
  → plusS i'
  → Γ ⊢d i' # e ⦂ A
⊢d-∞-weaken (⊢d-lam₁ ⊢e) plusS-base plusS-base = ⊢d-lam₁ ⊢e
⊢d-∞-weaken (⊢d-lam₁ ⊢e) plusS-base (plusS-S⇐ psi') = {!!}
⊢d-∞-weaken (⊢d-lam₁ ⊢e) plusS-base (plusS-S⇒ psi') = {!!}
⊢d-∞-weaken (⊢d-lam₂ ⊢e) psi psi' = {!!}
⊢d-∞-weaken (⊢d-app⇐ ⊢e ⊢e₁) psi psi' = {!!}
⊢d-∞-weaken (⊢d-app⇒ ⊢e ⊢e₁) psi psi' = {!!}
⊢d-∞-weaken (⊢d-sub ⊢e x x₁) psi psi' = {!!}
-}


----------------------------------------------------------------------
--+                                                                +--
--+                            Examples                            +--
--+                                                                +--
----------------------------------------------------------------------

_ : ∅ ⊢d ♭ Z # + · (lit 1) ⦂ Int ⇒ Int
_ = ⊢d-app⇐ (⊢d-sub ⊢d-+ (≤d-and₁ (≤d-arr-S⇐ ≤d-int∞ ≤d-Z) λ ()) λ ()) (⊢d-sub ⊢d-int ≤d-int∞ (λ ()))
