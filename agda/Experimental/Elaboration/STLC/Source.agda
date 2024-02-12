module Elaboration.STLC.Source where

open import Elaboration.STLC.Common

infixr 5  ƛ_⇒_
infixl 7  _·_
infix  9  `_
infix  5  _⦂_

data Term : Set where
  lit      : ℕ → Term
  `_       : Id → Term
  ƛ_⇒_     : Id → Term → Term
  _·_      : Term → Term → Term
  _⦂_      : Term → Type → Term

data Counter : Set where
  ∞ : Counter
  ‶_ : ℕ → Counter

infix 4 _⊢d_#_⦂_

data _⊢d_#_⦂_ : Context → Counter → Term → Type → Set where

  ⊢d-int : ∀ {Γ i}
    → Γ ⊢d ‶ 0 # (lit i) ⦂ Int

  ⊢d-var : ∀ {Γ x A}
    → Γ ∋ x ⦂ A
    → Γ ⊢d ‶ 0 # ` x ⦂ A

  ⊢d-ann : ∀ {Γ e A}
    → Γ ⊢d ∞ # e ⦂ A
    → Γ ⊢d ‶ 0 # (e ⦂ A) ⦂ A

  ⊢d-lam-∞ : ∀ {Γ e x A B}
    → Γ , x ⦂ A ⊢d ∞ # e ⦂ B
    → Γ ⊢d ∞ # (ƛ x ⇒ e) ⦂ A ⇒ B

  ⊢d-lam-n : ∀ {Γ e x A B n}
    → Γ , x ⦂ A ⊢d ‶ n # e ⦂ B
    → Γ ⊢d ‶ (suc n) # (ƛ x ⇒ e) ⦂ A ⇒ B

  ⊢d-app₁ : ∀ {Γ e₁ e₂ A B}
    → Γ ⊢d ‶ 0 # e₁ ⦂ A ⇒ B
    → Γ ⊢d ∞ # e₂ ⦂ A
    → Γ ⊢d ‶ 0 # e₁ · e₂ ⦂ B

  ⊢d-app₂ : ∀ {Γ e₁ e₂ A B n}
    → Γ ⊢d ‶ (suc n) # e₁ ⦂ A ⇒ B
    → Γ ⊢d ‶ 0 # e₂ ⦂ A
    → Γ ⊢d ‶ n # e₁ · e₂ ⦂ B

  ⊢d-app₃ : ∀ {Γ e₁ e₂ A B}
    → Γ ⊢d ∞ # e₁ ⦂ A ⇒ B
    → Γ ⊢d ‶ 0 # e₂ ⦂ A
    → Γ ⊢d ∞ # e₁ · e₂ ⦂ B
  

  ⊢d-sub : ∀ {Γ e A j}
    → Γ ⊢d ‶ 0 # e ⦂ A
    → j ≢ ‶ 0
    → Γ ⊢d j # e ⦂ A


⊢d-∞ : ∀ {Γ e A j}
  → Γ ⊢d j # e ⦂ A
  → Γ ⊢d ∞ # e ⦂ A
⊢d-∞ ⊢d-int = ⊢d-sub ⊢d-int (λ ())
⊢d-∞ (⊢d-var x) = ⊢d-sub (⊢d-var x) (λ ())
⊢d-∞ (⊢d-ann ⊢e) = ⊢d-sub (⊢d-ann ⊢e) (λ ())
⊢d-∞ (⊢d-lam-∞ ⊢e) = ⊢d-lam-∞ ⊢e
⊢d-∞ (⊢d-lam-n ⊢e) = ⊢d-lam-∞ (⊢d-∞ ⊢e)
⊢d-∞ (⊢d-app₁ ⊢e ⊢e₁) = ⊢d-sub (⊢d-app₁ ⊢e ⊢e₁) (λ ())
⊢d-∞ (⊢d-app₂ ⊢e ⊢e₁) = ⊢d-app₃ (⊢d-∞ ⊢e) ⊢e₁
⊢d-∞ (⊢d-app₃ ⊢e ⊢e₁) = ⊢d-app₃ ⊢e ⊢e₁
⊢d-∞ (⊢d-sub ⊢e x) = ⊢d-∞ ⊢e

⊢d-sub' : ∀ {Γ e A j}
  → Γ ⊢d ‶ 0 # e ⦂ A
  → Γ ⊢d j # e ⦂ A
⊢d-sub' {j = ∞} ⊢e = ⊢d-sub ⊢e (λ ())
⊢d-sub' {j = ‶ zero} ⊢e = ⊢e
⊢d-sub' {j = ‶ suc x} ⊢e = ⊢d-sub ⊢e (λ ())
