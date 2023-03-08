module Dec where

open import Data.Nat using (ℕ; zero; suc; _+_; _*_; _^_; _∸_)
open import Data.String using (String)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl)
open import Common




----------------------------------------------------------------------
--+                                                                +--
--+                           Subtyping                            +--
--+                                                                +--
----------------------------------------------------------------------


infix 5 _≤d_
data _≤d_ : Type → Type → Set where
  ≤d-int :
      Int ≤d Int
  ≤d-top : ∀ {A}
    → A ≤d Top
  ≤d-arr : ∀ {A B C D}
    → C ≤d A
    → B ≤d D
    → A ⇒ B ≤d C ⇒ D
    
≤d-refl : ∀ {A} → A ≤d A
≤d-refl {Int} = ≤d-int
≤d-refl {Top} = ≤d-top
≤d-refl {A ⇒ B} = ≤d-arr ≤d-refl ≤d-refl

----------------------------------------------------------------------
--+                                                                +--
--+                             Typing                             +--
--+                                                                +--
----------------------------------------------------------------------

data Counter : Set where
  ∘ : Counter
  c_ : ℕ → Counter

pred : ℕ → ℕ
pred zero = zero
pred (suc n) = n

dec : Counter → Counter
dec ∘ = ∘
-- dec (c zero) = c zero
dec (c (suc n)) = dec (c n)

succ : Counter → Counter
succ ∘ = ∘
succ (c n) = c (suc n)

data Mode : Set where
  ⇛ : Mode
  ⇚ : Mode

infix 4 _⊢d_╏_∙_∙_

data _⊢d_╏_∙_∙_ : Context → Counter → Term → Mode → Type → Set where
  ⊢d-int : ∀ {Γ n j}
    → Γ ⊢d j ╏ (lit n) ∙ ⇛ ∙ Int

  ⊢d-var : ∀ {Γ x A j}
    → Γ ∋ x ⦂ A
    → Γ ⊢d j ╏ ` x ∙ ⇛ ∙ A

  ⊢d-lam : ∀ {Γ x e A B j}
    → Γ , x ⦂ A ⊢d (dec j) ╏ e ∙ ⇚ ∙ B
    → Γ ⊢d j ╏ (ƛ x ⇒ e) ∙ ⇚ ∙ A ⇒ B


  ⊢d-app₁ : ∀ {Γ e₁ e₂ A B j}
    → Γ ⊢d j ╏ e₁ ∙ ⇛ ∙ A ⇒ B
    → Γ ⊢d ∘ ╏ e₂ ∙ ⇚ ∙ A
    → Γ ⊢d j ╏ e₁ · e₂ ∙ ⇛ ∙ B

  ⊢d-app₂ : ∀ {Γ e₁ e₂ A B j}
    → Γ ⊢d (succ j) ╏ e₁ ∙ ⇚ ∙ A ⇒ B
    → Γ ⊢d (c zero) ╏ e₂ ∙ ⇛ ∙ A
    → Γ ⊢d j ╏ e₁ · e₂ ∙ ⇚ ∙ B

  ⊢d-ann : ∀ {Γ e A j}
    → Γ ⊢d ∘ ╏ e ∙ ⇚ ∙ A
    → Γ ⊢d j ╏ e ⦂ A ∙ ⇛ ∙ A

  ⊢d-sub : ∀ {Γ e A B j}
    → Γ ⊢d j ╏ e ∙ ⇛ ∙ B
    → B ≤d A
    → Γ ⊢d j ╏ e ∙ ⇚ ∙ A

