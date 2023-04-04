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
  ∞ : Counter
  c_ : ℕ → Counter

succ : Counter → Counter
succ ∞ = ∞
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

  -- in presentation, we can merge two lam rules with a "dec" operation

  ⊢d-lam₁ : ∀ {Γ e A B }
    → Γ , A ⊢d ∞ ╏ e ∙ ⇚ ∙ B
    → Γ ⊢d ∞ ╏ (ƛ e) ∙ ⇚ ∙ A ⇒ B -- full information, we are safe to use

  ⊢d-lam₂ : ∀ {Γ e A B n}
    → Γ , A ⊢d c n ╏ e ∙ ⇚ ∙ B
    → Γ ⊢d c (suc n) ╏ (ƛ e) ∙ ⇚ ∙ A ⇒ B -- not full, only given a few arguments, we need to be careful to count arguments

  ⊢d-app₁ : ∀ {Γ e₁ e₂ A B j}
    → Γ ⊢d j ╏ e₁ ∙ ⇛ ∙ A ⇒ B
    → Γ ⊢d ∞ ╏ e₂ ∙ ⇚ ∙ A
    → Γ ⊢d j ╏ e₁ · e₂ ∙ ⇛ ∙ B

  ⊢d-app₂ : ∀ {Γ e₁ e₂ A B j}
    → Γ ⊢d (succ j) ╏ e₁ ∙ ⇚ ∙ A ⇒ B
    → Γ ⊢d (c 0) ╏ e₂ ∙ ⇛ ∙ A
    → Γ ⊢d j ╏ e₁ · e₂ ∙ ⇛ ∙ B

  ⊢d-ann : ∀ {Γ e A j}
    → Γ ⊢d ∞ ╏ e ∙ ⇚ ∙ A
    → Γ ⊢d j ╏ e ⦂ A ∙ ⇛ ∙ A

  ⊢d-sub : ∀ {Γ e A B j}
    → Γ ⊢d c 0 ╏ e ∙ ⇛ ∙ B
    → B ≤d A
    → Γ ⊢d j ╏ e ∙ ⇚ ∙ A


----------------------------------------------------------------------
--+                                                                +--
--+                            Examples                            +--
--+                                                                +--
----------------------------------------------------------------------

_ : ∅ ⊢d (c 0) ╏ (ƛ (` 0)) · lit 1 ∙ ⇛ ∙ Int
_ = ⊢d-app₂ (⊢d-lam₂ (⊢d-sub (⊢d-var Z) ≤d-refl)) ⊢d-int

_ : ∅ ⊢d (c 0) ╏ ((ƛ ` 0 · (lit 1)) ⦂ (Int ⇒ Int) ⇒ Int) · (ƛ ` 0) ∙ ⇛ ∙ Int
_ = ⊢d-app₁ (⊢d-ann (⊢d-lam₁ (⊢d-sub (⊢d-app₁ (⊢d-var Z) (⊢d-sub ⊢d-int ≤d-refl)) ≤d-refl))) (⊢d-lam₁ (⊢d-sub (⊢d-var Z) ≤d-refl))
