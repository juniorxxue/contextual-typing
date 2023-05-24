module Dec where

open import Data.Nat using (ℕ; zero; suc; _+_; _*_; _^_; _∸_)
open import Data.String using (String)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl)
open import Data.Empty using (⊥; ⊥-elim)

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

infix 4 _⊢d_╏_⦂_

-- is Γ ⊢∞ e ⇒ A allowed?
-- one counter example is
-- Γ ⊢∞ (λx. x) 1 ⇒ Top
-- it happens in reasoning, no corresponding algo cases
-- (perhaps let Top appears in hint is okay, but it complicates the infer mode)

data _⊢d_╏_⦂_ : Context → Counter → Term → Type → Set where
  ⊢d-int : ∀ {Γ n i}
    → Γ ⊢d (c n) ╏ (lit i) ⦂ Int

  ⊢d-var : ∀ {Γ x A n}
    → Γ ∋ x ⦂ A
    → Γ ⊢d (c n) ╏ ` x ⦂ A

  -- in presentation, we can merge two lam rules with a "dec" operation

  ⊢d-lam₁ : ∀ {Γ x e A B}
    → Γ , x ⦂ A ⊢d ∞ ╏ e ⦂ B
    → Γ ⊢d ∞ ╏ (ƛ x ⇒ e) ⦂ A ⇒ B -- full information, we are safe to use

  ⊢d-lam₂ : ∀ {Γ x e A B n}
    → Γ , x ⦂ A ⊢d c n ╏ e ⦂ B
    → Γ ⊢d c (suc n) ╏ (ƛ x ⇒ e) ⦂ A ⇒ B -- not full, only given a few arguments, we need to be careful to count arguments

  ⊢d-app₁ : ∀ {Γ e₁ e₂ A B}
    → Γ ⊢d (c 0) ╏ e₁ ⦂ A ⇒ B
    → Γ ⊢d ∞ ╏ e₂ ⦂ A
    → Γ ⊢d (c 0) ╏ e₁ · e₂ ⦂ B -- concern about this one

  ⊢d-app₂ : ∀ {Γ e₁ e₂ A B n}
    → Γ ⊢d (c (suc n)) ╏ e₁ ⦂ A ⇒ B
    → Γ ⊢d (c 0) ╏ e₂ ⦂ A
    → Γ ⊢d (c n) ╏ e₁ · e₂ ⦂ B

  ⊢d-app₃ : ∀ {Γ e₁ e₂ A B}
    → Γ ⊢d ∞ ╏ e₁ ⦂ A ⇒ B
    → Γ ⊢d (c 0) ╏ e₂ ⦂ A
    → Γ ⊢d ∞ ╏ e₁ · e₂ ⦂ B

  ⊢d-ann : ∀ {Γ e A n}
    → Γ ⊢d ∞ ╏ e ⦂ A
    → Γ ⊢d (c n) ╏ (e ⦂ A) ⦂ A

  ⊢d-sub : ∀ {Γ e A B}
    → Γ ⊢d c 0 ╏ e ⦂ B
    → B ≤d A
    → Γ ⊢d ∞ ╏ e ⦂ A
