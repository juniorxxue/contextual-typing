module Bot.Decl where

open import Bot.Prelude
open import Bot.Common

----------------------------------------------------------------------
--+                                                                +--
--+                           Subtyping                            +--
--+                                                                +--
----------------------------------------------------------------------

infix 5 _≤d_
data _≤d_ : Type → Type → Set where
  ≤d-int :
      Int ≤d Int
  ≤d-top :
      A ≤d Top
  ≤d-bot :
      Bot ≤d A
  ≤d-arr :
      C ≤d A
    → B ≤d D
    → A ⇒ B ≤d C ⇒ D
    
≤d-refl : A ≤d A
≤d-refl {Int} = ≤d-int
≤d-refl {Top} = ≤d-top
≤d-refl {Bot} = ≤d-bot
≤d-refl {A ⇒ B} = ≤d-arr ≤d-refl ≤d-refl

----------------------------------------------------------------------
--+                                                                +--
--+                             Typing                             +--
--+                                                                +--
----------------------------------------------------------------------

data Counter : Set where
  ∞ : Counter
  c_ : ℕ → Counter

variable
  ∞/n : Counter

infix 4 _⊢d_╏_⦂_

data _⊢d_╏_⦂_ : Context → Counter → Term → Type → Set where
  ⊢d-int :
      Γ ⊢d (c n) ╏ (lit i) ⦂ Int

  ⊢d-var :
      Γ ∋ x ⦂ A
    → Γ ⊢d (c n) ╏ ` x ⦂ A

  -- in presentation, we can merge two lam rules with a "dec" operation

  ⊢d-lam₁ :
      Γ , A ⊢d ∞ ╏ e ⦂ B
    → Γ ⊢d ∞ ╏ (ƛ e) ⦂ A ⇒ B -- full information, we are safe to use

  ⊢d-lam₂ :
      Γ , A ⊢d c n ╏ e ⦂ B
    → Γ ⊢d c (suc n) ╏ (ƛ e) ⦂ A ⇒ B -- not full, only given a few arguments, we need to be careful to count arguments

  ⊢d-lam₃ :
      Γ , Bot ⊢d ∞ ╏ e ⦂ Top
    → Γ ⊢d ∞ ╏ (ƛ e) ⦂ Top

  ⊢d-app₁ :
      Γ ⊢d (c 0) ╏ e₁ ⦂ A ⇒ B
    → Γ ⊢d ∞ ╏ e₂ ⦂ A
    → Γ ⊢d (c 0) ╏ e₁ · e₂ ⦂ B -- concern about this one

  ⊢d-app₂ :
      Γ ⊢d (c (suc n)) ╏ e₁ ⦂ A ⇒ B
    → Γ ⊢d (c 0) ╏ e₂ ⦂ A
    → Γ ⊢d (c n) ╏ e₁ · e₂ ⦂ B

  ⊢d-app₃ :
      Γ ⊢d ∞ ╏ e₁ ⦂ A ⇒ B
    → Γ ⊢d (c 0) ╏ e₂ ⦂ A
    → Γ ⊢d ∞ ╏ e₁ · e₂ ⦂ B

  ⊢d-ann :
      Γ ⊢d ∞ ╏ e ⦂ A
    → Γ ⊢d (c n) ╏ (e ⦂ A) ⦂ A

  ⊢d-sub :
      Γ ⊢d c 0 ╏ e ⦂ B
    → B ≤d A
    → Γ ⊢d ∞ ╏ e ⦂ A


----------------------------------------------------------------------
--+                                                                +--
--+                            Examples                            +--
--+                                                                +--
----------------------------------------------------------------------

_ : ∅ ⊢d (c 0) ╏ (ƛ (` 0)) · lit 1 ⦂ Int
_ = ⊢d-app₂ (⊢d-lam₂ (⊢d-var Z)) ⊢d-int

_ : ∅ ⊢d (c 0) ╏ ((ƛ ` 0 · (lit 1)) ⦂ (Int ⇒ Int) ⇒ Int) · (ƛ ` 0) ⦂ Int
_ = ⊢d-app₁ (⊢d-ann (⊢d-lam₁ (⊢d-app₃ (⊢d-sub (⊢d-var Z) (≤d-arr ≤d-int ≤d-int)) ⊢d-int))) (⊢d-lam₁ (⊢d-sub (⊢d-var Z) ≤d-int))

-- we want it to reject |-0 (\x . \y. y) 1
failed : ∅ ⊢d (c 0) ╏ (ƛ (ƛ ` 0)) · (lit 1) ⦂ (Int ⇒ Int) → ⊥
failed (⊢d-app₂ (⊢d-lam₂ ()) ⊢d₁)

-- let count to be 1, the cases should be okay,
_ : ∅ ⊢d (c 1) ╏ (ƛ (ƛ ` 0)) · (lit 1) ⦂ (Int ⇒ Int)
_ = ⊢d-app₂ (⊢d-lam₂ (⊢d-lam₂ (⊢d-var Z))) ⊢d-int

_ : ∅ ⊢d (c 0) ╏ (ƛ ((ƛ ` 0) ⦂ (Int ⇒ Int) ⇒ Int ⇒ Int)) · (lit 2) · (ƛ ` 0) ⦂ Int ⇒ Int
_ = ⊢d-app₁ (⊢d-app₂ (⊢d-lam₂ (⊢d-ann (⊢d-lam₁ (⊢d-sub (⊢d-var Z) ≤d-refl)))) ⊢d-int) (⊢d-lam₁ (⊢d-sub (⊢d-var Z) ≤d-refl))
