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

≤d-trans : A ≤d B → B ≤d C → A ≤d C
≤d-trans {.Int} {Int} {C} ≤d-int B≤C = B≤C
≤d-trans {.Bot} {Int} {C} ≤d-bot B≤C = ≤d-bot
≤d-trans {A} {Top} {.Top} ≤d-top ≤d-top = ≤d-top
≤d-trans {.Bot} {Top} {.Top} ≤d-bot ≤d-top = ≤d-top
≤d-trans {.Bot} {Bot} {C} ≤d-bot B≤C = B≤C
≤d-trans {.Bot} {B₁ ⇒ B₂} {C} ≤d-bot B≤C = ≤d-bot
≤d-trans {.(_ ⇒ _)} {B₁ ⇒ B₂} {.Top} (≤d-arr A≤B A≤B₁) ≤d-top = ≤d-top
≤d-trans {.(_ ⇒ _)} {B₁ ⇒ B₂} {.(_ ⇒ _)} (≤d-arr A≤B A≤B₁) (≤d-arr B≤C B≤C₁) = ≤d-arr (≤d-trans B≤C A≤B) (≤d-trans A≤B₁ B≤C₁)

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
  
infix 4 _⊢d_#_⦂_

data _⊢d_#_⦂_ : Context → Counter → Term → Type → Set where
  ⊢d-int :
      Γ ⊢d (c n) # (lit i) ⦂ Int

  ⊢d-var :
      Γ ∋ x ⦂ A
    → Γ ⊢d (c n) # ` x ⦂ A

  -- in presentation, we can merge two lam rules with a "dec" operation

  ⊢d-lam₁ :
      Γ , A ⊢d ∞ # e ⦂ B
    → Γ ⊢d ∞ # (ƛ e) ⦂ A ⇒ B -- full information, we are safe to use

  ⊢d-lam₂ :
      Γ , A ⊢d c n # e ⦂ B
    → Γ ⊢d c (suc n) # (ƛ e) ⦂ A ⇒ B -- not full, only given a few arguments, we need to be careful to count arguments

  ⊢d-lam₃ :
      Γ , Bot ⊢d ∞ # e ⦂ Top
    → Γ ⊢d ∞ # (ƛ e) ⦂ Top

  ⊢d-app₁ :
      Γ ⊢d (c 0) # e₁ ⦂ A ⇒ B
    → Γ ⊢d ∞ # e₂ ⦂ A
    → Γ ⊢d (c 0) # e₁ · e₂ ⦂ B

  ⊢d-app₁-bot :
      Γ ⊢d (c 0) # e₁ ⦂ Bot
    → Γ ⊢d ∞ # e₂ ⦂ A
    → Γ ⊢d (c 0) # e₁ · e₂ ⦂ Bot

  ⊢d-app₂ :
      Γ ⊢d (c (suc n)) # e₁ ⦂ A ⇒ B
    → Γ ⊢d (c 0) # e₂ ⦂ A
    → Γ ⊢d (c n) # e₁ · e₂ ⦂ B

  ⊢d-app₂-bot :
      Γ ⊢d (c (suc n)) # e₁ ⦂ Bot
    → Γ ⊢d (c 0) # e₂ ⦂ A
    → Γ ⊢d (c n) # e₁ · e₂ ⦂ Bot

  ⊢d-app₃ :
      Γ ⊢d ∞ # e₁ ⦂ A ⇒ B
    → Γ ⊢d (c 0) # e₂ ⦂ A
    → Γ ⊢d ∞ # e₁ · e₂ ⦂ B

  ⊢d-app₃-bot :
      Γ ⊢d ∞ # e₁ ⦂ Bot
    → Γ ⊢d (c 0) # e₂ ⦂ A
    → Γ ⊢d ∞ # e₁ · e₂ ⦂ Bot

  ⊢d-ann :
      Γ ⊢d ∞ # e ⦂ A
    → Γ ⊢d (c n) # (e ⦂ A) ⦂ A

  ⊢d-sub :
      Γ ⊢d c 0 # e ⦂ B
    → B ≤d A
    → Γ ⊢d ∞ # e ⦂ A
