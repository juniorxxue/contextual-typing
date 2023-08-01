module SubGen.Decl where

open import SubGen.Prelude
open import SubGen.Common

----------------------------------------------------------------------
--+                                                                +--
--+                            Counter                             +--
--+                                                                +--
----------------------------------------------------------------------

data Counter : Set where
  ∞ : Counter
  c_ : ℕ → Counter

succ : Counter → Counter
succ ∞ = ∞
succ (c n) = c (suc n)

private
  variable
    ∞/n : Counter

----------------------------------------------------------------------
--+                                                                +--
--+                           Subtyping                            +--
--+                                                                +--
----------------------------------------------------------------------

infix 5 _≤d_#_
data _≤d_#_ : Type → Counter → Type → Set where
  -- we force the refl to set as zero
  ≤d-0 : ∀ {A}
    → A ≤d c 0 # A
  ≤d-int∞ :
      Int ≤d ∞ # Int
  ≤d-base∞ : ∀ {n}
    → * n ≤d ∞ # * n
  ≤d-top : ∀ {A}
    → A ≤d ∞ # Top
  -- this can be merged to one single rule in presentation
  -- but not for formalisation in pred counter is partial
  ≤d-arr∞ : ∀ {A B C D}
    → C ≤d ∞ # A
    → B ≤d ∞ # D
    → A ⇒ B ≤d ∞ # C ⇒ D
  ≤d-arrn : ∀ {A B C D n}
    → C ≤d ∞ # A
    → B ≤d (c n) # D
    → A ⇒ B ≤d c (suc n) # C ⇒ D    
  ≤d-and₁ : ∀ {A B C}
    → A ≤d ∞/n # C
    → A & B ≤d ∞/n # C
  ≤d-and₂ : ∀ {A B C}
    → B ≤d ∞/n # C
    → A & B ≤d ∞/n # C
  ≤d-and : ∀ {A B C}
    → A ≤d ∞ # B
    → A ≤d ∞ # C
    → A ≤d ∞ # B & C

≤-refl0 : ∀ {A} → A ≤d c 0 # A
≤-refl0 = ≤d-0

≤d-refl∞ : ∀ {A} → A ≤d ∞ # A
≤d-refl∞ {A = Int} = ≤d-int∞
≤d-refl∞ {A = * x} = ≤d-base∞
≤d-refl∞ {A = Top} = ≤d-top
≤d-refl∞ {A = A ⇒ A₁} = ≤d-arr∞ ≤d-refl∞ ≤d-refl∞
≤d-refl∞ {A = A & A₁} = ≤d-and (≤d-and₁ ≤d-refl∞) (≤d-and₂ ≤d-refl∞)


----------------------------------------------------------------------
--+                                                                +--
--+                             Typing                             +--
--+                                                                +--
----------------------------------------------------------------------

infix 4 _⊢d_#_⦂_

data _⊢d_#_⦂_ : Context → Counter → Term → Type → Set where
  ⊢d-int : ∀ {Γ i}
    → Γ ⊢d (c 0) # (lit i) ⦂ Int

  ⊢d-var : ∀ {Γ x A}
    → Γ ∋ x ⦂ A
    → Γ ⊢d (c 0) # ` x ⦂ A

  -- in presentation, we can merge two lam rules with a "dec" operation

  ⊢d-lam₁ : ∀ {Γ e A B}
    → Γ , A ⊢d ∞ # e ⦂ B
    → Γ ⊢d ∞ # (ƛ e) ⦂ A ⇒ B -- full information, we are safe to use

  ⊢d-lam₂ : ∀ {Γ e A B n}
    → Γ , A ⊢d c n # e ⦂ B
    → Γ ⊢d c (suc n) # (ƛ e) ⦂ A ⇒ B -- not full, only given a few arguments, we need to be careful to count arguments

  ⊢d-app₁ : ∀ {Γ e₁ e₂ A B}
    → Γ ⊢d (c 0) # e₁ ⦂ A ⇒ B
    → Γ ⊢d ∞ # e₂ ⦂ A
    → Γ ⊢d (c 0) # e₁ · e₂ ⦂ B -- concern about this one

  ⊢d-app₂ : ∀ {Γ e₁ e₂ A B n}
    → Γ ⊢d (c (suc n)) # e₁ ⦂ A ⇒ B
    → Γ ⊢d (c 0) # e₂ ⦂ A
    → Γ ⊢d (c n) # e₁ · e₂ ⦂ B

  ⊢d-app₃ : ∀ {Γ e₁ e₂ A B}
    → Γ ⊢d ∞ # e₁ ⦂ A ⇒ B
    → Γ ⊢d (c 0) # e₂ ⦂ A
    → Γ ⊢d ∞ # e₁ · e₂ ⦂ B

  ⊢d-ann : ∀ {Γ e A}
    → Γ ⊢d ∞ # e ⦂ A
    → Γ ⊢d (c 0) # (e ⦂ A) ⦂ A

  ⊢d-sub : ∀ {Γ e A B}
    → Γ ⊢d c 0 # e ⦂ B
    → B ≤d ∞/n # A
    → ∞/n ≢ c 0
    → Γ ⊢d ∞/n # e ⦂ A

  ⊢d-and-i : ∀ {Γ e A B}
    → Γ ⊢d ∞ # e ⦂ A
    → Γ ⊢d ∞ # e ⦂ B
    → Γ ⊢d ∞ # e ⦂ A & B

{- recovered by subsumption

   ⊢d-and-e₁ : ∀ {Γ e A B}
    → Γ ⊢d ∞/n # e ⦂ A & B
    → Γ ⊢d ∞/n # e ⦂ A

  ⊢d-and-e₂ : ∀ {Γ e A B}
    → Γ ⊢d ∞/n # e ⦂ A & B
    → Γ ⊢d ∞/n # e ⦂ B

-}

----------------------------------------------------------------------
--+                                                                +--
--+                            Examples                            +--
--+                                                                +--
----------------------------------------------------------------------

_ : ∅ ⊢d (c 0) # (ƛ (` 0)) · lit 1 ⦂ Int
_ = ⊢d-app₂ (⊢d-lam₂ (⊢d-var Z)) ⊢d-int

{-

_ : ∅ ⊢d (c 0) # ((ƛ ` 0 · (lit 1)) ⦂ (Int ⇒ Int) ⇒ Int) · (ƛ ` 0) ⦂ Int
_ = ⊢d-app₁ (⊢d-ann (⊢d-lam₁ (⊢d-app₃ (⊢d-sub (⊢d-var Z) (≤d-arr∞ ≤d-int∞ ≤d-int∞))
                                ⊢d-int))) (⊢d-lam₁ (⊢d-sub (⊢d-var Z) ≤d-int∞))

-}

-- we want it to reject |-0 (\x . \y. y) 1
-- failed : ∅ ⊢d (c 0) # (ƛ (ƛ ` 0)) · (lit 1) ⦂ (Int ⇒ Int) → ⊥

-- let count to be 1, the cases should be okay,
_ : ∅ ⊢d (c 1) # (ƛ (ƛ ` 0)) · (lit 1) ⦂ (Int ⇒ Int)
_ = ⊢d-app₂ (⊢d-lam₂ (⊢d-lam₂ (⊢d-var Z))) ⊢d-int

{-
_ : ∅ ⊢d (c 0) # (ƛ ((ƛ ` 0) ⦂ (Int ⇒ Int) ⇒ Int ⇒ Int)) · (lit 2) · (ƛ ` 0) ⦂ Int ⇒ Int
_ = ⊢d-app₁ (⊢d-app₂ (⊢d-lam₂ (⊢d-ann (⊢d-lam₁ (⊢d-sub (⊢d-var Z) (≤d-arr∞ ≤d-int∞ ≤d-int∞))))) ⊢d-int) (⊢d-lam₁ (⊢d-sub (⊢d-var Z) ≤d-int∞))
-}
{-
-- |-0 (\x . x : (Int -> Int) & (Bool -> Bool)) 1 : Int
_ : ∅ ⊢d (c 0) # ((ƛ ` 0) ⦂ (Int ⇒ Int) & (* 1 ⇒ * 1)) · (lit 1) ⦂ Int
_ = ⊢d-app₂ (⊢d-sub (⊢d-ann (⊢d-and-i (⊢d-lam₁ (⊢d-sub (⊢d-var Z) ≤d-int)) (⊢d-lam₁ (⊢d-sub (⊢d-var Z) ≤d-base)))) ≤d-and₁) ⊢d-int
-}

{-
_ : ∅ , * 1 ⊢d c 0 # ((ƛ ` 0) ⦂ (* 1 ⇒ * 1) & (* 2 ⇒ * 2)) · ` 0 ⦂ * 1
_ = ⊢d-app₂ (⊢d-sub (⊢d-ann (⊢d-and-i (⊢d-lam₁ (⊢d-sub (⊢d-var Z) ≤d-base∞))
                                      (⊢d-lam₁ (⊢d-sub (⊢d-var Z) ≤d-base∞))))
                    (≤d-and₁ (≤d-arrn ≤d-base∞ ≤d-0)))
            (⊢d-var Z)
-}
