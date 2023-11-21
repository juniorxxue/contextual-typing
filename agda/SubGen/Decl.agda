module SubGen.Decl where

open import SubGen.Prelude
open import SubGen.Common

----------------------------------------------------------------------
--+                                                                +--
--+                            Counter                             +--
--+                                                                +--
----------------------------------------------------------------------

data Mode : Set where
  I : Mode
  C : Mode

{-
data Counter : Mode → Set where
  ∞ : ∀ {m} → Counter m
  Z : ∀ {m} → Counter m
  S⇒ : ∀ {m} → Counter m → Counter I
  S⇐ : Counter C → Counter C
-}

data CCounter : Set where
   Z : CCounter
   ∞ : CCounter
   S⇐ : CCounter → CCounter
   
data Counter : Set where
   ♭ : CCounter → Counter
   S⇒ : Counter → Counter
   
----------------------------------------------------------------------
--+                                                                +--
--+                           Subtyping                            +--
--+                                                                +--
----------------------------------------------------------------------

infix 5 _≤d_#_
data _≤d_#_ : Type → Counter → Type → Set where
  -- we force the refl to set as zero
  ≤d-Z : ∀ {A}
    → A ≤d ♭ Z # A
  ≤d-int∞ :
      Int ≤d ♭ ∞ # Int
  ≤d-base∞ : ∀ {n}
    → * n ≤d ♭ ∞ # * n
  ≤d-top : ∀ {A}
    → A ≤d ♭ ∞ # Top
  -- this can be merged to one single rule in presentation
  -- but not for formalisation in pred counter is partial
  ≤d-arr-∞ : ∀ {A B C D}
    → C ≤d ♭ ∞ # A
    → B ≤d ♭ ∞ # D
    → A ⇒ B ≤d ♭ ∞ # C ⇒ D
  ≤d-arr-S⇒ : ∀ {A B C D j}
    → C ≤d ♭ ∞ # A
    → B ≤d j # D
    → A ⇒ B ≤d S⇒ j # A ⇒ D
  ≤d-arr-S⇐ : ∀ {A B C D j}
    → C ≤d ♭ ∞ # A
    → B ≤d ♭ j # D
    → A ⇒ B ≤d ♭ (S⇐ j) # A ⇒ D  
  ≤d-and₁ : ∀ {A B C j}
    → A ≤d j # C
    → A & B ≤d j # C
  ≤d-and₂ : ∀ {A B C j}
    → B ≤d j # C
    → A & B ≤d j # C
  ≤d-and : ∀ {A B C}
    → A ≤d ♭ ∞ # B
    → A ≤d ♭ ∞ # C
    → A ≤d ♭ ∞ # B & C

≤-refl0 : ∀ {A} → A ≤d ♭ Z # A
≤-refl0 = ≤d-Z

≤d-refl∞ : ∀ {A} → A ≤d ♭ ∞ # A
≤d-refl∞ {A = Int} = ≤d-int∞
≤d-refl∞ {A = * x} = ≤d-base∞
≤d-refl∞ {A = Top} = ≤d-top
≤d-refl∞ {A = A ⇒ A₁} = ≤d-arr-∞ ≤d-refl∞ ≤d-refl∞
≤d-refl∞ {A = A & A₁} = ≤d-and (≤d-and₁ ≤d-refl∞) (≤d-and₂ ≤d-refl∞)


----------------------------------------------------------------------
--+                                                                +--
--+                             Typing                             +--
--+                                                                +--
----------------------------------------------------------------------

infix 4 _⊢d_#_⦂_

data _⊢d_#_⦂_ : Context → Counter → Term → Type → Set where
  ⊢d-int : ∀ {Γ n}
    → Γ ⊢d ♭ Z # (lit n) ⦂ Int

  ⊢d-var : ∀ {Γ x A}
    → Γ ∋ x ⦂ A
    → Γ ⊢d ♭ Z # ` x ⦂ A

  ⊢d-ann : ∀ {Γ e A}
    → Γ ⊢d ♭ ∞ # e ⦂ A
    → Γ ⊢d ♭ Z # (e ⦂ A) ⦂ A

  ⊢d-lam₁ : ∀ {Γ e A B}
    → Γ , A ⊢d ♭ ∞ # e ⦂ B
    → Γ ⊢d ♭ ∞ # (ƛ e) ⦂ A ⇒ B

  ⊢d-lam₂ : ∀ {Γ e A B i}
    → Γ , A ⊢d i # e ⦂ B
    → Γ ⊢d S⇒ i # (ƛ e) ⦂ A ⇒ B

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

  ⊢d-& : ∀ {Γ e A B}
    → Γ ⊢d ♭ ∞ # e ⦂ A
    → Γ ⊢d ♭ ∞ # e ⦂ B
    → Γ ⊢d ♭ ∞ # e ⦂ A & B
