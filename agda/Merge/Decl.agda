module Merge.Decl where

open import Merge.Prelude
open import Merge.Common

----------------------------------------------------------------------
--+                                                                +--
--+                            Counter                             +--
--+                                                                +--
----------------------------------------------------------------------

data CCounter : Set where
   Z : CCounter
   ∞ : CCounter
   S⇐ : CCounter → CCounter
   Sl : CCounter → CCounter -- remember to argue that this is not interleaved with S⇒

   
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
  ≤d-Z : ∀ {A}
    → A ≤d ♭ Z # A
  ≤d-int∞ :
      Int ≤d ♭ ∞ # Int
  ≤d-base∞ : ∀ {n}
    → * n ≤d ♭ ∞ # * n
  ≤d-top : ∀ {A}
    → A ≤d ♭ ∞ # Top
  ≤d-arr-∞ : ∀ {A B C D}
    → C ≤d ♭ ∞ # A
    → B ≤d ♭ ∞ # D
    → A ⇒ B ≤d ♭ ∞ # C ⇒ D
  ≤d-rcd∞ : ∀ {A B l}
    → A ≤d ♭ ∞ # B
    → ⌊ l ⇒ A ⌋ ≤d ♭ ∞ # ⌊ l ⇒ B ⌋
  ≤d-arr-S⇐ : ∀ {A B C D j}
    → C ≤d ♭ ∞ # A
    → B ≤d ♭ j # D
    → A ⇒ B ≤d ♭ (S⇐ j) # A ⇒ D
  ≤d-rcd-Sl : ∀ {A B l j}
    → A ≤d ♭ j # B
    → ⌊ l ⇒ A ⌋ ≤d ♭ (Sl j) # ⌊ l ⇒ B ⌋
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

≤-refl0 : ∀ {A} → A ≤d ♭ Z # A
≤-refl0 = ≤d-Z

≤d-refl∞ : ∀ {A} → A ≤d ♭ ∞ # A
≤d-refl∞ {A = Int} = ≤d-int∞
≤d-refl∞ {A = * x} = ≤d-base∞
≤d-refl∞ {A = Top} = ≤d-top
≤d-refl∞ {A = A ⇒ A₁} = ≤d-arr-∞ ≤d-refl∞ ≤d-refl∞
≤d-refl∞ {A = A & A₁} = ≤d-and (≤d-and₁ ≤d-refl∞ λ ()) (≤d-and₂ ≤d-refl∞ λ ())
≤d-refl∞ {⌊ l ⇒ A ⌋} = ≤d-rcd∞ ≤d-refl∞

----------------------------------------------------------------------
--+                                                                +--
--+                             Typing                             +--
--+                                                                +--
----------------------------------------------------------------------

infix 4 _⊢d_#_⦂_

data _⊢d_#_⦂_ : Context → Counter → Term → Type → Set

data _⊢d_#_⦂_ where

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

  ⊢d-⨟ : ∀ {Γ e₁ e₂ A B}
    → Γ ⊢d ♭ Z # e₁ ⦂ A
    → Γ ⊢d ♭ Z # e₂ ⦂ B
    → Γ ⊢d ♭ Z # e₁ ⨟ e₂ ⦂ A & B

  ⊢d-rcd : ∀ {Γ e l A}
    → Γ ⊢d ♭ Z # e ⦂ A
    → Γ ⊢d ♭ Z # ⌊ l ⇒ e ⌋ ⦂  ⌊ l ⇒ A ⌋

  ⊢d-prj : ∀ {Γ e l j A}
    → Γ ⊢d ♭ (Sl j) # e ⦂ ⌊ l ⇒ A ⌋
    → Γ ⊢d ♭ j # e ⋆ l ⦂ A


----------------------------------------------------------------------
--+                                                                +--
--+                            Examples                            +--
--+                                                                +--
----------------------------------------------------------------------

id-fun-& : Term
id-fun-& = (ƛ ` 0) ⦂ (Int ⇒ Int) & (* 1 ⇒ * 1)

⊢id-fun-& : ∅ ⊢d ♭ Z # id-fun-& ⦂ (Int ⇒ Int) & (* 1 ⇒ * 1)
⊢id-fun-& = ⊢d-ann (⊢d-& (⊢d-lam₁ (⊢d-sub (⊢d-var Z) ≤d-int∞ (λ ()))) (⊢d-lam₁ (⊢d-sub (⊢d-var Z) ≤d-base∞ (λ ()))))

example-sub-1 : (⌊ 1 ⇒ (Int ⇒ Int) & (* 1 ⇒ * 1) ⌋ & ⌊ 2 ⇒ Int ⌋) ≤d
       ♭ ((Sl (S⇐ Z))) # (⌊ 1 ⇒ (Int ⇒ Int) ⌋)
example-sub-1 = ≤d-and₁ (≤d-rcd-Sl (≤d-and₁ (≤d-arr-S⇐ ≤d-int∞ ≤d-Z) (λ ()))) (λ ())       

example-1 : ∅ ⊢d ♭ Z # ((⌊ 1 ⇒ id-fun-& ⌋ ⨟ ⌊ 2 ⇒ lit 2 ⌋) ⋆ 1) · (lit 42) ⦂ Int
example-1 = ⊢d-app⇐ (⊢d-prj (⊢d-sub (⊢d-⨟ (⊢d-rcd ⊢id-fun-&) (⊢d-rcd ⊢d-int)) example-sub-1 (λ ()))) (⊢d-sub ⊢d-int ≤d-int∞ (λ ()))
