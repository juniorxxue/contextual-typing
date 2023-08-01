module SubGen.Algo where

open import SubGen.Prelude
open import SubGen.Common

infixr 8 ⟦_⟧⇒_

data Hint : Set where
  τ : Type → Hint
  ⟦_⟧⇒_ : Term → Hint → Hint

infixl 7 _⇧_
_⇧_ : Hint → ℕ → Hint
τ A ⇧ n = τ A
(⟦ e ⟧⇒ H) ⇧ n = ⟦ e ↑ n ⟧⇒ (H ⇧ n)

infixl 7 _⇩_
_⇩_ : Hint → ℕ → Hint
τ A ⇩ n = τ A
(⟦ e ⟧⇒ H) ⇩ n = ⟦ e ↓ n ⟧⇒ (H ⇩ n)

data pv : Term → Set where

  pv-i : ∀ {n}
    → pv (lit n)

  pv-var : ∀ {x}
    → pv (` x)

  pv-ann : ∀ {e A}
    → pv (e ⦂ A)

↑-pv-prv : ∀ {p n}
  → pv p
  → pv (p ↑ n)
↑-pv-prv pv-i = pv-i
↑-pv-prv pv-var = pv-var
↑-pv-prv pv-ann = pv-ann

↓-pv-prv : ∀ {p n}
  → pv p
  → pv (p ↓ n)
↓-pv-prv pv-i = pv-i
↓-pv-prv pv-var = pv-var
↓-pv-prv pv-ann = pv-ann
  
infix 4 _⊢a_≤_⇝_
infix 4 _⊢a_⇛_⇛_ 

data _⊢a_≤_⇝_ : Context → Type → Hint → Type → Set
data _⊢a_⇛_⇛_ : Context → Hint → Term → Type → Set

data _⊢a_≤_⇝_ where
  ≤a-int : ∀ {Γ}
    → Γ ⊢a Int ≤ τ Int ⇝ Int
  ≤a-base : ∀ {Γ n}
    → Γ ⊢a * n ≤ τ (* n) ⇝ (* n)
  ≤a-top : ∀ {Γ A}
    → Γ ⊢a A ≤ τ Top ⇝ A
  ≤a-arr : ∀ {Γ A A' B C D D'}
    → Γ ⊢a C ≤ τ A ⇝ A'
    → Γ ⊢a B ≤ τ D ⇝ D'
    ---------------------------
    → Γ ⊢a (A ⇒ B) ≤ τ (C ⇒ D) ⇝ (A' ⇒ D')
  ≤a-hint : ∀ {Γ A B C H e D}
    → Γ ⊢a τ A ⇛ e ⇛ C
    → Γ ⊢a B ≤ H ⇝ D
    ------------------------
    → Γ ⊢a A ⇒ B ≤ ⟦ e ⟧⇒ H ⇝ (A ⇒ D)
  ≤a-and-l : ∀ {Γ A B H C}
    → Γ ⊢a A ≤ H ⇝ C
    → Γ ⊢a A & B ≤ H ⇝ C
  ≤a-and-r : ∀ {Γ A B H C}
    → Γ ⊢a B ≤ H ⇝ C
    → Γ ⊢a A & B ≤ H ⇝ C
  ≤a-and : ∀ {Γ A B B' C C'}
    → Γ ⊢a A ≤ τ B ⇝ B'
    → Γ ⊢a A ≤ τ C ⇝ C'
    → Γ ⊢a A ≤ τ (B & C) ⇝ (B' & C')

data _⊢a_⇛_⇛_ where

  ⊢a-lit : ∀ {Γ n}
    -----------------------
    → Γ ⊢a τ Top ⇛ lit n ⇛ Int

  ⊢a-var : ∀ {Γ A x}
    → Γ ∋ x ⦂ A
    -------------------
    → Γ ⊢a τ Top ⇛ ` x ⇛ A

  ⊢a-app : ∀ {Γ e₁ e₂ H A B}
    → Γ ⊢a ⟦ e₂ ⟧⇒ H ⇛ e₁ ⇛ A ⇒ B
    ----------------------------------
    → Γ ⊢a H ⇛ e₁ · e₂ ⇛ B

  ⊢a-ann : ∀ {Γ e A B}
    → Γ ⊢a τ A ⇛ e ⇛ B
    ---------------------
    → Γ ⊢a τ Top ⇛ e ⦂ A ⇛ A

  ⊢a-lam₁ : ∀ {Γ e A B C}
    → Γ , A ⊢a τ B ⇛ e ⇛ C
    ------------------------------------
    → Γ ⊢a τ (A ⇒ B) ⇛ ƛ e ⇛ A ⇒ C

  ⊢a-lam₂ : ∀ {Γ e₁ e A B H}
    → Γ ⊢a τ Top ⇛ e₁ ⇛ A
    → Γ , A ⊢a (H ⇧ 0) ⇛ e ⇛ B
      -------------------------------------
    → Γ ⊢a ⟦ e₁ ⟧⇒ H ⇛ ƛ e ⇛ A ⇒ B

  ⊢a-lam₃ : ∀ {Γ e A B C D}
    → Γ ⊢a τ A ⇛ ƛ e ⇛ C
    → Γ ⊢a τ B ⇛ ƛ e ⇛ D
    → Γ ⊢a τ (A & B) ⇛ ƛ e ⇛ C & D

  ⊢a-sub : ∀ {Γ H p A B}
    → pv p
    → Γ ⊢a τ Top ⇛ p ⇛ A
    → Γ ⊢a A ≤ H ⇝ B
    → H ≢ τ Top
    → Γ ⊢a H ⇛ p ⇛ B

----------------------------------------------------------------------
--                                                                  --
--                             Examples                             --
--                                                                  --
----------------------------------------------------------------------

≤a-refl : ∀ {Γ A}
  → Γ ⊢a A ≤ τ A ⇝ A
≤a-refl {A = Int} = ≤a-int
≤a-refl {A = * x} = ≤a-base
≤a-refl {A = Top} = ≤a-top
≤a-refl {A = A ⇒ A₁} = ≤a-arr ≤a-refl ≤a-refl
≤a-refl {A = A & B} = ≤a-and (≤a-and-l ≤a-refl) (≤a-and-r ≤a-refl)

----------------------------------------------------------------------
--+                                                                +--
--+                           Transform                            +--
--+                                                                +--
----------------------------------------------------------------------

_▻_ : Term → List Term → Term
e ▻ [] = e
e₁ ▻ (e₂ ∷ es) = (e₁ · e₂) ▻ es

infix 4 ❪_,_❫↣❪_,_,_,_❫

data ❪_,_❫↣❪_,_,_,_❫ : Hint → Type → List Term → Type → List Type → Type → Set where
  none : ∀ {A B}
    → ❪ τ A , B ❫↣❪ [] , A , [] , B ❫

  have : ∀ {e H A B es A' B' Bs}
    → ❪ H , B ❫↣❪ es , A' , Bs , B' ❫
    → ❪ ⟦ e ⟧⇒ H , A ⇒ B ❫↣❪ e ∷ es , A' , A ∷ Bs , B' ❫

≤a-determinism : ∀ {Γ H A B C}
  → H ≢ τ Top
  → Γ ⊢a A ≤ H ⇝ B
  → Γ ⊢a A ≤ H ⇝ C
  → B ≡ C
≤a-determinism neq ≤a-int ≤a-int = refl
≤a-determinism neq ≤a-base ≤a-base = refl
≤a-determinism neq ≤a-top ≤C = ⊥-elim (neq refl)
≤a-determinism neq (≤a-arr ≤B ≤B₁) (≤a-arr ≤C ≤C₁) = {!≤a-determinism ? ≤B ≤C!} -- easy
≤a-determinism neq (≤a-hint ⊢1 ≤B) (≤a-hint ⊢2 ≤C) = {!!} -- easy
≤a-determinism neq (≤a-and-l ≤B) ≤C = {!!}
≤a-determinism neq (≤a-and-r ≤B) ≤C = {!!}
≤a-determinism neq (≤a-and ≤B ≤B₁) (≤a-and-l ≤C) = {!!}
≤a-determinism neq (≤a-and ≤B ≤B₁) (≤a-and-r ≤C) = {!!}
≤a-determinism neq (≤a-and ≤B ≤B₁) (≤a-and ≤C ≤C₁) = {!!}


⊢a-determinism : ∀ {Γ H e A B}
  → Γ ⊢a H ⇛ e ⇛ A
  → Γ ⊢a H ⇛ e ⇛ B
  → A ≡ B
⊢a-determinism ⊢a-lit ⊢a-lit = refl
⊢a-determinism ⊢a-lit (⊢a-sub x ⊢2 x₁ x₂) = {!!} -- easy
⊢a-determinism (⊢a-var x) ⊢2 = {!!} -- easy

⊢a-determinism (⊢a-app ⊢1) (⊢a-app ⊢2) = {!⊢a-determinism ⊢1 ⊢2!} -- easy

⊢a-determinism (⊢a-ann ⊢1) (⊢a-ann ⊢2) = refl
⊢a-determinism (⊢a-ann ⊢1) (⊢a-sub x ⊢2 x₁ x₂) = {!!} -- easy

⊢a-determinism (⊢a-lam₁ ⊢1) (⊢a-lam₁ ⊢2) = {!⊢a-determinism ⊢1 ⊢2 !}  -- easy
⊢a-determinism (⊢a-lam₂ ⊢1 ⊢3) (⊢a-lam₂ ⊢2 ⊢4) rewrite ⊢a-determinism ⊢1 ⊢2 = {!⊢a-determinism ⊢3 ⊢4!} -- easy
⊢a-determinism (⊢a-lam₃ ⊢1 ⊢3) (⊢a-lam₃ ⊢2 ⊢4) rewrite ⊢a-determinism ⊢1 ⊢2 | ⊢a-determinism ⊢3 ⊢4 = refl
⊢a-determinism (⊢a-sub x ⊢1 x₁ x₂) ⊢a-lit = {!!}
⊢a-determinism (⊢a-sub x ⊢1 x₁ x₂) (⊢a-var x₃) = {!!}
⊢a-determinism (⊢a-sub x ⊢1 x₁ x₂) (⊢a-ann ⊢2) = {!!} -- all absurds
⊢a-determinism (⊢a-sub x ⊢1 x₁ x₂) (⊢a-sub x₃ ⊢2 x₄ x₅) rewrite ⊢a-determinism ⊢1 ⊢2 = {!!}
