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
  ≤a-arr : ∀ {Γ A B C D}
    → Γ ⊢a C ≤ τ A ⇝ A
    → Γ ⊢a B ≤ τ D ⇝ D
    ---------------------------
    → Γ ⊢a (A ⇒ B) ≤ τ (C ⇒ D) ⇝ (C ⇒ D)
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
  ≤a-and : ∀ {Γ A B C}
    → Γ ⊢a A ≤ τ B ⇝ B
    → Γ ⊢a A ≤ τ C ⇝ C
    → Γ ⊢a A ≤ τ (B & C) ⇝ (B & C)

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

  ⊢a-sub : ∀ {Γ H p A B}
    → pv p
    → Γ ⊢a τ Top ⇛ p ⇛ A
    → Γ ⊢a A ≤ H ⇝ B
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

_ : ∅ ⊢a τ Top ⇛ ((ƛ ` 0 · (lit 1)) ⦂ (Int ⇒ Int) ⇒ Int) · (ƛ ` 0) ⇛ Int
_ = ⊢a-app (⊢a-sub pv-ann (⊢a-ann (⊢a-lam₁ (⊢a-app (⊢a-sub pv-var (⊢a-var Z) (≤a-hint (⊢a-sub pv-i ⊢a-lit ≤a-int) ≤a-int)))))
           (≤a-hint (⊢a-lam₁ (⊢a-sub pv-var (⊢a-var Z) ≤a-int)) ≤a-top))

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
