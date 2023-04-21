module Algo where

open import Data.Nat using (ℕ)
open import Data.String using (String; _≟_)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl; cong; sym)
open import Data.Product using (_×_; proj₁; proj₂; ∃; ∃-syntax) renaming (_,_ to ⟨_,_⟩)
open import Data.Empty using (⊥; ⊥-elim)
open import Relation.Nullary using (¬_; Dec; yes; no)

open import Data.List using (List; []; _∷_; _++_; length; reverse; map; foldr; downFrom)

open import Common

infixr 8 ⟦_⟧⇒_

data Hint : Set where
  τ : Type → Hint
  ⟦_⟧⇒_ : Term → Hint → Hint
  
infix 4 _⊢a_≤_
infix 4 _⊢a_⇛_⇛_ 

data _⊢a_≤_ : Context → Type → Hint → Set
data _⊢a_⇛_⇛_ : Context → Hint → Term → Type → Set

data _⊢a_≤_ where
  ≤a-int : ∀ {Γ}
    → Γ ⊢a Int ≤ τ Int
  ≤a-top : ∀ {Γ A}
    → Γ ⊢a A ≤ τ Top
  ≤a-arr : ∀ {Γ A B C D}
    → Γ ⊢a C ≤ τ A
    → Γ ⊢a B ≤ τ D
    ---------------------------
    → Γ ⊢a (A ⇒ B) ≤ τ (C ⇒ D)
  ≤a-hint : ∀ {Γ A B C H e}
    → Γ ⊢a τ A ⇛ e ⇛ C
    → Γ ⊢a B ≤ H
    ------------------------
    → Γ ⊢a A ⇒ B ≤ ⟦ e ⟧⇒ H

data _⊢a_⇛_⇛_ where

  ⊢a-lit : ∀ {Γ n H}
    → Γ ⊢a Int ≤ H
    -----------------------
    → Γ ⊢a H ⇛ lit n ⇛ Int

  ⊢a-var : ∀ {Γ A H x}
    → Γ ∋ x ⦂ A
    → Γ ⊢a A ≤ H
    -------------------
    → Γ ⊢a H ⇛ ` x ⇛ A

  ⊢a-app : ∀ {Γ e₁ e₂ H A B}
    → Γ ⊢a ⟦ e₂ ⟧⇒ H ⇛ e₁ ⇛ A ⇒ B
    ----------------------------------
    → Γ ⊢a H ⇛ e₁ · e₂ ⇛ B

  ⊢a-ann : ∀ {Γ e H A B}
    → Γ ⊢a τ A ⇛ e ⇛ B
    → Γ ⊢a A ≤ H
    ---------------------
    → Γ ⊢a H ⇛ e ⦂ A ⇛ A

  ⊢a-lam : ∀ {Γ e A B C}
    → Γ , A ⊢a τ B ⇛ e ⇛ C
    ------------------------------------
    → Γ ⊢a τ (A ⇒ B) ⇛ ƛ e ⇛ A ⇒ C
    
----------------------------------------------------------------------
--                                                                  --
--                            Subtyping                             --
--                                                                  --
----------------------------------------------------------------------

≤a-refl-h : ∀ {A Γ}
  → Γ ⊢a A ≤ τ A
≤a-refl-h {A = Int} = ≤a-int
≤a-refl-h {A = Top} = ≤a-top
≤a-refl-h {A = A ⇒ A₁} = ≤a-arr ≤a-refl-h ≤a-refl-h

----------------------------------------------------------------------
--                                                                  --
--                             Examples                             --
--                                                                  --
----------------------------------------------------------------------


_ : ∅ ⊢a τ Top ⇛ ((ƛ ` 0 · (lit 1)) ⦂ (Int ⇒ Int) ⇒ Int) · (ƛ ` 0) ⇛ Int
_ = ⊢a-app (⊢a-ann (⊢a-lam (⊢a-app (⊢a-var Z proof-sub1))) proof-sub2)
  where
    proof-sub1 : ∅ , Int ⇒ Int ⊢a Int ⇒ Int ≤ ⟦ lit 1 ⟧⇒ τ Int
    proof-sub1 = ≤a-hint (⊢a-lit ≤a-int) ≤a-int
    proof-sub2 : ∅ ⊢a (Int ⇒ Int) ⇒ Int ≤ ⟦ ƛ ` 0 ⟧⇒ τ Top
    proof-sub2 = ≤a-hint (⊢a-lam (⊢a-var Z ≤a-int)) ≤a-top


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

▻-fold : ∀ {e₁ e₂ : Term} {es : List Term}
  → (e₁ · e₂) ▻ es ≡ e₁ ▻ (e₂ ∷ es)
▻-fold = refl

----------------------------------------------------------------------
--+                                                                +--
--+                       Typing & Subtyping                       +--
--+                                                                +--
----------------------------------------------------------------------

-- inversion lemmas

≤a-hint-inv₁ : ∀ {Γ H A B e}
  → Γ ⊢a A ⇒ B ≤ ⟦ e ⟧⇒ H
  → ∃[ C ] Γ ⊢a τ A ⇛ e ⇛ C
≤a-hint-inv₁ (≤a-hint {C = C} x ≤a) = ⟨ C , x ⟩

≤a-hint-inv₂ : ∀ {Γ H A B e}
  → Γ ⊢a A ⇒ B ≤ ⟦ e ⟧⇒ H
  → Γ ⊢a B ≤ H
≤a-hint-inv₂ (≤a-hint x ≤) = ≤

≤a-τ-weaken : ∀ {Γ A B C}
  → Γ , A ⊢a B ≤ τ C
  → Γ ⊢a B ≤ τ C
≤a-τ-weaken ≤a-int = ≤a-int
≤a-τ-weaken ≤a-top = ≤a-top
≤a-τ-weaken (≤a-arr B≤C B≤C₁) = ≤a-arr (≤a-τ-weaken B≤C) (≤a-τ-weaken B≤C₁)

⊢a-to-≤a : ∀ {Γ e A H}
  → Γ ⊢a H ⇛ e ⇛ A
  → Γ ⊢a A ≤ H
⊢a-to-≤a (⊢a-lit x) = x
⊢a-to-≤a (⊢a-var x x₁) = x₁
⊢a-to-≤a (⊢a-app ⊢e) = ≤a-hint-inv₂ (⊢a-to-≤a ⊢e)
⊢a-to-≤a (⊢a-ann ⊢e x) = x
⊢a-to-≤a (⊢a-lam ⊢e) = ≤a-arr ≤a-refl-h (≤a-τ-weaken ind-e)
  where ind-e = ⊢a-to-≤a ⊢e
