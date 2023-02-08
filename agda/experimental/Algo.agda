{-# OPTIONS --allow-unsolved-metas #-}
module Algo where

open import Data.Nat using (ℕ)
open import Data.String using (String; _≟_)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl; cong; sym)
open import Data.Product using (_×_; proj₁; proj₂; ∃; ∃-syntax) renaming (_,_ to ⟨_,_⟩)
open import Data.Empty using (⊥; ⊥-elim)
open import Relation.Nullary using (¬_; Dec; yes; no)
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
  ≤a-hint : ∀ {Γ A B H e}
    → Γ ⊢a τ A ⇛ e ⇛ A
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

  ⊢a-ann : ∀ {Γ e H A}
    → Γ ⊢a τ A ⇛ e ⇛ A
    → Γ ⊢a A ≤ H
    ---------------------
    → Γ ⊢a H ⇛ e ⦂ A ⇛ A

  ⊢a-lam₁ : ∀ {Γ e₁ e x A B H}
    → Γ ⊢a τ Top ⇛ e₁ ⇛ A
    → Γ , x ⦂ A ⊢a H ⇛ e ⇛ B
    -------------------------------------
    → Γ ⊢a ⟦ e₁ ⟧⇒ H ⇛ ƛ x ⇒ e ⇛ A ⇒ B

  ⊢a-lam₂ : ∀ {Γ x e A B C}
    → Γ , x ⦂ A ⊢a τ B ⇛ e ⇛ C
    ------------------------------------
    → Γ ⊢a τ (A ⇒ B) ⇛ ƛ x ⇒ e ⇛ A ⇒ C

----------------------------------------------------------------------
--                                                                  --
--                             Examples                             --
--                                                                  --
----------------------------------------------------------------------


_ : ∅ ⊢a τ Top ⇛ (ƛ "x" ⇒ ` "x") · lit 1 ⇛ Int
_ = ⊢a-app (⊢a-lam₁ (⊢a-lit ≤a-top) (⊢a-var Z ≤a-top))

_ : ∅ ⊢a τ Top ⇛ ((ƛ "f" ⇒ ` "f" · (lit 1)) ⦂ (Int ⇒ Int) ⇒ Int) · (ƛ "x" ⇒ ` "x") ⇛ Int
_ = ⊢a-app (⊢a-ann (⊢a-lam₂ (⊢a-app (⊢a-var Z proof-sub1))) proof-sub2)
  where
    proof-sub1 : ∅ , "f" ⦂ Int ⇒ Int ⊢a Int ⇒ Int ≤ ⟦ lit 1 ⟧⇒ τ Int
    proof-sub1 = ≤a-hint (⊢a-lit ≤a-int) ≤a-int
    proof-sub2 : ∅ ⊢a (Int ⇒ Int) ⇒ Int ≤ ⟦ ƛ "x" ⇒ ` "x" ⟧⇒ τ Top
    proof-sub2 = ≤a-hint (⊢a-lam₂ (⊢a-var Z ≤a-int)) ≤a-top


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
--                         Weakening Lemma                          --
--                                                                  --
----------------------------------------------------------------------

ext : ∀ {Γ Δ}
  → (∀ {x A} → Γ ∋ x ⦂ A → Δ ∋ x ⦂ A)
  → (∀ {x y A B} → Γ , y ⦂ B ∋ x ⦂ A → Δ , y ⦂ B ∋ x ⦂ A)
ext ρ Z           =  Z
ext ρ (S x≢y ∋x)  =  S x≢y (ρ ∋x)

_ : ∅ , "x" ⦂ Int ∋ "x" ⦂ Int
_ = Z

_ : ∅ , "x" ⦂ Int , "y" ⦂ Int , "x" ⦂ Top ∋ "x" ⦂ Top
_ = Z

≤a-rename : ∀ {Γ Δ}
  → (∀ {x A} → Γ ∋ x ⦂ A → Δ ∋ x ⦂ A)
  → (∀ {A B} → Γ ⊢a A ≤ B → Δ ⊢a A ≤ B)

⊢a-rename : ∀ {Γ Δ}
  → (∀ {x A} → Γ ∋ x ⦂ A → Δ ∋ x ⦂ A)
  → (∀ {e A B} → Γ ⊢a B ⇛ e ⇛ A → Δ ⊢a B ⇛ e ⇛ A)

≤a-rename = {!!}
⊢a-rename = {!!}

----------------------------------------------------------------------
--+                                                                +--
--+                           Transform                            +--
--+                                                                +--
----------------------------------------------------------------------

⊢a-transform : ∀ {Γ H A B C e e'}
  → Γ ⊢a H ⇛ e ⇛ A
  → Γ ⊢a τ B ⇛ e' ⇛ C
⊢a-transform {H = τ x} ⊢a = {!!}
⊢a-transform {H = ⟦ x ⟧⇒ H} (⊢a-var x₁ x₂) = {!!}
⊢a-transform {H = ⟦ x ⟧⇒ H} (⊢a-app ⊢a) = {!!}
⊢a-transform {H = ⟦ x ⟧⇒ H} (⊢a-ann ⊢a x₁) = {!!}
⊢a-transform {H = ⟦ x ⟧⇒ H} (⊢a-lam₁ ⊢a ⊢a₁) = {!!}


----------------------------------------------------------------------
--+                                                                +--
--+                       Typing & Subtyping                       +--
--+                                                                +--
----------------------------------------------------------------------

{-

⊢a-hint-self : ∀ {Γ e A}
  → Γ ⊢a τ Top ⇛ e ⇛ A
  → Γ ⊢a τ A ⇛ e ⇛ A
⊢a-hint-self (⊢a-lit x) = ⊢a-lit ≤a-int
⊢a-hint-self (⊢a-var x x₁) = ⊢a-var x ≤a-refl-h
⊢a-hint-self (⊢a-app ⊢a) = ⊢a-app {!!}
⊢a-hint-self (⊢a-ann ⊢a x) = ⊢a-ann ⊢a ≤a-refl-h

-}

-- a general version
⊢a-hint-self : ∀ {Γ e H A}
  → Γ ⊢a H ⇛ e ⇛ A
  → Γ ⊢a τ A ⇛ e ⇛ A
⊢a-hint-self (⊢a-lit x) = ⊢a-lit ≤a-int
⊢a-hint-self (⊢a-var x x₁) = ⊢a-var x ≤a-refl-h
⊢a-hint-self (⊢a-app ⊢a) = ⊢a-app {!⊢a-hint-self ⊢a!}
⊢a-hint-self (⊢a-ann ⊢a x) = ⊢a-ann ⊢a ≤a-refl-h
⊢a-hint-self (⊢a-lam₁ ⊢a ⊢a₁) = {!!}
⊢a-hint-self (⊢a-lam₂ ⊢a) = {!!}


⊢a-to-≤a : ∀ {Γ e A H}
  → Γ ⊢a H ⇛ e ⇛ A
  → Γ ⊢a A ≤ H
⊢a-to-≤a (⊢a-lit x) = x
⊢a-to-≤a (⊢a-var x x₁) = x₁
⊢a-to-≤a (⊢a-app ⊢a) = {!⊢a-to-≤a ⊢a!}
⊢a-to-≤a (⊢a-ann ⊢a x) = x
⊢a-to-≤a (⊢a-lam₁ ⊢a ⊢a₁) = {!!}
⊢a-to-≤a (⊢a-lam₂ ⊢a) = ≤a-arr ≤a-refl-h {!⊢a-to-≤a ⊢a!}



