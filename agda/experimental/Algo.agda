{-# OPTIONS --allow-unsolved-metas #-}
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
    → Γ ⊢a B ≤ H
    ----------------------------------
    → Γ ⊢a H ⇛ e₁ · e₂ ⇛ B

  ⊢a-ann : ∀ {Γ e H A B}
    → Γ ⊢a τ A ⇛ e ⇛ B
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
_ = ⊢a-app (⊢a-lam₁ (⊢a-lit ≤a-top) (⊢a-var Z ≤a-top)) {!!}

_ : ∅ ⊢a τ Top ⇛ ((ƛ "f" ⇒ ` "f" · (lit 1)) ⦂ (Int ⇒ Int) ⇒ Int) · (ƛ "x" ⇒ ` "x") ⇛ Int
_ = ⊢a-app (⊢a-ann (⊢a-lam₂ (⊢a-app (⊢a-var Z proof-sub1) {!!})) proof-sub2) {!!}
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

f : Hint → Type → List Term × Type × Type
f (τ A) B = ⟨ [] , ⟨ A , B ⟩ ⟩
f (⟦ e ⟧⇒ H) (A ⇒ B) with f H B
... | ⟨ es , ⟨  A' , B' ⟩ ⟩ = ⟨ (e ∷ es) , ⟨ A' , B' ⟩ ⟩
f (⟦ e ⟧⇒ H) Int = ⟨ [] , ⟨ Top , Top ⟩ ⟩ -- by inversion of algo, we will never reach the following results
f (⟦ e ⟧⇒ H) Top = ⟨ [] , ⟨ Top , Top ⟩ ⟩

_▻_ : Term → List Term → Term
e ▻ [] = e
e₁ ▻ (e₂ ∷ es) = (e₁ · e₂) ▻ es

{-

transform : ∀ {Γ H e A}
  → Γ ⊢a H ⇛ e ⇛ A
  → Γ ⊢a τ (proj₁ (proj₂ (f H A))) ⇛ e ▻ proj₁ (f H A) ⇛ proj₂ (proj₂ (f H A))
-}

infix 4 ⦅_,_⦆↣⦅_,_,_,_⦆

data ⦅_,_⦆↣⦅_,_,_,_⦆ : Hint → Type → List Term → Type → List Type → Type → Set where
  none : ∀ {A B}
    → ⦅ τ A , B ⦆↣⦅ [] , A , [] , B ⦆

  have : ∀ {e H A B es A' B' Bs}
    → ⦅ H , B ⦆↣⦅ es , A' , Bs , B' ⦆
    → ⦅ ⟦ e ⟧⇒ H , A ⇒ B ⦆↣⦅ e ∷ es , A' , A ∷ Bs , B' ⦆

absurd1 : ∀ {Γ x e} (H : Hint)
  → Γ ⊢a ⟦ x ⟧⇒ H ⇛ e ⇛ Top
  → ⊥
absurd1 = {!!}

{-

split-true : ∀ {Γ H e A}
  → Γ ⊢a H ⇛ e ⇛ A
  → ∃[ es ] ∃[ B ] ∃[ A' ] split H A es B A'
split-true {H = τ x} {A = A} ⊢a = ⟨ [] , ⟨ x , ⟨ A , none ⟩ ⟩ ⟩
split-true {H = ⟦ x ⟧⇒ H} {A = Int} ⊢a = ⟨ {!!} , {!!} ⟩
split-true {H = ⟦ x ⟧⇒ H} {A = Top} ⊢a = ⟨ {!!} , {!!} ⟩
split-true {H = ⟦ x ⟧⇒ H} {e = e} {A = A ⇒ A₁} ⊢a with split-true (⊢a-app ⊢a {!!})
... | ⟨ fst , ⟨ fst₁ , ⟨ fst₂ , snd ⟩ ⟩ ⟩ = ⟨  x ∷ fst , ⟨ fst₁ , ⟨ fst₂ ,  have {e = x} {A = A} snd ⟩ ⟩ ⟩

-}

▻-fold : ∀ {e₁ e₂ : Term} {es : List Term}
  → (e₁ · e₂) ▻ es ≡ e₁ ▻ (e₂ ∷ es)
▻-fold = refl

{-

transform : ∀ {Γ H e A es B A'}
  → Γ ⊢a H ⇛ e ⇛ A
  → split H A es B A'
  → Γ ⊢a τ B ⇛ e ▻ es ⇛ A'
transform ⊢a none = ⊢a
transform ⊢a (have spl) = transform ⊢a {!split-true ⊢a!}

-}

----------------------------------------------------------------------
--+                                                                +--
--+                       Typing & Subtyping                       +--
--+                                                                +--
----------------------------------------------------------------------

-- define a relation describing the "information level"
-- A -> B
-- ⊂ A
-- ⊂ A -> Top
-- ⊂ ⟦ e ⟧ -> Top
-- ⊂ Top

-- unapp from a normal type

{-
unapp-1 : ∀ {Γ A B C D e₁ e₂}
  → Γ ⊢a τ (A ⇒ B) ⇛ e₁ ⇛ C ⇒ D
  → Γ ⊢a τ A ⇛ e₁ ⇛ A
  → Γ ⊢a τ B ⇛ e₁ · e₂ ⇛ D
-}

-- a general version
⊢a-hint-self : ∀ {Γ e H A}
  → Γ ⊢a H ⇛ e ⇛ A
  → Γ ⊢a τ A ⇛ e ⇛ A
⊢a-hint-self (⊢a-lit x) = ⊢a-lit ≤a-int
⊢a-hint-self (⊢a-var x x₁) = {!!}
⊢a-hint-self (⊢a-app ⊢a x) = {!!}
⊢a-hint-self (⊢a-ann ⊢a x) = {!!}
⊢a-hint-self (⊢a-lam₁ ⊢a ⊢a₁) = {!!}
⊢a-hint-self (⊢a-lam₂ ⊢a) = {!!}

-- less information

⊢a-to-≤a : ∀ {Γ e A H}
  → Γ ⊢a H ⇛ e ⇛ A
  → Γ ⊢a A ≤ H
⊢a-to-≤a (⊢a-lit x) = x
⊢a-to-≤a (⊢a-var x x₁) = x₁
⊢a-to-≤a (⊢a-app ⊢a ≤) = ≤
⊢a-to-≤a (⊢a-ann ⊢a x) = x
⊢a-to-≤a (⊢a-lam₁ ⊢a ⊢a₁) = ≤a-hint {!!} {!⊢a-to-≤a ⊢a₁!}
⊢a-to-≤a (⊢a-lam₂ ⊢a) = ≤a-arr ≤a-refl-h {!⊢a-to-≤a ⊢a!}

ty-imp-sub : ∀ {Γ A e B}
  → Γ ⊢a τ A ⇛ e ⇛ B
  → Γ ⊢a B ≤ τ A
ty-imp-sub = {!!}


-- type preseveration under subtyping

ty-pres : ∀ {Γ H e A B}
  → Γ ⊢a H ⇛ e ⇛ A
  → Γ ⊢a B ≤ H
  → Γ ⊢a τ B ⇛ e ⇛ A
ty-pres (⊢a-lit x) ≤a-int = ⊢a-lit x
ty-pres (⊢a-lit x) ≤a-top = ⊢a-lit {!!}
ty-pres (⊢a-var x x₁) ≤ = {!!}
ty-pres (⊢a-app ⊢a x) ≤ = {!!}
ty-pres (⊢a-ann ⊢a x) ≤ = {!!}
ty-pres (⊢a-lam₁ ⊢a ⊢a₁) ≤ = {!!}
ty-pres (⊢a-lam₂ ⊢a) ≤ = {!!}
