module Counter.Algo where

open import Counter.Prelude
open import Counter.Common

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

  ⊢a-lam₁ : ∀ {Γ e A B C}
    → Γ , A ⊢a τ B ⇛ e ⇛ C
    ------------------------------------
    → Γ ⊢a τ (A ⇒ B) ⇛ ƛ e ⇛ A ⇒ C

  ⊢a-lam₂ : ∀ {Γ e₁ e A B H}
    → Γ ⊢a τ Top ⇛ e₁ ⇛ A
    → Γ , A ⊢a (H ⇧ 0) ⇛ e ⇛ B
      -------------------------------------
    → Γ ⊢a ⟦ e₁ ⟧⇒ H ⇛ ƛ e ⇛ A ⇒ B

----------------------------------------------------------------------
--                                                                  --
--                             Examples                             --
--                                                                  --
----------------------------------------------------------------------


_ : ∅ ⊢a τ Top ⇛ ((ƛ ` 0 · (lit 1)) ⦂ (Int ⇒ Int) ⇒ Int) · (ƛ ` 0) ⇛ Int
_ = ⊢a-app (⊢a-ann (⊢a-lam₁ (⊢a-app (⊢a-var Z proof-sub1))) proof-sub2)
  where
    proof-sub1 : ∅ , Int ⇒ Int ⊢a Int ⇒ Int ≤ ⟦ lit 1 ⟧⇒ τ Int
    proof-sub1 = ≤a-hint (⊢a-lit ≤a-int) ≤a-int
    proof-sub2 : ∅ ⊢a (Int ⇒ Int) ⇒ Int ≤ ⟦ ƛ ` 0 ⟧⇒ τ Top
    proof-sub2 = ≤a-hint (⊢a-lam₁ (⊢a-var Z ≤a-int)) ≤a-top

----------------------------------------------------------------------
--+                                                                +--
--+                           Transform                            +--
--+                                                                +--
----------------------------------------------------------------------

_▻_ : Term → List Term → Term
e ▻ [] = e
e₁ ▻ (e₂ ∷ es) = (e₁ · e₂) ▻ es

{-

--------------
e ▻ [] ~> e


(e₁ · e₂) ▻ es ~> e
----------------------
e₁ ▻ (e₂ ∷ es) ~> e

-}

{-
transform : ∀ {Γ H e A}
  → Γ ⊢a H ⇛ e ⇛ A
  → Γ ⊢a τ (proj₁ (proj₂ (f H A))) ⇛ e ▻ proj₁ (f H A) ⇛ proj₂ (proj₂ (f H A))
-}

infix 4 ❪_,_❫↣❪_,_,_,_❫

data ❪_,_❫↣❪_,_,_,_❫ : Hint → Type → List Term → Type → List Type → Type → Set where
  none : ∀ {A B}
    → ❪ τ A , B ❫↣❪ [] , A , [] , B ❫

  have : ∀ {e H A B es A' B' Bs}
    → ❪ H , B ❫↣❪ es , A' , Bs , B' ❫
    → ❪ ⟦ e ⟧⇒ H , A ⇒ B ❫↣❪ e ∷ es , A' , A ∷ Bs , B' ❫

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
