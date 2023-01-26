{-# OPTIONS --allow-unsolved-metas #-}
module Algo where

open import Data.Nat using (ℕ)
open import Data.String using (String)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl)
open import Data.Product using (_×_; proj₁; proj₂; ∃; ∃-syntax) renaming (_,_ to ⟨_,_⟩)
open import Data.Empty using (⊥; ⊥-elim)
open import Relation.Nullary using (¬_)
open import Common

infixr 8 _*⇒_
infixr 8 ⟦_⟧

data Hype : Set where
  Hnt : Hype
  Hop : Hype
  _*⇒_  : Hype → Hype → Hype
  ⟦_⟧ : Term → Hype

infix 4 _⊢a_≤_
infix 4 _⊢a_⇛_⇛_ 

data _⊢a_≤_ : Context → Hype → Hype → Set
data _⊢a_⇛_⇛_ : Context → Hype → Term → Type → Set

infix 5 _⊢a_

data _⊢a_ : Context → Hype → Set where
  wf-int : ∀ {Γ}
    → Γ ⊢a Hnt

  wf-top : ∀ {Γ}
    → Γ ⊢a Hop

  wf-arr : ∀ {Γ A B}
    → Γ ⊢a A
    → Γ ⊢a B
    → Γ ⊢a A *⇒ B

  wf-hole : ∀ {Γ e}
    → Γ ⊢ e
    → Γ ⊢a ⟦ e ⟧


h : Type → Hype
h Int = Hnt
h Top = Hop
h (A ⇒ B) = (h A) *⇒ (h B)

-- unh : Hype → Type
-- unh Hnt = Int
-- unh Hop = Top
-- unh (A *⇒ B) = (unh A) ⇒ (unh B)

data _⊢a_≤_ where
  ≤a-int : ∀ {Γ}
    → Γ ⊢a Hnt ≤ Hnt
  ≤a-top : ∀ {Γ A}
    → Γ ⊢a A ≤ Hop
  ≤a-arr : ∀ {Γ A B C D}
    → Γ ⊢a C ≤ A
    → Γ ⊢a B ≤ D
    → Γ ⊢a (A *⇒ B) ≤ (C *⇒ D)
  ≤a-hole : ∀ {Γ A B e}
    → Γ ⊢a A ⇛ e ⇛ B
    → Γ ⊢a ⟦ e ⟧ ≤ A

data _⊢a_⇛_⇛_ where

  ⊢a-lit : ∀ {Γ A n}
    → Γ ⊢a Hnt ≤ A
    -----------------------
    → Γ ⊢a A ⇛ lit n ⇛ Int

  ⊢a-var : ∀ {Γ A B x}
    → Γ ∋ x ⦂ B
    → Γ ⊢a h B ≤ A
    -------------------
    → Γ ⊢a A ⇛ ` x ⇛ B

  ⊢a-app : ∀ {Γ e₁ e₂ A C D}
    → Γ ⊢a ⟦ e₂ ⟧ *⇒ A ⇛ e₁ ⇛ (C ⇒ D)
    ----------------------------------
    → Γ ⊢a A ⇛ e₁ · e₂ ⇛ D

  ⊢a-ann : ∀ {Γ e A B}
    → Γ ⊢a h B ⇛ e ⇛ B
    → Γ ⊢a h B ≤ A
    ---------------------
    → Γ ⊢a A ⇛ e ⦂ B ⇛ B

  ⊢a-lam₁ : ∀ {Γ e₁ e x A B C}
    → Γ ⊢a Hop ⇛ e₁ ⇛ A
    → Γ , x ⦂ A ⊢a B ⇛ e ⇛ C
    → Γ ⊢a B
    -------------------------------------
    → Γ ⊢a ⟦ e₁ ⟧ *⇒ B ⇛ ƛ x ⇒ e ⇛ A ⇒ C

  ⊢a-lam₂ : ∀ {Γ x e A B C}
    → Γ , x ⦂ A ⊢a B ⇛ e ⇛ C
    → Γ ⊢a B
    ------------------------------------
    → Γ ⊢a (h A) *⇒ B ⇛ ƛ x ⇒ e ⇛ A ⇒ C

----------------------------------------------------------------------
--                                                                  --
--                             Examples                             --
--                                                                  --
----------------------------------------------------------------------


_ : ∅ ⊢a Hop ⇛ (ƛ "x" ⇒ ` "x") · lit 1 ⇛ Int
_ = ⊢a-app (⊢a-lam₁ (⊢a-lit ≤a-top) (⊢a-var Z ≤a-top) wf-top)

_ : ∅ ⊢a Hop ⇛ ((ƛ "f" ⇒ ` "f" · (lit 1)) ⦂ (Int ⇒ Int) ⇒ Int) · (ƛ "x" ⇒ ` "x") ⇛ Int
_ = ⊢a-app (⊢a-ann (⊢a-lam₂ (⊢a-app (⊢a-var Z (≤a-arr (≤a-hole (⊢a-lit ≤a-int)) ≤a-int))) wf-int) (≤a-arr (≤a-hole (⊢a-lam₂ {A = Int} (⊢a-var Z ≤a-int) wf-int)) ≤a-top))


----------------------------------------------------------------------
--                                                                  --
--                           Well-formed                            --
--                                                                  --
----------------------------------------------------------------------


⊢a-to-wf : ∀ {Γ B e A}
  → Γ ⊢a B ⇛ e ⇛ A
  → Γ ⊢a B × Γ ⊢ e
⊢a-to-wf = {!!}  


----------------------------------------------------------------------
--                                                                  --
--                            Subtyping                             --
--                                                                  --
----------------------------------------------------------------------

≤a-refl-h : ∀ {A Γ}
  → Γ ⊢a h A ≤ h A
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

⊢-rename : ∀ {Γ Δ}
  → (∀ {x A} → Γ ∋ x ⦂ A → Δ ∋ x ⦂ A)
  → (∀ {e} → Γ ⊢ e → Δ ⊢ e)
⊢-rename ρ wf-lit = wf-lit
⊢-rename ρ (wf-var x) = wf-var (ρ x)
⊢-rename ρ (wf-lam ⊢) = wf-lam (⊢-rename (ext ρ) ⊢)
⊢-rename ρ (wf-app ⊢₁ ⊢₂) = wf-app (⊢-rename ρ ⊢₁) (⊢-rename ρ ⊢₂)
⊢-rename ρ (wf-ann ⊢) = wf-ann (⊢-rename ρ ⊢)

wf-rename : ∀ {Γ Δ}
  → (∀ {x A} → Γ ∋ x ⦂ A → Δ ∋ x ⦂ A)
  → (∀ {A} → Γ ⊢a A → Δ ⊢a A)
wf-rename ρ wf-int = wf-int
wf-rename ρ wf-top = wf-top
wf-rename ρ (wf-arr ⊢₁ ⊢₂) = wf-arr (wf-rename ρ ⊢₁) (wf-rename ρ ⊢₂)
wf-rename ρ (wf-hole x) = wf-hole (⊢-rename ρ x)

≤a-rename : ∀ {Γ Δ}
  → (∀ {x A} → Γ ∋ x ⦂ A → Δ ∋ x ⦂ A)
  → (∀ {A B} → Γ ⊢a A ≤ B → Δ ⊢a A ≤ B)

⊢a-rename : ∀ {Γ Δ}
  → (∀ {x A} → Γ ∋ x ⦂ A → Δ ∋ x ⦂ A)
  → (∀ {e A B} → Γ ⊢a B ⇛ e ⇛ A → Δ ⊢a B ⇛ e ⇛ A)

≤a-rename ρ ≤a-int = ≤a-int
≤a-rename ρ ≤a-top = ≤a-top
≤a-rename ρ (≤a-arr ≤a₁ ≤a₂) = ≤a-arr (≤a-rename ρ ≤a₁) (≤a-rename ρ ≤a₂)
≤a-rename ρ (≤a-hole ⊢a) = ≤a-hole (⊢a-rename ρ ⊢a)

⊢a-rename ρ (⊢a-lit ⊢a) = ⊢a-lit (≤a-rename ρ ⊢a)
⊢a-rename ρ (⊢a-var ≤a ∋x) = ⊢a-var (ρ ≤a) (≤a-rename ρ ∋x)
⊢a-rename ρ (⊢a-app ⊢a) = ⊢a-app (⊢a-rename ρ ⊢a)
⊢a-rename ρ (⊢a-ann ⊢a ≤a) = ⊢a-ann (⊢a-rename ρ ⊢a) (≤a-rename ρ ≤a)
⊢a-rename ρ (⊢a-lam₁ ⊢a₁ ⊢a₂ wf) = ⊢a-lam₁ (⊢a-rename ρ ⊢a₁) (⊢a-rename (ext ρ) ⊢a₂) (wf-rename ρ wf)
⊢a-rename ρ (⊢a-lam₂ ⊢a wf) = ⊢a-lam₂ (⊢a-rename (ext ρ) ⊢a) (wf-rename ρ wf)

-- weakening

⊢a-weaken : ∀ {Γ e A B}
  → ∅ ⊢a B ⇛ e ⇛ A
  → Γ ⊢a B ⇛ e ⇛ A
⊢a-weaken {Γ} ⊢e = ⊢a-rename ρ ⊢e
  where
  ρ : ∀ {z C}
    → ∅ ∋ z ⦂ C
    → Γ ∋ z ⦂ C
  ρ = λ ()

-- swap
≤a-swap : ∀ {Γ x y A B C D}
  → x ≢ y
  → Γ , y ⦂ B , x ⦂ A ⊢a C ≤ D
  → Γ , x ⦂ A , y ⦂ B ⊢a C ≤ D
≤a-swap {Γ} {x} {y} {A} {B} {C} {D} x≢y ≤ = ≤a-rename ρ ≤
  where
    ρ : ∀ {z D}
      → Γ , y ⦂ B , x ⦂ A ∋ z ⦂ D
      → Γ , x ⦂ A , y ⦂ B ∋ z ⦂ D
    ρ Z                   =  S x≢y Z
    ρ (S z≢x Z)           =  Z
    ρ (S z≢x (S z≢y ∋z))  =  S z≢y (S z≢x ∋z)

⊢a-swap : ∀ {Γ x y e A B C D}
  → x ≢ y
  → Γ , y ⦂ B , x ⦂ A ⊢a C ⇛ e ⇛ D
  → Γ , x ⦂ A , y ⦂ B ⊢a C ⇛ e ⇛ D
⊢a-swap {Γ} {x} {y} {e} {A} {B} {C} {D} x≢y ⊢ = ⊢a-rename ρ ⊢
  where
    ρ : ∀ {z D}
      → Γ , y ⦂ B , x ⦂ A ∋ z ⦂ D
      → Γ , x ⦂ A , y ⦂ B ∋ z ⦂ D
    ρ Z                   =  S x≢y Z
    ρ (S z≢x Z)           =  Z
    ρ (S z≢x (S z≢y ∋z))  =  S z≢y (S z≢x ∋z)


----------------------------------------------------------------------
--                                                                  --
--                       Strengthening Lemma                        --
--                                                                  --
----------------------------------------------------------------------


∋-strengthen : ∀ {Γ x y A B}
  → Γ , y ⦂ A ∋ x ⦂ B
  → y ≢ x
  → Γ ∋ x ⦂ B
∋-strengthen Z neq = ⊥-elim (neq refl)
∋-strengthen (S x ∋) neq = ∋

≤-strengthen : ∀ {Γ x A B C}
  → (Γ , x ⦂ A) ⊢a C ≤ B
  → Γ ⊢a C
  → Γ ⊢a B
  → Γ ⊢a C ≤ B
⊢a-strengthen : ∀ {Γ e x A B C}
  → (Γ , x ⦂ A) ⊢a B ⇛ e ⇛ C
  → Γ ⊢a B
  → Γ ⊢ e
  → Γ ⊢a B ⇛ e ⇛ C



≤-strengthen ≤a-int wf₁ wf₂ = ≤a-int
≤-strengthen ≤a-top wf₁ wf₂ = ≤a-top
≤-strengthen (≤a-arr C≤A B≤D) (wf-arr wf₁ wf₃) (wf-arr wf₂ wf₄) = ≤a-arr (≤-strengthen C≤A wf₂ wf₁) (≤-strengthen B≤D wf₃ wf₄)
≤-strengthen (≤a-hole ⊢e) (wf-hole x) wf₂ = ≤a-hole (⊢a-strengthen ⊢e wf₂ x)

⊢a-strengthen ⊢ wf-B wf-e = {!!}


----------------------------------------------------------------------
--                                                                  --
--                        Typing & Subtyping                        --
--                                                                  --
----------------------------------------------------------------------



≤a-arr-inv : ∀ {Γ A B C D}
  → Γ ⊢a A *⇒ B ≤ C *⇒ D
  → (Γ ⊢a C ≤ A) × (Γ ⊢a B ≤ D)
≤a-arr-inv (≤a-arr ≤a₁ ≤a₂) = ⟨ ≤a₁ , ≤a₂ ⟩

⊢a-to-≤a : ∀ {Γ e A B}
  → Γ ⊢a B ⇛ e ⇛ A
  → Γ ⊢a h A ≤ B
⊢a-to-≤a (⊢a-lit ≤a) = ≤a
⊢a-to-≤a (⊢a-var ∋x ≤a) = ≤a
⊢a-to-≤a (⊢a-app ⊢a) = proj₂ (≤a-arr-inv (⊢a-to-≤a ⊢a))
⊢a-to-≤a (⊢a-ann ⊢a ≤a) = ≤a
⊢a-to-≤a (⊢a-lam₁ ⊢a₁ ⊢a₂ wf) = ≤a-arr (≤a-hole {!!}) (≤-strengthen (⊢a-to-≤a ⊢a₂) {!!} wf)
⊢a-to-≤a (⊢a-lam₂ ⊢a wf) = ≤a-arr ≤a-refl-h {!⊢a-to-≤a ⊢a!}

⊢a-hint-self : ∀ {Γ A e}
  → Γ ⊢a Hop ⇛ e ⇛ A
  → Γ ⊢a h A ⇛ e ⇛ A

⊢a-hint-self (⊢a-lit ≤) = ⊢a-lit ≤a-int
⊢a-hint-self (⊢a-var ∋ ≤) = ⊢a-var ∋ ≤a-refl-h
⊢a-hint-self (⊢a-app ⊢e) = ⊢a-app {!!}
⊢a-hint-self (⊢a-ann ⊢e ≤) = ⊢a-ann ⊢e ≤a-refl-h
