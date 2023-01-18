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

data free : Term → Id → Set where
  free-var : ∀ {x} → free (` x) x
  free-lam : ∀ {x₁ x₂ e} → free e x₁ → x₁ ≢ x₂ → free (ƛ x₂ ⇒ e) x₁
  free-app-l : ∀ {e₁ e₂ x} → free e₁ x → free (e₁ · e₂) x
  free-app-r : ∀ {e₁ e₂ x} → free e₂ x → free (e₁ · e₂) x
  free-ann : ∀ {e A x} → free e x → free (e ⦂ A) x

data freeT : Hype → Id → Set where
  free-hole : ∀ {e x} → free e x → freeT (⟦ e ⟧) x

infix 4 _⊢a_≤_
infix 4 _⊢a_⇛_⇛_ 

data _⊢a_≤_ : Context → Hype → Hype → Set
data _⊢a_⇛_⇛_ : Context → Hype → Term → Type → Set

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
    → Γ ⊢a A ⇛ lit n ⇛ Int

  ⊢a-var : ∀ {Γ A B x}
    → Γ ∋ x ⦂ B
    → Γ ⊢a h B ≤ A
    → Γ ⊢a A ⇛ ` x ⇛ B

  ⊢a-app : ∀ {Γ e₁ e₂ A C D}
    → Γ ⊢a ⟦ e₂ ⟧ *⇒ A ⇛ e₁ ⇛ (C ⇒ D)
    → Γ ⊢a A ⇛ e₁ · e₂ ⇛ D

  ⊢a-ann : ∀ {Γ e A B}
    → Γ ⊢a h B ⇛ e ⇛ B
    → Γ ⊢a h B ≤ A
    → Γ ⊢a A ⇛ e ⦂ B ⇛ B

  ⊢a-lam₁ : ∀ {Γ e₁ e x A B C}
    → Γ ⊢a Hop ⇛ e₁ ⇛ A
    → Γ , x ⦂ A ⊢a B ⇛ e ⇛ C
    → ¬ (freeT B x)
    → Γ ⊢a ⟦ e₁ ⟧ *⇒ B ⇛ ƛ x ⇒ e ⇛ A ⇒ C

  ⊢a-lam₂ : ∀ {Γ x e A B C}
    → Γ , x ⦂ A ⊢a B ⇛ e ⇛ C
    → Γ ⊢a h A *⇒ B ⇛ ƛ x ⇒ e ⇛ A ⇒ C


_ : ∅ ⊢a Hop ⇛ (ƛ "x" ⇒ ` "x") · lit 1 ⇛ Int
_ = ⊢a-app (⊢a-lam₁ (⊢a-lit ≤a-top) (⊢a-var Z ≤a-top) λ ())

_ : ∀ {x} → ¬ freeT Hop x
_ = λ ()

_ : ∅ ⊢a Hop ⇛ ((ƛ "f" ⇒ ` "f" · (lit 1)) ⦂ (Int ⇒ Int) ⇒ Int) · (ƛ "x" ⇒ ` "x") ⇛ Int
_ = ⊢a-app (⊢a-ann (⊢a-lam₂ (⊢a-app (⊢a-var Z (≤a-arr (≤a-hole (⊢a-lit ≤a-int)) ≤a-int)))) (≤a-arr (≤a-hole (⊢a-lam₂ {A = Int} (⊢a-var Z ≤a-int))) ≤a-top))


------------ Properties of Algorithmic System ---------------

≤a-refl-h : ∀ {A Γ}
  → Γ ⊢a h A ≤ h A
≤a-refl-h {A = Int} = ≤a-int
≤a-refl-h {A = Top} = ≤a-top
≤a-refl-h {A = A ⇒ A₁} = ≤a-arr ≤a-refl-h ≤a-refl-h

-- renaming

{-
according to https://plfa.github.io/Properties/
three corollaries follow this lemma
1. weakening lemma
2. drop lemma: drop shadowed occurrence
3. swap lemma
-}

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

≤a-rename ρ ≤a-int = ≤a-int
≤a-rename ρ ≤a-top = ≤a-top
≤a-rename ρ (≤a-arr ≤a₁ ≤a₂) = ≤a-arr (≤a-rename ρ ≤a₁) (≤a-rename ρ ≤a₂)
≤a-rename ρ (≤a-hole ⊢a) = ≤a-hole (⊢a-rename ρ ⊢a)

⊢a-rename ρ (⊢a-lit ⊢a) = ⊢a-lit (≤a-rename ρ ⊢a)
⊢a-rename ρ (⊢a-var ≤a ∋x) = ⊢a-var (ρ ≤a) (≤a-rename ρ ∋x)
⊢a-rename ρ (⊢a-app ⊢a) = ⊢a-app (⊢a-rename ρ ⊢a)
⊢a-rename ρ (⊢a-ann ⊢a ≤a) = ⊢a-ann (⊢a-rename ρ ⊢a) (≤a-rename ρ ≤a)
⊢a-rename ρ (⊢a-lam₁ ⊢a₁ ⊢a₂ nf) = ⊢a-lam₁ (⊢a-rename ρ ⊢a₁) (⊢a-rename (ext ρ) ⊢a₂) nf
⊢a-rename ρ (⊢a-lam₂ ⊢a) = ⊢a-lam₂ (⊢a-rename (ext ρ) ⊢a)

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

-- strengthening

≤-strengthen-r : ∀ {Γ x A B C}
  → (Γ , x ⦂ A) ⊢a C ≤ B
  → ¬ freeT C x
  → ¬ freeT B x
  → Γ ⊢a C ≤ B
≤-strengthen-r {Γ} {x} {A} {B} {C} ≤ nf₁ nf₂ = ≤a-rename {!!} ≤

{-
  where
    ρ : ∀ {z D}
      → Γ , x ⦂ A ∋ z ⦂ D
      → Γ ∋ z ⦂ D
    ρ = {!!}
-}    

{-

Goal: Γ ⊢a h C ≤ B
Have: (Γ , x ⦂ A) ⊢a h C ≤ B
————————————————————————————————————————————————————————————
⊢a₂ : Γ , x ⦂ A ⊢a B ⇛ e ⇛ C
⊢a₁ : Γ ⊢a Hop ⇛ e₁ ⇛ A

Intuitively we know that this lemma holds, since x ⦂ A shouldn't appear in B type

1st try: fix the rule
2nd try: de bruijn or something else <- i don't think it solves the problem

-}

{-
strengthen : ∀ {Γ x A B C}
  → (Γ , x ⦂ A) ⊢a h C ≤ B
  → ¬ freeT B x
  → Γ ⊢a h C ≤ B
strengthen {B = Hnt} {C = Int} ≤ nf = ≤a-int
strengthen {B = Hop} {C = Int} ≤ nf = ≤a-top
strengthen {B = Hop} {C = Top} ≤ nf = ≤a-top
strengthen {B = .Hop} {C = C₁ ⇒ C₂} ≤a-top nf = ≤a-top
strengthen {B = .(_ *⇒ _)} {C = C₁ ⇒ C₂} (≤a-arr ≤ ≤₁) nf = ≤a-arr {!!} {!!}

the problem here is that arrow type is contra
Just notice that the free shouldn't be baised on each side
so

r-}

∋-strengthen : ∀ {Γ x y A B}
  → Γ , y ⦂ A ∋ x ⦂ B
  → y ≢ x
  → Γ ∋ x ⦂ B
∋-strengthen Z neq = ⊥-elim (neq refl)
∋-strengthen (S x ∋) neq = ∋

≤-strengthen : ∀ {Γ x A B C}
  → (Γ , x ⦂ A) ⊢a C ≤ B
  → ¬ freeT C x
  → ¬ freeT B x
  → Γ ⊢a C ≤ B

⊢a-strengthen : ∀ {Γ e x A B C}
  → (Γ , x ⦂ A) ⊢a B ⇛ e ⇛ C
  → ¬ free e x
  → ¬ freeT B x
  → Γ ⊢a B ⇛ e ⇛ C

≤-strengthen {B = Hnt} {C = Hnt} ≤ nf₁ nf₂ = ≤a-int
≤-strengthen {B = Hop} {C = Hnt} ≤ nf₁ nf₂ = ≤a-top
≤-strengthen {B = Hop} {C = Hop} ≤ nf₁ nf₂ = ≤a-top
≤-strengthen {B = Hop} {C = C₁ *⇒ C₂} ≤ nf₁ nf₂ = ≤a-top
≤-strengthen {B = B₁ *⇒ B₂} {C = C₁ *⇒ C₂} (≤a-arr ≤₁ ≤₂) nf₁ nf₂ = ≤a-arr (≤-strengthen ≤₁ {!!} {!!}) (≤-strengthen ≤₂ {!!} {!!}) -- trivial
≤-strengthen {C = ⟦ x ⟧} ≤a-top nf₁ nf₂ = ≤a-top
≤-strengthen {C = ⟦ x ⟧} (≤a-hole ⊢) nf₁ nf₂ = ≤a-hole (⊢a-strengthen ⊢ {!!} {!!})

⊢a-strengthen (⊢a-lit ≤) nf nft = ⊢a-lit (≤-strengthen ≤ {!!} nft) -- trivial
⊢a-strengthen (⊢a-var ∋ ≤) nf nft = ⊢a-var (∋-strengthen ∋ {!!}) (≤-strengthen ≤ {!!} nft) -- trivial
⊢a-strengthen (⊢a-app ⊢) nf nft = ⊢a-app (⊢a-strengthen ⊢ {!!} {!!}) -- trivial
⊢a-strengthen (⊢a-ann ⊢ ≤) nf nft = ⊢a-ann (⊢a-strengthen ⊢ {!!} {!!}) (≤-strengthen ≤ {!!} nft) -- trivial
⊢a-strengthen (⊢a-lam₁ ⊢₁ ⊢₂ nfx) nf nft = ⊢a-lam₁ {!!} {!!} nfx
⊢a-strengthen (⊢a-lam₂ ⊢) nf nft = ⊢a-lam₂ (⊢a-strengthen (⊢a-swap {!!} ⊢) {!!} {!!}) -- strengthen should be more general or a swap lemma (proved); others are trivial lemmas

-- inversion lemmas

≤a-arr-inv : ∀ {Γ A B C D}
  → Γ ⊢a A *⇒ B ≤ C *⇒ D
  → (Γ ⊢a C ≤ A) × (Γ ⊢a B ≤ D)
≤a-arr-inv (≤a-arr ≤a₁ ≤a₂) = ⟨ ≤a₁ , ≤a₂ ⟩

-- lemmas about typing and subtyping

⊢a-to-≤a : ∀ {Γ e A B}
  → Γ ⊢a B ⇛ e ⇛ A
  → Γ ⊢a h A ≤ B
⊢a-to-≤a (⊢a-lit ≤a) = ≤a
⊢a-to-≤a (⊢a-var ∋x ≤a) = ≤a
⊢a-to-≤a (⊢a-app ⊢a) = proj₂ (≤a-arr-inv (⊢a-to-≤a ⊢a))
⊢a-to-≤a (⊢a-ann ⊢a ≤a) = ≤a
⊢a-to-≤a (⊢a-lam₁ ⊢a₁ ⊢a₂ nf) = ≤a-arr (≤a-hole {!!}) {!⊢a-to-≤a ⊢a₂!}
⊢a-to-≤a (⊢a-lam₂ ⊢a) = ≤a-arr ≤a-refl-h {!⊢a-to-≤a ⊢a!}

-- lemmas about algo typing

--------------------- Lemmas for algo typing -----------------

-- aux lemma


⊢a-hint-chk : ∀ {Γ e₁ e₂ A B C}
  → Γ ⊢a ⟦ e₂ ⟧ *⇒ A ⇛ e₁ ⇛ B ⇒ C
  → Γ ⊢a h B ⇛ e₂ ⇛ B

-- Two lemmas should be unified

⊢a-hint-self : ∀ {Γ A e}
  → Γ ⊢a Hop ⇛ e ⇛ A
  → Γ ⊢a h A ⇛ e ⇛ A

⊢a-hint-self-1 : ∀ {Γ B C e₁ e₂}
  → Γ ⊢a ⟦ e₂ ⟧ *⇒ Hop ⇛ e₁ ⇛ B ⇒ C -- <- this premise can introduce a checking rule for e₂
  → Γ ⊢a ⟦ e₂ ⟧ *⇒ h C ⇛ e₁ ⇛ B ⇒ C
⊢a-hint-self-1 {e₁ = ` x} (⊢a-var x₁ (≤a-arr x₂ x₃)) = ⊢a-var x₁ (≤a-arr x₂ ≤a-refl-h)
⊢a-hint-self-1 {e₁ = ƛ x ⇒ e₁} ⊢ = {!!}
⊢a-hint-self-1 {e₁ = e₁ · e₂} ⊢ = {!!}
⊢a-hint-self-1 {e₁ = e₁ ⦂ x} ⊢ = {!!}

⊢a-hint-self (⊢a-lit ≤) = ⊢a-lit ≤a-int
⊢a-hint-self (⊢a-var ∋ ≤) = ⊢a-var ∋ ≤a-refl-h
⊢a-hint-self (⊢a-app ⊢a) = ⊢a-app (⊢a-hint-self-1 ⊢a)
⊢a-hint-self (⊢a-ann ⊢a ≤) = ⊢a-ann ⊢a ≤a-refl-h


{-
work around: ⊢a-to-≤a

rule change: not free condition in lam rule

1. strengthening lemma <-- find the correct lemma, and simplify the proof (solved?)

   problems with rename lemma

2. ⊢a-hint-self: <-- find the correct with lemma intuituion

  perhaps it's the same lemma

-}
