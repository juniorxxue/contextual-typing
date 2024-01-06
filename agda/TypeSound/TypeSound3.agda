module TypeSound3 where

open import Data.Bool using (Bool; true; false; T; not)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.List using (List; _∷_; [])
open import Data.Nat using (ℕ; zero; suc)
open import Data.Product using (∃-syntax; _×_)
open import Data.String using (String; _≟_)
open import Data.Unit using (tt)
open import Relation.Nullary using (Dec; yes; no; ¬_)
open import Relation.Nullary.Decidable using (False; toWitnessFalse)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl)
open import Data.Product using (_×_; proj₁; proj₂; ∃; ∃-syntax) renaming (_,_ to ⟨_,_⟩) public
open import Function.Base using (case_of_; case_return_of_) public

Id : Set
Id = String

infixr 5  ƛ_⇒_
infixl 7  _·_
infix  9  `_
infix  5  _⦂_
infixr 8 _⇒_

data Type : Set where
  Int : Type
  _⇒_ : Type → Type → Type

data Term : Set where
  lit      : ℕ → Term
  `_       : Id → Term
  ƛ_⇒_     : Id → Term → Term
  _·_      : Term → Term → Term
  _⦂_      : Term → Type → Term

infixl 5  _,_⦂_

data Context : Set where
  ∅     : Context
  _,_⦂_ : Context → Id → Type → Context

infix  4  _∋_⦂_

data _∋_⦂_ : Context → Id → Type → Set where

  Z : ∀ {Γ x A}
      ------------------
    → Γ , x ⦂ A ∋ x ⦂ A

  S : ∀ {Γ x y A B}
    → x ≢ y
    → Γ ∋ x ⦂ A
      ------------------
    → Γ , y ⦂ B ∋ x ⦂ A


data Counter : Set where
  ∞ : Counter
  Z : Counter
  S : Counter → Counter

infix 4 _⊢d_#_⦂_

data _⊢d_#_⦂_ : Context → Counter → Term → Type → Set where

  ⊢d-int : ∀ {Γ i}
    → Γ ⊢d Z # (lit i) ⦂ Int

  ⊢d-var : ∀ {Γ x A}
    → Γ ∋ x ⦂ A
    → Γ ⊢d Z # ` x ⦂ A

  ⊢d-ann : ∀ {Γ e A}
    → Γ ⊢d ∞ # e ⦂ A
    → Γ ⊢d Z # (e ⦂ A) ⦂ A

  ⊢d-lam-∞ : ∀ {Γ e x A B}
    → Γ , x ⦂ A ⊢d ∞ # e ⦂ B
    → Γ ⊢d ∞ # (ƛ x ⇒ e) ⦂ A ⇒ B

  ⊢d-lam-n : ∀ {Γ e x A B j}
    → Γ , x ⦂ A ⊢d j # e ⦂ B
    → Γ ⊢d S j # (ƛ x ⇒ e) ⦂ A ⇒ B

  ⊢d-app₁ : ∀ {Γ e₁ e₂ A B}
    → Γ ⊢d Z # e₁ ⦂ A ⇒ B
    → Γ ⊢d ∞ # e₂ ⦂ A
    → Γ ⊢d Z # e₁ · e₂ ⦂ B

  ⊢d-app₂ : ∀ {Γ e₁ e₂ A B j}
    → Γ ⊢d (S j) # e₁ ⦂ A ⇒ B
    → Γ ⊢d Z # e₂ ⦂ A
    → Γ ⊢d j # e₁ · e₂ ⦂ B

  ⊢d-sub : ∀ {Γ e A j}
    → Γ ⊢d Z # e ⦂ A
    → j ≢ Z
    → Γ ⊢d j # e ⦂ A


data Functional : Term → Set where

  f-z : ∀ {x e}
    → Functional (ƛ x ⇒ e)

  f-s : ∀ {f A B}
    → Functional f
    → Functional (f ⦂ A ⇒ B)

data Value : Term → Set where

  V-n : ∀ {n}
    → Value (lit n)
      
  V-ƛ : ∀ {f A B}
    → Functional f
    → Value (f ⦂ A ⇒ B)

infix 9 _[_:=_]

_[_:=_] : Term → Id → Term → Term
(` x) [ y := V ] with x ≟ y
... | yes _         = V
... | no  _         = ` x
(ƛ x ⇒ e) [ y := V ] with x ≟ y
... | yes _         = ƛ x ⇒ e
... | no  _         = ƛ x ⇒ e [ y := V ]
(e₁ · e₂) [ y := V ]  = e₁ [ y := V ] · e₂ [ y := V ]
(e ⦂ A) [ y := V ] = e [ y := V ] ⦂ A
(lit n) [ y := V ]  = lit n

infix 4 _—→_

data _—→_ : Term → Term → Set where
  ξ-lam : ∀ {L L' x M}
    → L —→ L'
    → (ƛ x ⇒ M) · L —→  (ƛ x ⇒ M) · L'

  ξ-app-l : ∀ {L M M′}
    → M —→ M′
    → L · M —→ L · M′

  ξ-⦂ : ∀ {e e' A}
    → e —→ e'
    → (e ⦂ A) —→ (e' ⦂ A)
  
  β-⦂ : ∀ {V A}
    → Value V
    → ¬ (Value (V ⦂ A))
    → (V ⦂ A) —→ V

  β-ƛ : ∀ {x N V}
    → Value V
    → (ƛ x ⇒ N) · V —→ N [ x := V ]

  β-ƛ⦂ : ∀ {f A B e}
    → Functional f
    → (f ⦂ A ⇒ B) · e —→ (f · (e ⦂ A)) ⦂ B


f⦂¬—→ : ∀ {f N}
  → Functional f
  → ¬ (f —→ N)
f⦂¬—→ (f-s Ff) (ξ-⦂ f→N) = f⦂¬—→ Ff f→N
f⦂¬—→ (f-s Ff) (β-⦂ x x₁) = x₁ (V-ƛ Ff)

V¬—→ : ∀ {M N}
  → Value M
    ----------
  → ¬ (M —→ N)
V¬—→ (V-ƛ x) (ξ-⦂ M→N) = f⦂¬—→ x M→N
V¬—→ (V-ƛ x) (β-⦂ x₁ x₂) = x₂ (V-ƛ x)

—→¬V : ∀ {M N}
  → M —→ N
    ---------
  → ¬ Value M
—→¬V M—→N VM  =  V¬—→ VM M—→N

v-dec-case-n : ∀ {n A B}
  → ¬ Value (lit n ⦂ A ⇒ B)
v-dec-case-n (V-ƛ ())

f⦂→f : ∀ {M A B}
  → Functional (M ⦂ A ⇒ B)
  → Functional M
f⦂→f (f-s fM) = fM

f-dec : ∀ M
  → Dec (Functional M)
f-dec (lit x) = no (λ ())
f-dec (` x) = no (λ ())
f-dec (ƛ x ⇒ M) = yes f-z
f-dec (M · M₁) = no (λ ())
f-dec (M ⦂ Int) = no (λ ())
f-dec (M ⦂ A ⇒ B) with f-dec M
... | yes p = yes (f-s p)
... | no ¬p = no λ x → ¬p (f⦂→f x)

v⦂→f : ∀ {M A B}
  → Value (M ⦂ A ⇒ B)
  → Functional M
v⦂→f (V-ƛ x) = x

v-dec : ∀ M
  → Dec (Value M)
v-dec (lit x) = yes V-n
v-dec (` x) = no (λ ())
v-dec (ƛ x ⇒ M) = no (λ ())
v-dec (M · M₁) = no (λ ())
v-dec (M ⦂ Int) = no (λ ())
v-dec (M ⦂ A ⇒ B) with f-dec M
... | yes p = yes (V-ƛ p)
... | no ¬p = no (λ x → ¬p (v⦂→f x))


infix  4 Canonical_⦂_

data Canonical_⦂_ : Term → Type → Set where

  C-ƛ : ∀ {x A N B}
    → ∅ , x ⦂ A ⊢d Z # N ⦂ B
      -----------------------------
    → Canonical (ƛ x ⇒ N) ⦂ (A ⇒ B)

  C-zero : ∀ {n}
    →  Canonical (lit n) ⦂ Int

data Progress (M : Term) : Set where

  step : ∀ {N}
    → M —→ N
      ----------
    → Progress M

  done :
      Value M
      ----------
    → Progress M

progress : ∀ {M A j}
  → ∅ ⊢d j # M ⦂ A
  → Progress M
progress ⊢d-int = done V-n
progress (⊢d-ann {e = e} {A = A} ⊢M) with progress ⊢M | v-dec (e ⦂ A)
... | step x | _ = step (ξ-⦂ x)
... | done x | yes p = done p
... | done x | no ¬p = step (β-⦂ x ¬p)
progress (⊢d-lam-∞ ⊢M) = {!!}
progress (⊢d-lam-n ⊢M) = {!!}
progress (⊢d-app₁ ⊢M ⊢M₁) = {!!}
progress (⊢d-app₂ ⊢M ⊢M₁) = {!!}
progress (⊢d-sub ⊢M x) = progress ⊢M


ext : ∀ {Γ Δ}
  → (∀ {x A}     →         Γ ∋ x ⦂ A →         Δ ∋ x ⦂ A)
    -----------------------------------------------------
  → (∀ {x y A B} → Γ , y ⦂ B ∋ x ⦂ A → Δ , y ⦂ B ∋ x ⦂ A)
ext ρ Z           =  Z
ext ρ (S x≢y ∋x)  =  S x≢y (ρ ∋x)

rename : ∀ {Γ Δ}
  → (∀ {x A} → Γ ∋ x ⦂ A → Δ ∋ x ⦂ A)
    ----------------------------------
  → (∀ {M A j} → Γ ⊢d j # M ⦂ A → Δ ⊢d j # M ⦂ A)

rename ρ ⊢d-int = ⊢d-int
rename ρ (⊢d-var x) = ⊢d-var (ρ x)
rename ρ (⊢d-ann ⊢e) = ⊢d-ann (rename ρ ⊢e)
rename ρ (⊢d-lam-∞ ⊢e) = ⊢d-lam-∞ (rename (ext ρ) ⊢e)
rename ρ (⊢d-lam-n ⊢e) = ⊢d-lam-n (rename (ext ρ) ⊢e)
rename ρ (⊢d-app₁ ⊢e₁ ⊢e₂) = ⊢d-app₁ (rename ρ ⊢e₁) (rename ρ ⊢e₂)
rename ρ (⊢d-app₂ ⊢e₁ ⊢e₂) = ⊢d-app₂ (rename ρ ⊢e₁) (rename ρ ⊢e₂)
rename ρ (⊢d-sub ⊢e x) = ⊢d-sub (rename ρ ⊢e) x

weaken : ∀ {Γ M A j}
  → ∅ ⊢d j # M ⦂ A
    ----------
  → Γ ⊢d j # M ⦂ A
weaken {Γ} ⊢M = rename ρ ⊢M
  where
  ρ : ∀ {z C}
    → ∅ ∋ z ⦂ C
      ---------
    → Γ ∋ z ⦂ C
  ρ ()


drop : ∀ {Γ x M A B C j}
  → Γ , x ⦂ A , x ⦂ B ⊢d j # M ⦂ C
    --------------------------
  → Γ , x ⦂ B ⊢d j # M ⦂ C
drop {Γ} {x} {M} {A} {B} {C} ⊢M = rename ρ ⊢M
  where
  ρ : ∀ {z C}
    → Γ , x ⦂ A , x ⦂ B ∋ z ⦂ C
      -------------------------
    → Γ , x ⦂ B ∋ z ⦂ C
  ρ Z                 =  Z
  ρ (S x≢x Z)         =  ⊥-elim (x≢x refl)
  ρ (S z≢x (S _ ∋z))  =  S z≢x ∋z

swap : ∀ {Γ x y M A B C j}
  → x ≢ y
  → Γ , y ⦂ B , x ⦂ A ⊢d j # M ⦂ C
    --------------------------
  → Γ , x ⦂ A , y ⦂ B ⊢d j # M ⦂ C
swap {Γ} {x} {y} {M} {A} {B} {C} x≢y ⊢M = rename ρ ⊢M
  where
  ρ : ∀ {z C}
    → Γ , y ⦂ B , x ⦂ A ∋ z ⦂ C
      --------------------------
    → Γ , x ⦂ A , y ⦂ B ∋ z ⦂ C
  ρ Z                   =  S x≢y Z
  ρ (S z≢x Z)           =  Z
  ρ (S z≢x (S z≢y ∋z))  =  S z≢y (S z≢x ∋z)

subst : ∀ {Γ x N V A B j j'}
  → ∅ ⊢d j' # V ⦂ A
  → Γ , x ⦂ A ⊢d j # N ⦂ B
    --------------------
  → Γ ⊢d j # N [ x := V ] ⦂ B
subst {x = y} ⊢V ⊢d-int = ⊢d-int
subst {x = y} ⊢V (⊢d-var {x = x} Z) with x ≟ y
... | yes _         =  weaken {!!}
... | no  x≢y       =  ⊥-elim (x≢y refl)
subst {x = y} ⊢V (⊢d-var {x = x} (S x≢y ∋x)) with x ≟ y
... | yes refl      =  ⊥-elim (x≢y refl)
... | no  _         =  ⊢d-var ∋x
subst {x = y} ⊢V (⊢d-ann ⊢N) = ⊢d-ann (subst ⊢V ⊢N)
subst {x = y} ⊢V (⊢d-lam-∞ {x = x} ⊢N) with x ≟ y
... | yes refl      =  ⊢d-lam-∞ (drop ⊢N)
... | no  x≢y       =  ⊢d-lam-∞ (subst ⊢V (swap x≢y ⊢N))
subst {x = y} ⊢V (⊢d-lam-n {x = x} ⊢N) with x ≟ y
... | yes refl      =  ⊢d-lam-n (drop ⊢N)
... | no  x≢y       =  ⊢d-lam-n (subst ⊢V (swap x≢y ⊢N))
subst {x = y} ⊢V (⊢d-app₁ ⊢L ⊢M) = ⊢d-app₁ (subst ⊢V ⊢L) (subst ⊢V ⊢M)
subst {x = y} ⊢V (⊢d-app₂ ⊢L ⊢M) = ⊢d-app₂ (subst ⊢V ⊢L) (subst ⊢V ⊢M)
subst {x = y} ⊢V (⊢d-sub ⊢N j≢Z) = ⊢d-sub (subst ⊢V ⊢N) j≢Z

⊢d-sub' : ∀ {Γ e A j}
  → Γ ⊢d Z # e ⦂ A
  → Γ ⊢d j # e ⦂ A
⊢d-sub' {j = ∞} ⊢e = ⊢d-sub ⊢e (λ ())
⊢d-sub' {j = Z} ⊢e = ⊢e
⊢d-sub' {j = S j} ⊢e = ⊢d-sub ⊢e (λ ())

preserve : ∀ {M N A j}
  → ∅ ⊢d j # M ⦂ A
  → M —→ N
    ----------
  → ∅ ⊢d j # N ⦂ A
