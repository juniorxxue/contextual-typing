module TypeSound.Operation.STLC where

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

{-
two specialised subst lemma is required since we have two rules
  for annotated lambda and unannoatated lambda
-}

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

data Value : Term → Set where

  V-n : ∀ {n}
    → Value (lit n)

  V-ƛ : ∀ {x e}
    → Value (ƛ x ⇒ e)

  V-ƛ⦂ : ∀ {x e A B}
    → Value ((ƛ x ⇒ e) ⦂ A ⇒ B)


----------------------------------------------------------------------
--+                                                                +--
--+                     Operational Semantics                      +--
--+                                                                +--
----------------------------------------------------------------------

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
  ξ-·₁ : ∀ {L L′ M}
    → L —→ L′
    → L · M —→ L′ · M

  ξ-·₂ : ∀ {V M M′}
    → Value V
    → M —→ M′
    → V · M —→ V · M′

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

  β-ƛ⦂ : ∀ {x N V A B}
    → Value V
    → ((ƛ x ⇒ N) ⦂ A ⇒ B) · V —→ (N [ x := (V ⦂ A) ] ⦂ B)    


V¬—→ƛ : ∀ {x e N}
  → ƛ x ⇒ e —→ N
  → ⊥
V¬—→ƛ ()

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


⊢int-arr-inv : ∀ {Γ j n A B}
  → Γ ⊢d j # lit n ⦂ A ⇒ B
  → ⊥
⊢int-arr-inv (⊢d-sub ⊢e x) = ⊢int-arr-inv ⊢e

inv-absurd-n-fun : ∀ {Γ j n A B}
  → Γ ⊢d j # lit n ⦂ A ⇒ B
  → ⊥
inv-absurd-n-fun (⊢d-sub ⊢e x) = inv-absurd-n-fun ⊢e

v-dec : ∀ e
  → Dec (Value e)
v-dec (lit x) = yes V-n
v-dec (` x) = no (λ ())
v-dec (ƛ x ⇒ e) = yes V-ƛ
v-dec (e · e₁) = no (λ ())
v-dec (e ⦂ Int) = no (λ ())
v-dec (lit x ⦂ A ⇒ B) = no (λ ())
v-dec (` x ⦂ A ⇒ B) = no (λ ())
v-dec ((ƛ x ⇒ e) ⦂ A ⇒ B) = yes V-ƛ⦂
v-dec (e · e₁ ⦂ A ⇒ B) = no (λ ())
v-dec ((e ⦂ x) ⦂ A ⇒ B) = no (λ ())

progress : ∀ {j e A}
  → ∅ ⊢d j # e ⦂ A
  → Progress e
progress ⊢d-int = done V-n
progress (⊢d-ann {e = e} {A = A} ⊢e) with progress ⊢e | v-dec (e ⦂ A)
... | step m | _ = step (ξ-⦂ m)
... | done m | yes p = done p
... | done m | no ¬p = step (β-⦂ m ¬p)
progress (⊢d-lam-∞ ⊢e) = done V-ƛ
progress (⊢d-lam-n ⊢e) = done V-ƛ
progress (⊢d-app₁ ⊢e ⊢e₁) with progress ⊢e
... | step x = step (ξ-·₁ x)
... | done x with progress ⊢e₁
... | step x₁ = step (ξ-·₂ x x₁)
progress (⊢d-app₁ (⊢d-ann ⊢e) ⊢e₁) | done V-ƛ⦂ | done x₁ = step (β-ƛ⦂ x₁)
progress (⊢d-app₁ (⊢d-sub ⊢e x₂) ⊢e₁) | done x | done x₁ = ⊥-elim (x₂ refl)
progress (⊢d-app₂ ⊢e ⊢e₁) with progress ⊢e
... | step x = step (ξ-·₁ x)
... | done x with progress ⊢e₁
... | step x₁ = step (ξ-·₂ x x₁)
progress (⊢d-app₂ (⊢d-lam-n ⊢e) ⊢e₁) | done x | done x₁ = step (β-ƛ x₁)
progress (⊢d-app₂ (⊢d-sub (⊢d-ann ⊢e) x₂) ⊢e₁) | done V-ƛ⦂ | done x₁ = step (β-ƛ⦂ x₁)
progress (⊢d-app₂ (⊢d-sub (⊢d-sub ⊢e x₃) x₂) ⊢e₁) | done x | done x₁ = ⊥-elim (x₃ refl)
progress (⊢d-sub ⊢e x) = progress ⊢e

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

subst : ∀ {Γ x N V A B}
  → ∅ ⊢d ∞ # V ⦂ A
  → Γ , x ⦂ A ⊢d ∞ # N ⦂ B
    --------------------
  → Γ ⊢d ∞ # N [ x := (V ⦂ A) ] ⦂ B

subst' : ∀ {Γ x N V A B j}
  → ∅ ⊢d Z # V ⦂ A
  → Γ , x ⦂ A ⊢d j # N ⦂ B
    --------------------
  → Γ ⊢d j # N [ x := V ] ⦂ B
  
subst {x = y} ⊢V (⊢d-lam-∞ {x = x} ⊢e) with x ≟ y
... | yes refl = ⊢d-lam-∞ (drop ⊢e)
... | no  x≢y  = ⊢d-lam-∞ (subst ⊢V (swap x≢y ⊢e))
subst {x = y} ⊢V (⊢d-app₂ ⊢e ⊢e₁) = ⊢d-app₂ (subst' (⊢d-ann ⊢V) ⊢e) (subst' (⊢d-ann ⊢V) ⊢e₁)
subst {x = y} ⊢V (⊢d-sub ⊢e x) = ⊢d-sub (subst' (⊢d-ann ⊢V) ⊢e) x

subst' {x = y} ⊢V ⊢d-int = ⊢d-int
subst' {x = y} ⊢V (⊢d-var {x = x} Z) with x ≟ y
... | yes _         =  weaken ⊢V
... | no  x≢y       =  ⊥-elim (x≢y refl)
subst' {x = y} ⊢V (⊢d-var {x = x} (S x≢y ∋x)) with x ≟ y
... | yes refl      =  ⊥-elim (x≢y refl)
... | no  _         =  ⊢d-var ∋x
subst' {x = y} ⊢V (⊢d-ann ⊢N) = ⊢d-ann (subst' ⊢V ⊢N)
subst' {x = y} ⊢V (⊢d-lam-∞ {x = x} ⊢N) with x ≟ y
... | yes refl      =  ⊢d-lam-∞ (drop ⊢N)
... | no  x≢y       =  ⊢d-lam-∞ (subst' ⊢V (swap x≢y ⊢N))
subst' {x = y} ⊢V (⊢d-lam-n {x = x} ⊢N) with x ≟ y
... | yes refl      =  ⊢d-lam-n (drop ⊢N)
... | no  x≢y       =  ⊢d-lam-n (subst' ⊢V (swap x≢y ⊢N))
subst' {x = y} ⊢V (⊢d-app₁ ⊢L ⊢M) = ⊢d-app₁ (subst' ⊢V ⊢L) (subst' ⊢V ⊢M)
subst' {x = y} ⊢V (⊢d-app₂ ⊢L ⊢M) = ⊢d-app₂ (subst' ⊢V ⊢L) (subst' ⊢V ⊢M)
subst' {x = y} ⊢V (⊢d-sub ⊢N j≢Z) = ⊢d-sub (subst' ⊢V ⊢N) j≢Z

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
preserve (⊢d-ann ⊢e) (ξ-⦂ M→N) = ⊢d-ann (preserve ⊢e M→N)
preserve (⊢d-ann (⊢d-sub ⊢d-int x)) (β-⦂ V-n x₁) = ⊢d-int
preserve (⊢d-ann (⊢d-sub (⊢d-sub ⊢e x₂) x)) (β-⦂ V-n x₁) = ⊥-elim (x₂ refl)
preserve (⊢d-ann (⊢d-lam-∞ ⊢e)) (β-⦂ V-ƛ x₁) = ⊥-elim (x₁ V-ƛ⦂)
preserve (⊢d-ann (⊢d-sub (⊢d-sub ⊢e x₂) x)) (β-⦂ V-ƛ x₁) = ⊥-elim (x₂ refl)
preserve (⊢d-ann (⊢d-sub (⊢d-ann ⊢e) x)) (β-⦂ V-ƛ⦂ x₁) = ⊢d-ann ⊢e
preserve (⊢d-ann (⊢d-sub (⊢d-sub ⊢e x₂) x)) (β-⦂ V-ƛ⦂ x₁) = ⊥-elim (x₂ refl)
preserve (⊢d-app₁ ⊢e ⊢e₁) (ξ-·₁ M→N) = ⊢d-app₁ (preserve ⊢e M→N) ⊢e₁
preserve (⊢d-app₁ ⊢e ⊢e₁) (ξ-·₂ x M→N) = ⊢d-app₁ ⊢e (preserve ⊢e₁ M→N)
preserve (⊢d-app₁ (⊢d-sub ⊢e x₁) ⊢e₁) (β-ƛ x) = ⊥-elim (x₁ refl)
preserve (⊢d-app₁ (⊢d-ann (⊢d-lam-∞ ⊢e)) ⊢e₁) (β-ƛ⦂ x) = ⊢d-ann (subst ⊢e₁ ⊢e)
preserve (⊢d-app₁ (⊢d-ann (⊢d-sub (⊢d-sub ⊢e x₂) x₁)) ⊢e₁) (β-ƛ⦂ x) = ⊥-elim (x₂ refl)
preserve (⊢d-app₁ (⊢d-sub ⊢e x₁) ⊢e₁) (β-ƛ⦂ x) = ⊥-elim (x₁ refl)
preserve (⊢d-app₂ ⊢e ⊢e₁) (ξ-·₁ M→N) = ⊢d-app₂ (preserve ⊢e M→N) ⊢e₁
preserve (⊢d-app₂ ⊢e ⊢e₁) (ξ-·₂ x M→N) = ⊢d-app₂ ⊢e (preserve ⊢e₁ M→N)
preserve (⊢d-app₂ (⊢d-lam-n ⊢e) ⊢e₁) (β-ƛ x) = subst' ⊢e₁ ⊢e
preserve (⊢d-app₂ (⊢d-sub (⊢d-sub ⊢e x₂) x₁) ⊢e₁) (β-ƛ x) = ⊥-elim (x₂ refl)
preserve (⊢d-app₂ (⊢d-sub (⊢d-ann (⊢d-lam-∞ ⊢e)) x₁) ⊢e₁) (β-ƛ⦂ x) = ⊢d-sub' (⊢d-ann (subst' (⊢d-ann (⊢d-sub' ⊢e₁)) ⊢e))
preserve (⊢d-app₂ (⊢d-sub (⊢d-ann (⊢d-sub (⊢d-sub ⊢e x₃) x₂)) x₁) ⊢e₁) (β-ƛ⦂ x) = ⊥-elim (x₃ refl)
preserve (⊢d-app₂ (⊢d-sub (⊢d-sub ⊢e x₂) x₁) ⊢e₁) (β-ƛ⦂ x) = ⊥-elim (x₂ refl)
preserve (⊢d-sub ⊢e x) M→N = ⊢d-sub' (preserve ⊢e M→N)
