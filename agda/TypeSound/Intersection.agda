{-# OPTIONS --allow-unsolved-metas #-}
module TypeSound.Intersection where

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
infixr 8 _&_

data Type : Set where
  Int : Type
  Top : Type
  _⇒_ : Type → Type → Type
  _&_ : Type → Type → Type


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

data CCounter : Set where
   Z : CCounter
   ∞ : CCounter
   S⇐ : CCounter → CCounter
   
data Counter : Set where
   ♭ : CCounter → Counter
   S⇒ : Counter → Counter

infix 5 _≤d_#_
data _≤d_#_ : Type → Counter → Type → Set where
  ≤d-Z : ∀ {A}
    → A ≤d ♭ Z # A
  ≤d-int∞ :
      Int ≤d ♭ ∞ # Int
  ≤d-top : ∀ {A}
    → A ≤d ♭ ∞ # Top
  ≤d-arr-∞ : ∀ {A B C D}
    → C ≤d ♭ ∞ # A
    → B ≤d ♭ ∞ # D
    → A ⇒ B ≤d ♭ ∞ # C ⇒ D
  ≤d-arr-S⇒ : ∀ {A B C D j}
    → C ≤d ♭ ∞ # A
    → B ≤d j # D
    → A ⇒ B ≤d S⇒ j # A ⇒ D
  ≤d-arr-S⇐ : ∀ {A B C D j}
    → C ≤d ♭ ∞ # A
    → B ≤d ♭ j # D
    → A ⇒ B ≤d ♭ (S⇐ j) # A ⇒ D  
  ≤d-and₁ : ∀ {A B C j}
    → A ≤d j # C
    → j ≢ ♭ Z
    → A & B ≤d j # C
  ≤d-and₂ : ∀ {A B C j}
    → B ≤d j # C
    → j ≢ ♭ Z
    → A & B ≤d j # C
  ≤d-and : ∀ {A B C}
    → A ≤d ♭ ∞ # B
    → A ≤d ♭ ∞ # C
    → A ≤d ♭ ∞ # B & C

infix 4 _⊢d_#_⦂_

data _⊢d_#_⦂_ : Context → Counter → Term → Type → Set where
  ⊢d-int : ∀ {Γ n}
    → Γ ⊢d ♭ Z # (lit n) ⦂ Int

  ⊢d-var : ∀ {Γ x A}
    → Γ ∋ x ⦂ A
    → Γ ⊢d ♭ Z # ` x ⦂ A

  ⊢d-ann : ∀ {Γ e A}
    → Γ ⊢d ♭ ∞ # e ⦂ A
    → Γ ⊢d ♭ Z # (e ⦂ A) ⦂ A

  ⊢d-lam₁ : ∀ {Γ e x A B}
    → Γ , x ⦂ A ⊢d ♭ ∞ # e ⦂ B
    → Γ ⊢d ♭ ∞ # (ƛ x ⇒ e) ⦂ A ⇒ B

  ⊢d-lam₂ : ∀ {Γ e x A B i}
    → Γ , x ⦂ A ⊢d i # e ⦂ B
    → Γ ⊢d S⇒ i # (ƛ x ⇒ e) ⦂ A ⇒ B

  ⊢d-app⇐ : ∀ {Γ e₁ e₂ A B j}
    → Γ ⊢d ♭ (S⇐ j) # e₁ ⦂ A ⇒ B
    → Γ ⊢d ♭ ∞ # e₂ ⦂ A
    → Γ ⊢d ♭ j # e₁ · e₂ ⦂ B

  ⊢d-app⇒ : ∀ {Γ e₁ e₂ A B j}
    → Γ ⊢d S⇒ j # e₁ ⦂ A ⇒ B
    → Γ ⊢d ♭ Z # e₂ ⦂ A
    → Γ ⊢d j # e₁ · e₂ ⦂ B

  ⊢d-sub : ∀ {Γ e A B i}
    → Γ ⊢d ♭ Z # e ⦂ B
    → (B≤A : B ≤d i # A)
    → (i≢Z : i ≢ ♭ Z)
    → Γ ⊢d i # e ⦂ A

  ⊢d-& : ∀ {Γ e A B}
    → Γ ⊢d ♭ ∞ # e ⦂ A
    → Γ ⊢d ♭ ∞ # e ⦂ B
    → Γ ⊢d ♭ ∞ # e ⦂ A & B

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


data Progress (M : Term) : Set where

  step : ∀ {N}
    → M —→ N
      ----------
    → Progress M

  done :
      Value M
      ----------
    → Progress M


v-dec : ∀ e
  → Dec (Value e)
v-dec (lit x) = yes V-n
v-dec (` x) = no (λ ())
v-dec (ƛ x ⇒ e) = yes V-ƛ
v-dec (e · e₁) = no (λ ())
v-dec (e ⦂ Int) = no (λ ())
v-dec (e ⦂ Top) = no (λ ())
v-dec (lit x ⦂ A ⇒ A₁) = no (λ ())
v-dec (` x ⦂ A ⇒ A₁) = no (λ ())
v-dec ((ƛ x ⇒ e) ⦂ A ⇒ A₁) = yes V-ƛ⦂
v-dec (e · e₁ ⦂ A ⇒ A₁) = no (λ ())
v-dec ((e ⦂ x) ⦂ A ⇒ A₁) = no (λ ())
v-dec (e ⦂ A & A₁) = no (λ ())

progress-app₁ : ∀ {e₁ e₂ j A B}
  → ∅ ⊢d ♭ (S⇐ j) # e₁ ⦂ A ⇒ B
  → ∅ ⊢d ♭ ∞ # e₂ ⦂ A
  → Value e₁
  → Value e₂
  → Progress (e₁ · e₂)
progress-app₁ (⊢d-sub (⊢d-sub ⊢e₁ x₂ x₃) x x₁) ⊢e₂ V-n V2 = ⊥-elim (x₃ refl)
progress-app₁ (⊢d-sub (⊢d-sub ⊢e₁ x₂ x₃) x x₁) ⊢e₂ V-ƛ V2 = ⊥-elim (x₃ refl)
progress-app₁ ⊢e₁ ⊢e₂ V-ƛ⦂ v2 = step (β-ƛ⦂ v2)

progress-app₂ : ∀ {e₁ e₂ i A B}
  → ∅ ⊢d (S⇒ i) # e₁ ⦂ A ⇒ B
  → ∅ ⊢d ♭ Z # e₂ ⦂ A
  → Value e₁
  → Value e₂
  → Progress (e₁ · e₂)
progress-app₂ (⊢d-sub (⊢d-sub ⊢e₁ x₂ x₃) x x₁) ⊢e₂ V-n v2 = ⊥-elim (x₃ refl)
progress-app₂ (⊢d-lam₂ ⊢e₁) ⊢e₂ V-ƛ v2 = step (β-ƛ v2)
progress-app₂ (⊢d-sub (⊢d-sub ⊢e₁ x₂ x₃) x x₁) ⊢e₂ V-ƛ v2 = ⊥-elim (x₃ refl)
progress-app₂ ⊢e₁ ⊢e₂ V-ƛ⦂ v2 = step (β-ƛ⦂ v2)

progress : ∀ {j e A}
  → ∅ ⊢d j # e ⦂ A
  → Progress e
progress ⊢d-int = done V-n
progress (⊢d-ann {e = e} {A = A} ⊢e) with progress ⊢e | v-dec (e ⦂ A)
... | step x | _ = step (ξ-⦂ x)
... | done x | yes p = done p
... | done x | no ¬p = step (β-⦂ x ¬p)
progress (⊢d-lam₁ ⊢e) = done V-ƛ
progress (⊢d-lam₂ ⊢e) = done V-ƛ
progress (⊢d-app⇐ ⊢e₁ ⊢e₂) with progress ⊢e₁
... | step x = step (ξ-·₁ x)
... | done x with progress ⊢e₂
... | step x₁ = step (ξ-·₂ x x₁)
... | done x₁ = progress-app₁ ⊢e₁ ⊢e₂ x x₁
progress (⊢d-app⇒ ⊢e₁ ⊢e₂) with progress ⊢e₁ | progress ⊢e₂
... | step r1 | _ = step (ξ-·₁ r1)
... | done v1 | step r2 = step (ξ-·₂ v1 r2)
... | done v1 | done v2 = progress-app₂ ⊢e₁ ⊢e₂ v1 v2
progress (⊢d-sub ⊢e x x₁) = progress ⊢e
progress (⊢d-& ⊢e₁ ⊢e₂) = progress ⊢e₁

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
rename ρ (⊢d-ann ⊢M) = ⊢d-ann (rename ρ ⊢M)
rename ρ (⊢d-lam₁ ⊢M) = ⊢d-lam₁ (rename (ext ρ) ⊢M)
rename ρ (⊢d-lam₂ ⊢M) = ⊢d-lam₂ (rename (ext ρ) ⊢M)
rename ρ (⊢d-app⇐ ⊢M ⊢M₁) = ⊢d-app⇐ (rename ρ ⊢M) (rename ρ ⊢M₁)
rename ρ (⊢d-app⇒ ⊢M ⊢M₁) = ⊢d-app⇒ (rename ρ ⊢M) (rename ρ ⊢M₁)
rename ρ (⊢d-sub ⊢M x x₁) = ⊢d-sub (rename ρ ⊢M) x x₁
rename ρ (⊢d-& ⊢M ⊢M₁) = ⊢d-& (rename ρ ⊢M) (rename ρ ⊢M₁)

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

⊢d-sub' : ∀ {Γ e A B i}
  → Γ ⊢d ♭ Z # e ⦂ B
  → B ≤d i # A
  → Γ ⊢d i # e ⦂ A
⊢d-sub' ⊢e ≤d-Z = ⊢e
⊢d-sub' ⊢e ≤d-int∞ = ⊢d-sub ⊢e ≤d-int∞ (λ ())
⊢d-sub' ⊢e ≤d-top = ⊢d-sub ⊢e ≤d-top (λ ())
⊢d-sub' ⊢e (≤d-arr-∞ B≤A B≤A₁) = ⊢d-sub ⊢e (≤d-arr-∞ B≤A B≤A₁) (λ ())
⊢d-sub' ⊢e (≤d-arr-S⇒ B≤A B≤A₁) = ⊢d-sub ⊢e (≤d-arr-S⇒ B≤A B≤A₁) (λ ())
⊢d-sub' ⊢e (≤d-arr-S⇐ B≤A B≤A₁) = ⊢d-sub ⊢e (≤d-arr-S⇐ B≤A B≤A₁) (λ ())
⊢d-sub' ⊢e (≤d-and₁ B≤A x) = ⊢d-sub ⊢e (≤d-and₁ B≤A x) x
⊢d-sub' ⊢e (≤d-and₂ B≤A x) = ⊢d-sub ⊢e (≤d-and₂ B≤A x) x
⊢d-sub' ⊢e (≤d-and B≤A B≤A₁) = ⊢d-& (⊢d-sub' ⊢e B≤A) (⊢d-sub' ⊢e B≤A₁)

≤d-refl∞ : ∀ {A} → A ≤d ♭ ∞ # A
≤d-refl∞ {A = Int} = ≤d-int∞
≤d-refl∞ {A = Top} = ≤d-top
≤d-refl∞ {A = A ⇒ A₁} = ≤d-arr-∞ ≤d-refl∞ ≤d-refl∞
≤d-refl∞ {A = A & A₁} = ≤d-and (≤d-and₁ ≤d-refl∞ λ ()) (≤d-and₂ ≤d-refl∞ λ ())

subst : ∀ {Γ x N V A B}
  → ∅ ⊢d ♭ ∞ # V ⦂ A
  → Γ , x ⦂ A ⊢d ♭ ∞ # N ⦂ B
    --------------------
  → Γ ⊢d ♭ ∞ # N [ x := (V ⦂ A) ] ⦂ B

subst' : ∀ {Γ x N V A B j}
  → ∅ ⊢d ♭ Z # V ⦂ A
  → Γ , x ⦂ A ⊢d j # N ⦂ B
    --------------------
  → Γ ⊢d j # N [ x := V ] ⦂ B

subst {x = y} ⊢V (⊢d-lam₁ {x = x} ⊢N) with x ≟ y
... | yes refl = ⊢d-lam₁ (drop ⊢N)
... | no  x≢y  = ⊢d-lam₁ (subst ⊢V (swap x≢y ⊢N))
subst {x = y} ⊢V (⊢d-app⇐ ⊢N ⊢M) = ⊢d-app⇐ (subst' (⊢d-ann ⊢V) ⊢N) (subst' (⊢d-ann ⊢V) ⊢M)
subst {x = y} ⊢V (⊢d-app⇒ ⊢N ⊢M) = ⊢d-app⇒ (subst' (⊢d-ann ⊢V) ⊢N) (subst' (⊢d-ann ⊢V) ⊢M)
subst {x = y} ⊢V (⊢d-sub ⊢N x x₁) = ⊢d-sub' (subst' (⊢d-ann ⊢V) ⊢N) x
subst {x = y} ⊢V (⊢d-& ⊢N ⊢M) = ⊢d-& (subst ⊢V ⊢N) (subst ⊢V ⊢M)

subst' {x = y} ⊢V ⊢d-int = ⊢d-int
subst' {x = y} ⊢V (⊢d-var {x = x} Z) with x ≟ y
... | yes _         =  weaken ⊢V
... | no  x≢y       =  ⊥-elim (x≢y refl)
subst' {x = y} ⊢V (⊢d-var {x = x} (S x≢y ∋x)) with x ≟ y
... | yes refl      =  ⊥-elim (x≢y refl)
... | no  _         =  ⊢d-var ∋x
subst' {x = y} ⊢V (⊢d-ann ⊢N) = ⊢d-ann (subst' ⊢V ⊢N)
subst' {x = y} ⊢V (⊢d-lam₁ {x = x} ⊢N) with x ≟ y
... | yes refl      =  ⊢d-lam₁ (drop ⊢N)
... | no  x≢y       =  ⊢d-lam₁ (subst' ⊢V (swap x≢y ⊢N))
subst' {x = y} ⊢V (⊢d-lam₂ {x = x} ⊢N) with x ≟ y
... | yes refl      =  ⊢d-lam₂ (drop ⊢N)
... | no  x≢y       =  ⊢d-lam₂ (subst' ⊢V (swap x≢y ⊢N))
subst' {x = y} ⊢V (⊢d-app⇐ ⊢L ⊢M) = ⊢d-app⇐ (subst' ⊢V ⊢L) (subst' ⊢V ⊢M)
subst' {x = y} ⊢V (⊢d-app⇒ ⊢L ⊢M) = ⊢d-app⇒ (subst' ⊢V ⊢L) (subst' ⊢V ⊢M)
subst' {x = y} ⊢V (⊢d-sub ⊢N x x₁) = ⊢d-sub' (subst' ⊢V ⊢N) x
subst' {x = y} ⊢V (⊢d-& ⊢M ⊢N) = ⊢d-& (subst' ⊢V ⊢M) (subst' ⊢V ⊢N)

preserve : ∀ {M N A j}
  → ∅ ⊢d j # M ⦂ A
  → M —→ N
  → ∅ ⊢d j # N ⦂ A
-- ann  
preserve (⊢d-ann ⊢M) (ξ-⦂ M→N) = ⊢d-ann (preserve ⊢M M→N)
-- ann value
preserve (⊢d-ann ⊢M) (β-⦂ V-n ¬vnA) = {!!}
preserve (⊢d-ann ⊢M) (β-⦂ V-ƛ ¬vnA) = {!!}
preserve (⊢d-ann ⊢M) (β-⦂ V-ƛ⦂ ¬vnA) = {!!}
-- app check
preserve (⊢d-app⇐ ⊢M ⊢B) (ξ-·₁ M→N) = ⊢d-app⇐ (preserve ⊢M M→N) ⊢B
preserve (⊢d-app⇐ ⊢M ⊢B) (ξ-·₂ VM M→N) = ⊢d-app⇐ ⊢M (preserve ⊢B M→N)
preserve (⊢d-app⇐ (⊢d-sub (⊢d-sub ⊢M x₂ x₃) x x₁) ⊢B) (β-ƛ VB) = ⊥-elim (x₃ refl)
preserve (⊢d-app⇐ (⊢d-sub (⊢d-ann (⊢d-lam₁ ⊢M)) (≤d-arr-S⇐ x₁ x₃) x₂) ⊢B) (β-ƛ⦂ x) = ⊢d-sub' (⊢d-ann (subst ⊢B ⊢M)) x₃
preserve (⊢d-app⇐ (⊢d-sub (⊢d-ann (⊢d-sub (⊢d-sub ⊢M x₅ x₆) x₃ x₄)) x₁ x₂) ⊢B) (β-ƛ⦂ x) = ⊥-elim (x₆ refl)
preserve (⊢d-app⇐ (⊢d-sub (⊢d-sub ⊢M x₃ x₄) x₁ x₂) ⊢B) (β-ƛ⦂ x) = ⊥-elim (x₄ refl)
-- app infer
preserve (⊢d-app⇒ ⊢M ⊢B) (ξ-·₁ M→N) = ⊢d-app⇒ (preserve ⊢M M→N) ⊢B
preserve (⊢d-app⇒ ⊢M ⊢B) (ξ-·₂ x M→N) = ⊢d-app⇒ ⊢M (preserve ⊢B M→N)
preserve (⊢d-app⇒ (⊢d-lam₂ ⊢M) ⊢B) (β-ƛ x) = subst' ⊢B ⊢M
preserve (⊢d-app⇒ (⊢d-sub (⊢d-sub ⊢M x₃ x₄) x₁ x₂) ⊢B) (β-ƛ x) = ⊥-elim (x₄ refl)
preserve (⊢d-app⇒ (⊢d-sub (⊢d-ann (⊢d-lam₁ ⊢M)) (≤d-arr-S⇒ x₁ x₃) x₂) ⊢B) (β-ƛ⦂ x) = ⊢d-sub' (⊢d-ann (subst (⊢d-sub' ⊢B ≤d-refl∞) ⊢M)) x₃
preserve (⊢d-app⇒ (⊢d-sub (⊢d-ann (⊢d-sub (⊢d-sub ⊢M x₆ x₇) x₄ x₅)) (≤d-arr-S⇒ x₁ x₃) x₂) ⊢B) (β-ƛ⦂ x) = ⊥-elim (x₇ refl)
preserve (⊢d-app⇒ (⊢d-sub (⊢d-sub ⊢M x₃ x₄) x₁ x₂) ⊢B) (β-ƛ⦂ x) = ⊥-elim (x₄ refl)
-- sub
preserve (⊢d-sub ⊢M B≤A nz) M→N = ⊢d-sub (preserve ⊢M M→N) B≤A nz
-- and
preserve (⊢d-& ⊢M ⊢B) M→N = ⊢d-& (preserve ⊢M M→N) (preserve ⊢B M→N)

-- TODO: use dependent pattern matching to eliminate ⊥-elim cases
-- Warning: must consider how subtyping affects the reasoning
