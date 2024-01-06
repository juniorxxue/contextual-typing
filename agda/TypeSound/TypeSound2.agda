module TypeSound2 where

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

data PValue : Term → Set where

  P-ƛ : ∀ {x e}
      ---------------
    → PValue (ƛ x ⇒ e)

  P-n : ∀ {n}
    → PValue (lit n)


data Value : Term → Set where

  V-p : ∀ {p A}
    → PValue p
      ---------------
    → Value (p ⦂ A)

  V-ƛ : ∀ {x e}
      ---------------
    → Value (ƛ x ⇒ e)

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
    → ¬ (PValue e)
    → e —→ e'
    → (e ⦂ A) —→ (e' ⦂ A)
  
  β-⦂ : ∀ {V A}
    → Value V
    → (∀ {x e} → V ≢ (ƛ x ⇒ e))
    → (V ⦂ A) —→ V

  β-ƛ : ∀ {x N V}
    → Value V
    → (ƛ x ⇒ N) · V —→ N [ x := V ]

  β-ƛ⦂ : ∀ {x N V A B}
    → Value V
    → ((ƛ x ⇒ N) ⦂ A ⇒ B) · V —→ (N [ x := V ] ⦂ B)

  n-⦂ : ∀ {n}
    → (lit n) —→ ((lit n) ⦂ Int)

¬pvalue→¬ƛ : ∀ {e}
  → ¬ PValue e
  → (∀ {x e'} → e ≢ ƛ x ⇒ e')
¬pvalue→¬ƛ noP x₁ rewrite x₁ = noP P-ƛ


V¬—→ƛ : ∀ {x e N}
  → ƛ x ⇒ e —→ N
  → ⊥
V¬—→ƛ ()

V¬—→p : ∀ {p A N}
  → PValue p
  → (p ⦂ A) —→ N
  → ⊥
V¬—→p P-ƛ (β-⦂ x x₁) = ⊥-elim (x₁ refl)
V¬—→p P-n (ξ-⦂ x n-⦂) = ⊥-elim (x P-n)


V¬—→ : ∀ {M N}
  → Value M
    ----------
  → ¬ (M —→ N)
V¬—→ (V-p p) = V¬—→p p
V¬—→ V-ƛ = V¬—→ƛ

—→¬V : ∀ {M N}
  → M —→ N
    ---------
  → ¬ Value M
—→¬V M—→N VM  =  V¬—→ VM M—→N

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

p-dec : ∀ e
  → Dec (PValue e)
p-dec (lit x) = yes P-n
p-dec (` x) = no λ ()
p-dec (ƛ x ⇒ e) = yes P-ƛ
p-dec (e · e₁) = no (λ ())
p-dec (e ⦂ x) = no (λ ())

inv-absurd-n-fun : ∀ {Γ j n A B}
  → Γ ⊢d j # lit n ⦂ A ⇒ B
  → ⊥
inv-absurd-n-fun (⊢d-sub ⊢e x) = inv-absurd-n-fun ⊢e

progress-lam : ∀ {p₁ e₂ A A₁ A₂ j}
  → PValue p₁
  → ∅ ⊢d j # (p₁ ⦂ A) ⦂ A₁ ⇒ A₂
  → Value e₂
  → Progress ((p₁ ⦂ A) · e₂)
progress-lam P-ƛ (⊢d-ann ⊢p) ve = step (β-ƛ⦂ ve)
progress-lam P-ƛ (⊢d-sub ⊢p x) ve = progress-lam P-ƛ ⊢p ve
progress-lam P-n (⊢d-ann ⊢p) ve = ⊥-elim (inv-absurd-n-fun ⊢p)
progress-lam P-n (⊢d-sub ⊢p x) ve = progress-lam P-n ⊢p ve

progress : ∀ {M A j}
  → ∅ ⊢d j # M ⦂ A
  → Progress M
progress ⊢d-int = step n-⦂
progress (⊢d-ann {e = e} ⊢e) with progress ⊢e | p-dec e
... | step x | yes P-n = done (V-p P-n)
... | step x | no ¬p = step (ξ-⦂ ¬p x)
... | done x | yes p = done (V-p p)
... | done x | no ¬p = step (β-⦂ x (¬pvalue→¬ƛ ¬p))
progress (⊢d-lam-∞ ⊢e) = done V-ƛ
progress (⊢d-lam-n ⊢e) = done V-ƛ
progress (⊢d-app₁ ⊢L ⊢M) with progress ⊢L
... | step L—→L′                            =  step (ξ-·₁ L—→L′)
... | done V-ƛ with progress ⊢M
...   | step M—→M′                          =  step (ξ-·₂ V-ƛ M—→M′)
...   | done VM                             =  step (β-ƛ VM)
progress (⊢d-app₁ ⊢L ⊢M) | done (V-p p) with progress ⊢M
...   | step M—→M′  = step (ξ-·₂ (V-p p) M—→M′)
...   | done VM     = progress-lam p ⊢L VM
progress (⊢d-app₂ ⊢L ⊢M) with progress ⊢L
... | step L—→L′                            =  step (ξ-·₁ L—→L′)
... | done V-ƛ with progress ⊢M
...   | step M—→M′                          =  step (ξ-·₂ V-ƛ M—→M′)
...   | done VM                             =  step (β-ƛ VM)
progress (⊢d-app₂ ⊢L ⊢M) | done (V-p p) with progress ⊢M
...   | step M—→M′  = step (ξ-·₂ (V-p p) M—→M′)
...   | done VM     = progress-lam p ⊢L VM
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

prv-value : ∀ {Γ j A V}
  → Γ ⊢d j # V ⦂ A
  → Value V
  → (∀ {x e} → V ≢ ƛ x ⇒ e)
  → Γ ⊢d Z # V ⦂ A
prv-value (⊢d-ann ⊢e) (V-p x) neq = ⊢d-ann ⊢e
prv-value (⊢d-sub ⊢e x₁) (V-p x) neq = ⊢e
prv-value ⊢e V-ƛ neq = ⊥-elim (neq refl)


preserve : ∀ {M N A j}
  → ∅ ⊢d j # M ⦂ A
  → M —→ N
    ----------
  → ∅ ⊢d j # N ⦂ A
preserve ⊢d-int n-⦂ = ⊢d-ann (⊢d-sub' ⊢d-int)
preserve (⊢d-ann ⊢e) (ξ-⦂ x M→N) = ⊢d-ann (preserve ⊢e M→N)
preserve (⊢d-ann ⊢e) (β-⦂ VN neq) = prv-value ⊢e VN neq
-- app1
preserve (⊢d-app₁ ⊢e ⊢e₁) (ξ-·₁ M→N) = ⊢d-app₁ (preserve ⊢e M→N) ⊢e₁
preserve (⊢d-app₁ ⊢e ⊢e₁) (ξ-·₂ x M→N) = ⊢d-app₁ ⊢e (preserve ⊢e₁ M→N)
preserve (⊢d-app₁ (⊢d-sub ⊢e Z≢Z) ⊢e₁) (β-ƛ x) = ⊥-elim (Z≢Z refl)
preserve (⊢d-app₁ (⊢d-ann (⊢d-lam-∞ ⊢e)) ⊢e₁) (β-ƛ⦂ x) = ⊢d-ann ({!!})
preserve (⊢d-app₁ (⊢d-ann (⊢d-sub (⊢d-sub ⊢e x₂) x₁)) ⊢e₁) (β-ƛ⦂ x) = ⊥-elim (x₂ refl)
preserve (⊢d-app₁ (⊢d-sub ⊢e Z≢Z) ⊢e₁) (β-ƛ⦂ x) = ⊥-elim (Z≢Z refl)
-- app2
preserve (⊢d-app₂ ⊢e ⊢e₁) (ξ-·₁ M→N) = ⊢d-app₂ (preserve ⊢e M→N) ⊢e₁
preserve (⊢d-app₂ ⊢e ⊢e₁) (ξ-·₂ x M→N) = ⊢d-app₂ ⊢e (preserve ⊢e₁ M→N)
-- beta
preserve (⊢d-app₂ (⊢d-lam-n ⊢e) ⊢e₁) (β-ƛ x) = {!!}
preserve (⊢d-app₂ (⊢d-sub (⊢d-sub ⊢e x₂) x₁) ⊢e₁) (β-ƛ x) = ⊥-elim (x₂ refl)
-- beta ann
preserve (⊢d-app₂ (⊢d-sub (⊢d-ann (⊢d-lam-∞ ⊢e)) x₁) ⊢e₁) (β-ƛ⦂ x) = ⊢d-sub' (⊢d-ann {!!})
preserve (⊢d-app₂ (⊢d-sub (⊢d-ann (⊢d-sub (⊢d-sub ⊢e x₃) x₂)) x₁) ⊢e₁) (β-ƛ⦂ x) = ⊥-elim (x₃ refl)

preserve (⊢d-app₂ (⊢d-sub (⊢d-sub ⊢e x₂) x₁) ⊢e₁) (β-ƛ⦂ x) = ⊥-elim (x₂ refl)
-- sub
preserve (⊢d-sub ⊢e x) M→N = ⊢d-sub' (preserve ⊢e M→N)
