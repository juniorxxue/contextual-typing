module Poly.Main where

open import Data.Nat renaming (_/_ to _/d_)  public
open import Data.Nat.Properties public
open import Data.String using (String) public
open import Relation.Nullary using (yes; no; Dec; ¬_) public
open import Relation.Nullary.Decidable using (True; toWitness; fromWitness) public
open import Function.Base using (case_of_; case_return_of_) public
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl; cong; sym; ≢-sym) public
open import Data.Empty public
open import Data.Product using (_×_; proj₁; proj₂; ∃; ∃-syntax) renaming (_,_ to ⟨_,_⟩) public
open import Data.List using (List; []; _∷_; _++_; reverse; foldr; downFrom) renaming (length to len) public
open import Data.List.Properties using (map-++) public
open import Data.Maybe using (Maybe; just; nothing)

pattern ⟦_⟧ z = z ∷ []

data Singleton {a} {A : Set a} (x : A) : Set a where
  _with≡_ : (y : A) → x ≡ y → Singleton x

inspect : ∀ {a} {A : Set a} (x : A) → Singleton x
inspect x = x with≡ refl

----------------------------------------------------------------------
--+                                                                +--
--+                             Syntax                             +--
--+                                                                +--
----------------------------------------------------------------------

infixr 5  ƛ_
infixl 7  _·_
infix  9  `_
infix  5  _⦂_
infix  5  Λ_
infix  5  _⟦_⟧

infix  9 ‶_
infixr 8 _`→_
infixr 8 `∀

data Type : Set where
  Int : Type
  ‶_ : ℕ → Type
  _`→_ : Type → Type → Type
  `∀ : Type → Type

data Term : Set where
  lit      : ℕ → Term
  `_       : ℕ → Term
  ƛ_       : Term → Term
  _·_      : Term → Term → Term
  _⦂_      : Term → Type → Term
  Λ_       : Term → Term
  _⟦_⟧ₐ     : Term → Type → Term

----------------------------------------------------------------------
--+                                                                +--
--+                         Binding Infra                          +--
--+                                                                +--
----------------------------------------------------------------------


Context : Set → Set
Context a = List (Maybe a)

lookup : ∀ {a} → ℕ → Context a → Maybe a
lookup n [] = nothing
lookup zero (x ∷ _) = x
lookup (suc n) (_ ∷ e) = lookup n e

raw-insert : ∀ {A} → ℕ → Maybe A → Context A → Context A
raw-insert zero o e = o ∷ e
raw-insert (suc n) o e@[] = nothing ∷ raw-insert n o e
raw-insert (suc n) o (x ∷ e) = x ∷ raw-insert n o e

insert : ∀ {A} → ℕ → A → Context A → Context A
insert n a e = raw-insert n (just a) e

raw-insert-zero : ∀ {A o} {e : Context A}
  → raw-insert 0 o e ≡ o ∷ e
raw-insert-zero = refl

lift : ℕ → ℕ → Term → Term
lift = {!!}

shift = lift 1

lift-type : ℕ → ℕ → Type → Type
lift-type = {!!}

shift-type = lift-type 1

subst : Term → ℕ → Term → Term
subst = {!!}

subst-type : Type → ℕ → Type → Type
subst-type = {!!}

⟦_/_⟧_ : Type → ℕ → Type → Type
⟦ A / n ⟧ B = subst-type A n B

map : ∀ {A B} → (f : A → B) → (e : Context A) → Context B
map f [] = []
map f (just x ∷ e) = just (f x) ∷ map f e
map f (nothing ∷ e) = nothing ∷ map f e

----------------------------------------------------------------------
--+                                                                +--
--+                              Decl                              +--
--+                                                                +--
----------------------------------------------------------------------

_,_ : Context Type → Type → Context Type
_,_ Γ A = insert 0 A Γ

_↑ : Context Type → Context Type
_↑ Γ = map (shift-type 0) Γ

data Counter : Set where
  ∞ : Counter
  Z : Counter
  S : Counter → Counter

infix 3 _⊢d_#_⦂_
infix 3 _⊢d_#_≤_

data _⊢d_#_≤_ : Context Type → Counter → Type → Type → Set where

  ≤d-refl : ∀ {Γ A}
    → Γ ⊢d Z # A ≤ A

  ≤d-int : ∀ {Γ}
    → Γ ⊢d ∞ # Int ≤ Int

  ≤d-arr-∞ : ∀ {Γ A B C D}
    → Γ ⊢d ∞ # C ≤ A
    → Γ ⊢d ∞ # B ≤ D
    → Γ ⊢d ∞ # A `→ B ≤ C `→ D

  ≤d-∀ : ∀ {Γ A B}
    → Γ ↑ ⊢d ∞ # A ≤ B
    → Γ ⊢d ∞ # `∀ A ≤ `∀ B

  ≤d-∀L : ∀ {Γ A B C j}
    -- B is well formed
    → (Γ ↑) ⊢d S j # (⟦ B / 0 ⟧ A) ≤ C
    → Γ ⊢d S j # `∀ A ≤ C


data _⊢d_#_⦂_ : Context Type → Counter → Term → Type → Set where

  ⊢d-lit : ∀ {Γ n}
    → Γ ⊢d Z # lit n ⦂ Int

  ⊢d-var : ∀ {Γ x A}
    → lookup x Γ ≡ just A
    → Γ ⊢d Z # ` x ⦂ A

  ⊢d-ann : ∀ {Γ e A}
    → Γ ⊢d ∞ # e ⦂ A
    → Γ ⊢d Z # (e ⦂ A) ⦂ A

  ⊢d-lam-∞ : ∀ {Γ e A B}
    → Γ , A ⊢d ∞ # e ⦂ B
    → Γ ⊢d ∞ # (ƛ e) ⦂ A `→ B

  ⊢d-lam-n : ∀ {Γ e A B j}
    → Γ , A ⊢d j # e ⦂ B
    → Γ ⊢d S j # (ƛ e) ⦂ A `→ B

  ⊢d-app₁ : ∀ {Γ e₁ e₂ A B}
    → Γ ⊢d Z # e₁ ⦂ A `→ B
    → Γ ⊢d ∞ # e₂ ⦂ A
    → Γ ⊢d Z # e₁ · e₂ ⦂ B

  ⊢d-app₂ : ∀ {Γ e₁ e₂ A B j}
    → Γ ⊢d (S j) # e₁ ⦂ A `→ B
    → Γ ⊢d Z # e₂ ⦂ A
    → Γ ⊢d j # e₁ · e₂ ⦂ B

  ⊢d-sub : ∀ {Γ e A A' j}
    → Γ ⊢d Z # e ⦂ A
    → Γ ⊢d j # A ≤ A'
    → j ≢ Z
    → Γ ⊢d j # e ⦂ A'

  ⊢d-ty-abs : ∀ {Γ j e A}
    → Γ ↑ ⊢d j # e ⦂ A
    → Γ ⊢d j # Λ e ⦂ `∀ A

  ⊢d-ty-app : ∀ {Γ j e A B B'}
    → Γ ⊢d j # e ⦂ `∀ B
    → ⟦ A / 0 ⟧ B ≡ B'
    → Γ ⊢d j # e ⟦ A ⟧ₐ ⦂ B'

