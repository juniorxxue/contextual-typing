module Poly.Main where

open import Data.Nat public
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

data Term : Set where
  tvar : ℕ → Term
  tabs : Term → Term
  tapp : Term → Term → Term
  ttyabs : Term → Term
  ttyapp : Term → Term

data Type : Set where
  tyvar : ℕ → Type
  tyarrow : Type → Type → Type
  tyforall : Type → Type

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

map : ∀ {A B} → (f : A → B) → (e : Context A) → Context B
map f [] = []
map f (just x ∷ e) = just (f x) ∷ map f e
map f (nothing ∷ e) = nothing ∷ map f e

infix 3 _⊢_⦂_

data _⊢_⦂_ : Context Type → Term → Type → Set where

  j-var : ∀ {Γ x A}
    → lookup x Γ ≡ just A
    → Γ ⊢ (tvar x) ⦂ A

  j-abs : ∀ {Γ e A B}
    → (insert 0 A Γ) ⊢ e ⦂ B
    → Γ ⊢ (tabs e) ⦂ (tyarrow A B)

  j-app : ∀ {Γ e₁ e₂ A B}
    → Γ ⊢ e₁ ⦂ (tyarrow A B)
    → Γ ⊢ e₂ ⦂ A
    → Γ ⊢ (tapp e₁ e₂) ⦂ B

  j-ty-abs : ∀ {Γ e A}
    → map (shift-type 0) Γ ⊢ e ⦂ A
    → Γ ⊢ (ttyabs e) ⦂ (tyforall A)

  j-ty-app : ∀ {Γ e A B B'}
    → Γ ⊢ e ⦂ (tyforall A)
    → subst-type B 0 A ≡ B'
    → Γ ⊢ (ttyapp e) ⦂ B'


