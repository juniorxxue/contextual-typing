module TypeSound.Elaboration.STLC.Common where

open import Data.Bool using (Bool; true; false; T; not) public
open import Data.Empty using (⊥; ⊥-elim) public
open import Data.List using (List; _∷_; []) public
open import Data.Nat using (ℕ; zero; suc) public
open import Data.Product using (∃-syntax; _×_) public
open import Data.String using (String; _≟_) public
open import Data.Unit using (tt) public
open import Relation.Nullary using (Dec; yes; no; ¬_) public
open import Relation.Nullary.Decidable using (False; toWitnessFalse) public
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl) public
open import Data.Product using (_×_; proj₁; proj₂; ∃; ∃-syntax) renaming (_,_ to ⟨_,_⟩) public
open import Data.Sum using (_⊎_; inj₁; inj₂) renaming ([_,_] to case-⊎) public

data Singleton {a} {A : Set a} (x : A) : Set a where
  _with≡_ : (y : A) → x ≡ y → Singleton x

inspect : ∀ {a} {A : Set a} (x : A) → Singleton x
inspect x = x with≡ refl


Id : Set
Id = String

infixr 8 _⇒_

data Type : Set where
  Int : Type
  _⇒_ : Type → Type → Type

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
