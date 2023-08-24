module CheckSub.Main where

open import Data.Nat public
open import Data.Nat.Properties public
open import Data.String using (String) public
open import Relation.Nullary using (yes; no; Dec; ¬_) public
open import Relation.Nullary.Decidable using (True; toWitness; fromWitness) public
open import Function.Base using (case_of_; case_return_of_) public
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl; cong; sym; ≢-sym) public
open import Data.Empty public
open import Data.Product using (_×_; proj₁; proj₂; ∃; ∃-syntax) renaming (_,_ to ⟨_,_⟩) public
open import Data.List using (List; []; _∷_; _++_; reverse; map; foldr; downFrom) public

infixr 5  ƛ_
infixl 7  _·_
infix  9  `_
infix  5  _⦂_
infixr 8 _⇒_

data Type : Set where
  Int : Type
  Top : Type
  Bot : Type
  _⇒_ : Type → Type → Type

data Term : Set where
  lit      : ℕ → Term
  `_       : ℕ → Term
  ƛ_       : Term → Term
  _·_      : Term → Term → Term
  _⦂_      : Term → Type → Term

infixl 5  _,_

data Context : Set where
  ∅     : Context
  _,_   : Context → Type → Context

infix  4  _∋_⦂_

data _∋_⦂_ : Context → ℕ → Type → Set where

  Z : ∀ {Γ A}
      ------------------
    → Γ , A ∋ zero ⦂ A

  S : ∀ {Γ A B n}
    → Γ ∋ n ⦂ A
      ------------------
    → Γ , B ∋ (suc n) ⦂ A

infix 5 _<:_
data _<:_ : Type → Type → Set where
  ≤int :
      Int <: Int
  ≤top : ∀ {A}
    → A <: Top
  ≤bot : ∀ {A}
    → Bot <: A
  ≤arr : ∀ {A B C D}
    → C <: A
    → B <: D
    → (A ⇒ B) <: (C ⇒ D)
   

infix 4 _⊢_⇒_
infix 4 _⊢_⇐_

data _⊢_⇒_ : Context → Term → Type → Set
data _⊢_⇐_ : Context → Term → Type → Set

data _⊢_⇒_ where

  ⊢int : ∀ {Γ n}
    → Γ ⊢ lit n ⇒ Int

  ⊢var : ∀ {Γ x A}
    → Γ ∋ x ⦂ A
    → Γ ⊢ ` x ⇒ A

  ⊢app₁ : ∀ {Γ e₁ e₂ A B}
    → Γ ⊢ e₁ ⇒ (A ⇒ B)
    → Γ ⊢ e₂ ⇐ A
    → Γ ⊢ e₁ · e₂ ⇒ B

  ⊢ann : ∀ {Γ e A}
    → Γ ⊢ e ⇐ A
    → Γ ⊢ (e ⦂ A) ⇒ A

data _⊢_⇐_ where

  ⊢lam : ∀ {Γ e A B}
    → Γ , A ⊢ e ⇐ B
    → Γ ⊢ ƛ e ⇐ (A ⇒ B)

  ⊢app₂ : ∀ {Γ e₁ e₂ A B}
    → Γ ⊢ e₁ ⇐ (A ⇒ B)
    → Γ ⊢ e₂ ⇒ A
    → Γ ⊢ e₁ · e₂ ⇐ B

  ⊢sub : ∀ {Γ e A B}
    → Γ ⊢ e ⇒ B
    → B <: A
    → Γ ⊢ e ⇐ A

infix 6 _>>_
_>>_ : Context → Context → Context
Γ₁ >> ∅ = Γ₁
Γ₁ >> (Γ₂ , A) = (Γ₁ >> Γ₂) , A


check-sub : ∀ {Γ e A B}
  → Γ ⊢ e ⇐ A
  → A <: B
  → Γ ⊢ e ⇐ B
  
narrow : ∀ {Γ₁ Γ₂ A A' B e}
  → (Γ₁ , A) >> Γ₂ ⊢ e ⇐ B
  → A' <: A
  → ∃[ B' ] ((Γ₁ , A') >> Γ₂ ⊢ e ⇐ B') × (B' <: B)

narrow' : ∀ {Γ₁ Γ₂ A A' B e}
  → (Γ₁ , A) >> Γ₂ ⊢ e ⇒ B
  → A' <: A
  → ∃[ B' ] ((Γ₁ , A') >> Γ₂ ⊢ e ⇒ B') × (B' <: B)


check-sub (⊢lam ⊢e) ≤top = {!!}
check-sub (⊢lam ⊢e) (≤arr A<B A<B₁) = ⊢lam (check-sub {!!} {!!}) -- subject to narrowing lemma
check-sub (⊢app₂ ⊢e x) A<B = ⊢app₂ (check-sub ⊢e (≤arr {!!} A<B)) x
check-sub (⊢sub x x₁) A<B = {!!}

narrow (⊢lam ⊢e) sub = {!!}
narrow (⊢app₂ ⊢e x) sub with narrow ⊢e sub | narrow' x sub
... | ⟨ E , ⟨ fst , snd ⟩ ⟩ | ⟨ F , ⟨ fst₁ , snd₁ ⟩ ⟩ = {!!}
narrow (⊢sub x x₁) sub = {!!}

narrow' ⊢int sub = {!!}
narrow' (⊢var x) sub = {!!}
narrow' (⊢app₁ ⊢e x) sub = {!!}
narrow' (⊢ann x) sub = {!!}
