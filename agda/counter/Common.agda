module Common where

open import Data.Nat using (ℕ; zero; suc; _+_; _*_; _^_; _∸_; _≤?_; _≤_; s≤s)
open import Data.Nat.Properties
open import Data.String using (String)
open import Relation.Binary.PropositionalEquality
open import Relation.Nullary using (yes; no)
open import Function.Base using (case_of_; case_return_of_)
open import Data.Empty
open import Data.Product using (_×_; proj₁; proj₂; ∃; ∃-syntax) renaming (_,_ to ⟨_,_⟩)

Id : Set
Id = String

infixr 5  ƛ_
infixl 7  _·_
infix  9  `_
infix  5  _⦂_
infixr 8 _⇒_

data Type : Set where
  Int : Type
  Top : Type
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

----------------------------------------------------------------------
--+                                                                +--
--+                             Shift                              +--
--+                                                                +--
----------------------------------------------------------------------

infixl 7 _↑_
_↑_ : Term → ℕ → Term
lit i ↑ n = lit i
` x ↑ n with n ≤? x
... | yes n≤x = ` (suc x)
... | no  n>x = ` x
(ƛ e) ↑ n = ƛ (e ↑ (suc n))
e₁ · e₂ ↑ n = (e₁ ↑ n) · (e₂ ↑ n)
(e ⦂ A) ↑ n = (e ↑ n) ⦂ A

↑-idx : ℕ → ℕ → ℕ
↑-idx x n with n ≤? x
... | yes p = suc x
... | no ¬p = x

↑-var : ∀ x n → ` x ↑ n ≡ ` (↑-idx x n)
↑-var x n with n ≤? x
... | yes p = refl
... | no ¬p = refl

ƛ-injective : ∀ {e₁ e₂}
  → ƛ e₁ ≡ ƛ e₂
  → e₁ ≡ e₂
ƛ-injective refl = refl

app-injective : ∀ {e₁ e₂ e₃ e₄}
  → e₁ · e₂ ≡ e₃ · e₄
  → (e₁ ≡ e₃) × (e₂ ≡ e₄)
app-injective refl = ⟨ refl , refl ⟩

⦂-injective : ∀ {e₁ e₂ A B}
  → (e₁ ⦂ A) ≡ (e₂ ⦂ B)
  → (e₁ ≡ e₂) × (A ≡ B)
⦂-injective refl = ⟨ refl , refl ⟩

↑-injective : ∀ {e₁ e₂ n}
  → e₁ ↑ n ≡ e₂ ↑ n
  → e₁ ≡ e₂
↑-injective {lit x} {lit .x} {n} refl = refl
↑-injective {lit _} {` x} {n} eq
  rewrite ↑-var x n = case eq of λ ()
  
↑-injective {` x} {lit _} {n} eq
  rewrite ↑-var x n = case eq of λ ()
  
↑-injective {` x} {` y} {n} eq with n ≤? x | n ≤? y
↑-injective {` x} {` y} {n} refl | yes n≤x | yes n≤y = refl
↑-injective {` x} {` y} {n} refl | yes n≤x | no n>y = ⊥-elim (n>y (m≤n⇒m≤1+n n≤x))
↑-injective {` x} {` y} {n} refl | no n>x | yes n≤y = ⊥-elim (n>x (m≤n⇒m≤1+n n≤y))
↑-injective {` x} {` y} {n} refl | no n>x | no n>y = refl

↑-injective {` x} {ƛ e} {n} eq
  rewrite ↑-var x n = case eq of λ ()
↑-injective {` x} {e₁ · e₂} {n} eq
  rewrite ↑-var x n = case eq of λ ()
↑-injective {` x} {e ⦂ A} {n} eq
  rewrite ↑-var x n = case eq of λ ()
  
↑-injective {ƛ e} {` x} {n} eq
  rewrite ↑-var x n = case eq of λ ()
↑-injective {ƛ e₁} {ƛ e₂} {n} eq = cong ƛ_ (↑-injective (ƛ-injective eq))

↑-injective {e₁ · e₂} {` x} {n} eq
  rewrite ↑-var x n = case eq of λ ()
  
↑-injective {e₁ · e₂} {e₃ · e₄} {n} eq with app-injective eq
... | ⟨ eq₁ , eq₂ ⟩ = cong₂ _·_ (↑-injective eq₁) (↑-injective eq₂)

↑-injective {e ⦂ A} {` x} {n} eq
  rewrite ↑-var x n = case eq of λ ()
  
↑-injective {e₁ ⦂ A} {e₂ ⦂ B} {n} eq with ⦂-injective eq
... | ⟨ eq₁ , eq₂ ⟩ = cong₂ _⦂_ (↑-injective eq₁) eq₂

postulate

  ↑-↑-comm : ∀ e m n → m ≤ n → e ↑ m ↑ suc n ≡ e ↑ n ↑ m

{-
↑-↑-comm (lit _) m n m≤n = refl
↑-↑-comm (` x) m n m≤n with n ≤? x | m ≤? x
... | yes n≤x | yes m≤x = {!!}
... | yes n≤x | no  m>x = {!!}
... | no  n>x | yes m≤x = {!!}
... | no  n>x | no  m>x = {!!} 
↑-↑-comm (ƛ e) m n m≤n rewrite ↑-↑-comm e (suc m) (suc n) (s≤s m≤n) = refl
↑-↑-comm (e₁ · e₂) m n m≤n rewrite ↑-↑-comm e₁ m n m≤n | ↑-↑-comm e₂ m n m≤n = refl
↑-↑-comm (e ⦂ A) m n m≤n rewrite ↑-↑-comm e m n m≤n = refl
-}
