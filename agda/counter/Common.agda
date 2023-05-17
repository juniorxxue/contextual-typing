module Common where

open import Prelude hiding (_≤?_)
open import Data.Nat.Tactic.RingSolver

  
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
abstract
  _≤?_ : (x y : ℕ) → Dec (x ≤ y)
  _≤?_ = Prelude._≤?_

↑-var : ℕ → ℕ → ℕ
↑-var n x with n ≤? x
... | yes n≤x = suc x
... | no  n>x = x

infixl 7 _↑_
_↑_ : Term → ℕ → Term
lit i ↑ n = lit i
` x ↑ n = ` (↑-var n x)
(ƛ e) ↑ n = ƛ (e ↑ (suc n))
e₁ · e₂ ↑ n = (e₁ ↑ n) · (e₂ ↑ n)
(e ⦂ A) ↑ n = (e ↑ n) ⦂ A

↓-var : ℕ → ℕ → ℕ
↓-var n x with (suc n) ≤? x
... | yes n+1≤x = pred x
... | no n+1>x   = x

infixl 7 _↓_
_↓_ : Term → ℕ → Term
lit i ↓ n = lit i
` x ↓ n = ` (↓-var n x)
(ƛ e) ↓ n = ƛ (e ↓ (suc n))
e₁ · e₂ ↓ n = (e₁ ↓ n) · (e₂ ↓ n)
(e ⦂ A) ↓ n = (e ↓ n) ⦂ A

↓-↑-var : ∀ x n → ↓-var n (↑-var n x) ≡ x
↓-↑-var x n with n ≤? x
...         | yes n≤x with suc n ≤? suc x
...                   | yes n+1≤x+1 = pred-suc x
                            where pred-suc : ∀ n → pred (suc n) ≡ n
                                  pred-suc zero = refl
                                  pred-suc (suc n) = refl
...                   | no  n+1>x+1 = ⊥-elim (n+1>x+1 (s≤s n≤x))
↓-↑-var x n | no n>x with suc n ≤? x
...                   | yes n+1≤x = ⊥-elim (n>x (n+1≤x→n≤x n+1≤x))
                            where n+1≤x→n≤x : ∀ {n x} → suc n ≤ x → n ≤ x
                                  n+1≤x→n≤x n+1≤x = ≤-pred (m≤n⇒m≤1+n n+1≤x)
...                   | no  n+1>x = refl

↑-↑-comm-var : ∀ m n x
  → m ≤ n
  → ↑-var (suc n) (↑-var m x) ≡ ↑-var m (↑-var n x)
↑-↑-comm-var m n x m≤n with m ≤? x | n ≤? x
...               | yes m≤x | yes n≤x with suc n ≤? suc x | m ≤? suc x
...                                   | yes n+1≤x+1 | yes m≤x+1 = refl
...                                   | yes n+1≤x+1 | no  m≰x+1 = ⊥-elim (m≰x+1 (m≤n⇒m≤1+n m≤x))
...                                   | no  n+1≰x+1 | yes m≤x+1 = ⊥-elim (n+1≰x+1 (s≤s n≤x))
...                                   | no  n+1≰x+1 | no  m≰x+1 = refl
↑-↑-comm-var m n x m≤n | yes m≤x | no n≰x  with suc n ≤? suc x | m ≤? x
...                                   | yes n+1≤x+1 | yes m≤x = ⊥-elim (n≰x (≤-pred n+1≤x+1))
...                                   | yes n+1≤x+1 | no  m≰x = ⊥-elim (m≰x m≤x)
...                                   | no  n+1≰x+1 | yes m≤x = refl
...                                   | no  n+1≰x+1 | no  m≰x = ⊥-elim (m≰x m≤x)
↑-↑-comm-var m n x m≤n | no  m≰x | yes n≤x with suc n ≤? x | m ≤? suc x
...                                   | yes n+1≤x | yes m≤x+1 = ⊥-elim (m≰x (≤-trans m≤n n≤x))
...                                   | yes n+1≤x | no  m≰x+1 = refl
...                                   | no  n+1≰x | yes m≤x+1 = ⊥-elim (m≰x (≤-trans m≤n n≤x))
...                                   | no  n+1≰x | no  m≰x+1 = ⊥-elim (m≰x (≤-trans m≤n n≤x))
↑-↑-comm-var m n x m≤n | no  m≰x | no n≰x  with suc n ≤? x | m ≤? x
...                                   | yes n+1≤x | yes m≤x = refl
...                                   | yes n+1≤x | no  m≰x = ⊥-elim (n≰x (m+1≤n→m≤n n+1≤x))
...                                   | no  n+1≰x | yes m≤x = ⊥-elim (m≰x m≤x)
...                                   | no  n+1≰x | no  m≰x = refl


↑-↑-comm : ∀ e m n → m ≤ n → e ↑ m ↑ suc n ≡ e ↑ n ↑ m
↑-↑-comm (lit _) m n m≤n = refl
↑-↑-comm (` x) m n m≤n = cong `_ (↑-↑-comm-var m n x m≤n)
↑-↑-comm (ƛ e) m n m≤n rewrite ↑-↑-comm e (suc m) (suc n) (s≤s m≤n) = refl
↑-↑-comm (e₁ · e₂) m n m≤n rewrite ↑-↑-comm e₁ m n m≤n | ↑-↑-comm e₂ m n m≤n = refl
↑-↑-comm (e ⦂ A) m n m≤n rewrite ↑-↑-comm e m n m≤n = refl

↓-↑-comm-var : ∀ m n x
  → m ≤ n
  → ↑-var m (↓-var n x) ≡ ↓-var (suc n) (↑-var m x)
↓-↑-comm-var m n x m≤n with (suc n) ≤? x | m ≤? x
...                    | yes n+1≤x | yes m≤x with m ≤? pred x | suc (suc n) ≤? suc x
...                                          | yes m≤x-1 | yes n+2≤x+1 = n-1+1≡n+1-1 (m<n⇒0<n n+1≤x)
...                                          | yes m≤x-1 | no  n+2≰x+1 = ⊥-elim (n+2≰x+1 (s≤s n+1≤x))
...                                          | no  m≰x-1 | yes n+2≤x+1 = ⊥-elim (m≰x-1 (≤-trans m≤n (<⇒≤pred (n+1≤x))))
...                                          | no  m≰x-1 | no  n+2≰x+1 = ⊥-elim (m≰x-1 (≤-trans m≤n (<⇒≤pred (n+1≤x))))
↓-↑-comm-var m n x m≤n | yes n+1≤x | no  n≰x with m ≤? pred x | suc (suc n) ≤? x
...                                          | yes m≤x-1 | yes n+2≤x = ⊥-elim (n≰x (≤pred⇒≤ (m≤x-1)))
...                                          | yes m≤x-1 | no  n+2≰x = n-1+1≡n+1-1 (m<n⇒0<n n+1≤x)
...                                          | no  m≰x-1 | yes n+2≤x = refl
...                                          | no  m≰x-1 | no  n+2≰x = ⊥-elim (m≰x-1 (≤-trans m≤n (<⇒≤pred (n+1≤x))))
↓-↑-comm-var m n x m≤n | no  n+1≰x | yes m≤x with m ≤? x | suc (suc n) ≤? suc x
...                                          | yes m≤x | yes n+2≤x+1 = ⊥-elim (n+1≰x (≤-pred n+2≤x+1))
...                                          | yes m≤x | no  n+2≰x+1 = refl
...                                          | no  m≰x | yes n+2≤x+1 = refl
...                                          | no  m≰x | no  n+2≰x+1 = ⊥-elim (m≰x m≤x)
↓-↑-comm-var m n x m≤n | no  n+1≰x | no  m≰x with m ≤? x | suc (suc n) ≤? x
...                                          | yes m≤x | yes n+2≤x = ⊥-elim (m≰x m≤x)
...                                          | yes m≤x | no  n+2≰x = ⊥-elim (m≰x m≤x)
...                                          | no  m≰x | yes n+2≤x = ⊥-elim (n+1≰x (m+1≤n→m≤n n+2≤x))
...                                          | no  m≰x | no  n+2≰x = refl

↓-↑-comm : ∀ e m n
  → m ≤ n
  → e ↓ n ↑ m ≡ e ↑ m ↓ (suc n)
↓-↑-comm (lit x) m n m≤n = refl
↓-↑-comm (` x) m n m≤n = cong `_ (↓-↑-comm-var m n x m≤n)
↓-↑-comm (ƛ e) m n m≤n rewrite ↓-↑-comm e (suc m) (suc n) (s≤s m≤n) = refl
↓-↑-comm (e₁ · e₂) m n m≤n rewrite ↓-↑-comm e₁ m n m≤n | ↓-↑-comm e₂ m n m≤n = refl
↓-↑-comm (e ⦂ A) m n m≤n rewrite ↓-↑-comm e m n m≤n = refl
