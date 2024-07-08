module Application where

open import Data.Nat public
open import Data.Nat.Properties public
open import Data.String using (String) public
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl; cong; sym; ≢-sym) public

Id : Set
Id = String

infixr 5  ƛ_⇒_
infixl 7  _·_
infix  9  `_
infixr 8  _⇒_

data Type : Set where
  Int : Type
  _⇒_ : Type → Type → Type

data Term : Set where
  lit      : ℕ → Term
  `_       : Id → Term
  ƛ_⇒_     : Id → Term → Term
  _·_      : Term → Term → Term

infixl 5  _,_⦂_

data Context : Set where
  ∅     : Context
  _,_⦂_ : Context → Id → Type → Context

infix  4  _∋_⦂_

data _∋_⦂_ : Context → Id → Type → Set where

  Z : ∀ {Γ x A}
    → Γ , x ⦂ A ∋ x ⦂ A

  S : ∀ {Γ x y A B}
    → x ≢ y
    → Γ ∋ x ⦂ A
    → Γ , y ⦂ B ∋ x ⦂ A


----------------------------------------------------------------------
--+                                                                +--
--+                     Let Argument Go First                      +--
--+                                                                +--
----------------------------------------------------------------------

data AppContext : Set where
  ∅     : AppContext
  _,,_   : AppContext → Type → AppContext

infix 3 _~_⊢_⇒_

data _~_⊢_⇒_ : Context → AppContext → Term → Type → Set where

  ⊢int : ∀ {Γ n}
    → Γ ~ ∅ ⊢ lit n ⇒ Int

  ⊢var : ∀ {Γ x A}
    → Γ ∋ x ⦂ A
    → Γ ~ ∅ ⊢ ` x ⇒ A

  ⊢lam : ∀ {Γ : Context} {Ψ : AppContext} {e x A B}
    → (Γ , x ⦂ A) ~ Ψ ⊢ e ⇒ B
    → Γ ~ (Ψ ,, A) ⊢ (ƛ x ⇒ e) ⇒ (A ⇒ B)

  ⊢app : ∀ {Γ Ψ e₁ e₂ A B}
    → Γ ~ ∅ ⊢ e₂ ⇒ A
    → Γ ~ Ψ ,, A ⊢ e₁ ⇒ (A ⇒ B)
    → Γ ~ Ψ ⊢ e₁ · e₂ ⇒ B


----------------------------------------------------------------------
--+                                                                +--
--+                              QTAS                              +--
--+                                                                +--
----------------------------------------------------------------------

data Counter : Set where
  Z : Counter
  S : Counter → Counter


infix 4 _⊢d_#_⦂_

data _⊢d_#_⦂_ : Context → Counter → Term → Type → Set where

  ⊢d-int : ∀ {Γ i}
    → Γ ⊢d Z # (lit i) ⦂ Int

  ⊢d-var : ∀ {Γ x A}
    → Γ ∋ x ⦂ A
    → Γ ⊢d Z # ` x ⦂ A

  ⊢d-lam : ∀ {Γ e x A B n}
    → Γ , x ⦂ A ⊢d n # e ⦂ B
    → Γ ⊢d S n # (ƛ x ⇒ e) ⦂ A ⇒ B

  ⊢d-app : ∀ {Γ e₁ e₂ A B n}
    → Γ ⊢d (S n) # e₁ ⦂ A ⇒ B
    → Γ ⊢d Z # e₂ ⦂ A
    → Γ ⊢d n # e₁ · e₂ ⦂ B


----------------------------------------------------------------------
--+                                                                +--
--+                       Sound and Complete                       +--
--+                                                                +--
----------------------------------------------------------------------

data R : AppContext → Counter → Type → Set where

  R-Z : ∀ {A} → R ∅ Z A
  
  R-S : ∀ {Ψ n A B}
    → R Ψ n B
    → R (Ψ ,, A) (S n) (A ⇒ B)

complete : ∀ {Γ Ψ n e A}
  → Γ ~ Ψ ⊢ e ⇒ A
  → R Ψ n A
  → Γ ⊢d n # e ⦂ A
complete ⊢int R-Z = ⊢d-int
complete (⊢var x) R-Z = ⊢d-var x
complete (⊢lam ⊢e) (R-S r) = ⊢d-lam (complete ⊢e r)
complete (⊢app ⊢e ⊢e₁) r = ⊢d-app (complete ⊢e₁ (R-S r)) (complete ⊢e R-Z)

sound : ∀ {Γ Ψ n e A}
  → Γ ⊢d n # e ⦂ A
  → R Ψ n A
  → Γ ~ Ψ ⊢ e ⇒ A
sound ⊢d-int R-Z = ⊢int
sound (⊢d-var x) R-Z = ⊢var x
sound (⊢d-lam ⊢e) (R-S r) = ⊢lam (sound ⊢e r)
sound (⊢d-app ⊢e ⊢e₁) r = ⊢app (sound ⊢e₁ R-Z) (sound ⊢e (R-S r))
