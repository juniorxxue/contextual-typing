module AllOrNothing where

open import Data.Nat public
open import Data.Nat.Properties public
open import Data.String using (String) public
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl; cong; sym; ≢-sym) public

Id : Set
Id = String

infixr 5  ƛ_⇒_
infixl 7  _·_
infix  9  `_
infixr 6  _⦂_
infixr 8  _⇒_

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
    → Γ , x ⦂ A ∋ x ⦂ A

  S : ∀ {Γ x y A B}
    → x ≢ y
    → Γ ∋ x ⦂ A
    → Γ , y ⦂ B ∋ x ⦂ A

----------------------------------------------------------------------
--+                                                                +--
--+          Traditional Bidirectional Typing                      +--
--+                                                                +--
----------------------------------------------------------------------

-- we add App2 and switch the direction of Lit rule to inference

data Mode : Set where
  c : Mode
  i : Mode

infix 4 _⊢b_#_⦂_

data _⊢b_#_⦂_ : Context → Mode → Term → Type → Set where

  ⊢b-int : ∀ {Γ n}
    → Γ ⊢b i # (lit n) ⦂ Int

  ⊢b-var : ∀ {Γ x A}
    → Γ ∋ x ⦂ A
    → Γ ⊢b i # ` x ⦂ A

  ⊢b-ann : ∀ {Γ e A}
    → Γ ⊢b c # e ⦂ A
    → Γ ⊢b i # (e ⦂ A) ⦂ A

  ⊢b-lam-∞ : ∀ {Γ e x A B}
    → Γ , x ⦂ A ⊢b c # e ⦂ B
    → Γ ⊢b c # (ƛ x ⇒ e) ⦂ A ⇒ B

  ⊢b-app₁ : ∀ {Γ e₁ e₂ A B}
    → Γ ⊢b i # e₁ ⦂ A ⇒ B
    → Γ ⊢b c # e₂ ⦂ A
    → Γ ⊢b i # e₁ · e₂ ⦂ B

  ⊢b-app₂ : ∀ {Γ e₁ e₂ A B}
    → Γ ⊢b c # e₁ ⦂ A ⇒ B
    → Γ ⊢b i # e₂ ⦂ A
    → Γ ⊢b c # e₁ · e₂ ⦂ B

  ⊢b-sub : ∀ {Γ e A B}
    → Γ ⊢b i # e ⦂ A
    → A ≡ B
    → Γ ⊢b c # e ⦂ B


----------------------------------------------------------------------
--+                                                                +--
--+                        QTAS                                    +--
--+                                                                +--
----------------------------------------------------------------------

data Counter : Set where
  ∞ : Counter
  Z : Counter

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

  ⊢d-app₁ : ∀ {Γ e₁ e₂ A B}
    → Γ ⊢d Z # e₁ ⦂ A ⇒ B
    → Γ ⊢d ∞ # e₂ ⦂ A
    → Γ ⊢d Z # e₁ · e₂ ⦂ B

  ⊢d-app₂ : ∀ {Γ e₁ e₂ A B}
    → Γ ⊢d ∞ # e₁ ⦂ A ⇒ B
    → Γ ⊢d Z # e₂ ⦂ A
    → Γ ⊢d ∞ # e₁ · e₂ ⦂ B

  ⊢d-sub : ∀ {Γ e A B}
    → Γ ⊢d Z # e ⦂ A
    → A ≡ B
    → Γ ⊢d ∞ # e ⦂ B


----------------------------------------------------------------------
--+                                                                +--
--+                     Sound and Complete                         +--
--+                                                                +--
----------------------------------------------------------------------

data R : Mode → Counter → Set where
  R-Z : R i Z
  R-∞ : R c ∞

complete : ∀ {Γ m n e A}
  → Γ ⊢b m # e ⦂ A
  → R m n
  → Γ ⊢d n # e ⦂ A
complete (⊢b-var x) R-Z = ⊢d-var x
complete (⊢b-ann ⊢e) R-Z = ⊢d-ann (complete ⊢e R-∞)
complete (⊢b-app₁ ⊢e ⊢e₁) R-Z = ⊢d-app₁ (complete ⊢e R-Z) (complete ⊢e₁ R-∞)
complete ⊢b-int R-Z = ⊢d-int
complete (⊢b-lam-∞ ⊢e) R-∞ = ⊢d-lam-∞ (complete ⊢e R-∞)
complete (⊢b-app₂ ⊢e ⊢e₁) R-∞ = ⊢d-app₂ (complete ⊢e R-∞) (complete ⊢e₁ R-Z)
complete (⊢b-sub ⊢e x) R-∞ = ⊢d-sub (complete ⊢e R-Z) x

sound : ∀ {Γ m n e A}
  → Γ ⊢d n # e ⦂ A
  → R m n
  → Γ ⊢b m # e ⦂ A
sound ⊢d-int R-Z = ⊢b-int
sound (⊢d-var x) R-Z = ⊢b-var x
sound (⊢d-ann ⊢e) R-Z = ⊢b-ann (sound ⊢e R-∞)
sound (⊢d-app₁ ⊢e ⊢e₁) R-Z = ⊢b-app₁ (sound ⊢e R-Z) (sound ⊢e₁ R-∞)
sound (⊢d-lam-∞ ⊢e) R-∞ = ⊢b-lam-∞ (sound ⊢e R-∞)
sound (⊢d-app₂ ⊢e ⊢e₁) R-∞ = ⊢b-app₂ (sound ⊢e R-∞) (sound ⊢e₁ R-Z)
sound (⊢d-sub ⊢e x) R-∞ = ⊢b-sub (sound ⊢e R-Z) x

-- corollaries

sound-inf : ∀ {Γ e A}
  → Γ ⊢d Z # e ⦂ A
  → Γ ⊢b i # e ⦂ A
sound-inf ⊢e = sound ⊢e R-Z

sound-chk : ∀ {Γ e A}
  → Γ ⊢d ∞ # e ⦂ A
  → Γ ⊢b c # e ⦂ A
sound-chk ⊢e = sound ⊢e R-∞

complete-inf : ∀ {Γ e A}
  → Γ ⊢b i # e ⦂ A
  → Γ ⊢d Z # e ⦂ A
complete-inf ⊢e = complete ⊢e R-Z

complete-chk : ∀ {Γ e A}
  → Γ ⊢b c # e ⦂ A
  → Γ ⊢d ∞ # e ⦂ A
complete-chk ⊢e = complete ⊢e R-∞


