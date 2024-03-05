module Complete.Trad where

open import Complete.Prelude

Id : Set
Id = String

infixr 5  ƛ_⇒_
infixl 7  _·_
infix  9  `_
infixr 6  _⦂_
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

----------------------------------------------------------------------
--+                                                                +--
--+          Traditional Bidirectional Typing                      +--
--+                                                                +--
----------------------------------------------------------------------

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

  ⊢b-sub : ∀ {Γ e A}
    → Γ ⊢b i # e ⦂ A
    → Γ ⊢b c # e ⦂ A


----------------------------------------------------------------------
--+                                                                +--
--+                         Counter Typing                         +--
--+                                                                +--
----------------------------------------------------------------------

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


----------------------------------------------------------------------
--+                                                                +--
--+                          Completeness                          +--
--+                                                                +--
----------------------------------------------------------------------

data R : Mode → Counter → Set where

  R-Z : R i Z
  
  R-∞ : R c ∞

  R-S : ∀ {j}
    → R c j
    → R c (S j)

complete : ∀ {Γ m j e A}
  → Γ ⊢b m # e ⦂ A
  → R m j
  → Γ ⊢d j # e ⦂ A
complete ⊢b-int R-Z = ⊢d-int
complete (⊢b-var x) R-Z = ⊢d-var x
complete (⊢b-ann ⊢e) R-Z = ⊢d-ann (complete ⊢e R-∞)
complete (⊢b-lam-∞ ⊢e) R-∞ = ⊢d-lam-∞ (complete ⊢e R-∞)
complete (⊢b-lam-∞ x) (R-S x₁) = ⊢d-lam-n (complete x x₁)
complete (⊢b-app₁ ⊢e ⊢e₁) R-Z = ⊢d-app₁ (complete ⊢e R-Z) (complete ⊢e₁ R-∞)
complete (⊢b-app₂ ⊢e ⊢e₁) R-∞ = ⊢d-app₂ (complete ⊢e (R-S R-∞)) (complete ⊢e₁ R-Z)
complete (⊢b-app₂ x x₁) (R-S x₂) = ⊢d-app₂ (complete x (R-S (R-S x₂))) (complete x₁ R-Z)
complete (⊢b-sub ⊢e) R-∞ = ⊢d-sub (complete ⊢e R-Z) λ ()
complete (⊢b-sub ⊢e) (R-S r) = ⊢d-sub (complete ⊢e R-Z) λ ()
