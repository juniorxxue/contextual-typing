module Complete.LetArg where

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

data R : AppContext → Counter → Set where

  R-Z : R ∅ Z
  
  R-S : ∀ {Ψ j A}
    → R Ψ j
    → R (Ψ ,, A) (S j)

complete : ∀ {Γ Ψ j e A}
  → Γ ~ Ψ ⊢ e ⇒ A
  → R Ψ j
  → Γ ⊢d j # e ⦂ A
complete ⊢int R-Z = ⊢d-int
complete (⊢var x) R-Z = ⊢d-var x
complete (⊢lam ⊢e) (R-S ψj) = ⊢d-lam-n (complete ⊢e ψj)
complete (⊢app ⊢e₂ ⊢e₁) ψj = ⊢d-app₂ (complete ⊢e₁ (R-S ψj)) (complete ⊢e₂ R-Z)
