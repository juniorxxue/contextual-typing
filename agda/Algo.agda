module Algo where

open import Data.Nat using (ℕ)
open import Data.String using (String)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl)
open import Relation.Nullary using (¬_)
open import Data.Empty using (⊥; ⊥-elim)
open import Common

infixr 8 _*⇒_
infixr 8 ⟦_⟧

data Hype : Set where
  Hnt : Hype
  Hop : Hype
  _*⇒_  : Hype → Hype → Hype
  ⟦_⟧ : Term → Hype

data free : Term → Id → Set where
  free-var : ∀ {x} → free (` x) x
  free-lam : ∀ {x₁ x₂ e} → free e x₁ → x₁ ≢ x₂ → free (ƛ x₂ ⇒ e) x₁
  free-app-l : ∀ {e₁ e₂ x} → free e₁ x → free (e₁ · e₂) x
  free-app-r : ∀ {e₁ e₂ x} → free e₂ x → free (e₁ · e₂) x
  free-ann : ∀ {e A x} → free e x → free (e ⦂ A) x

data freeT : Hype → Id → Set where
  free-hole : ∀ {e x} → free e x → freeT (⟦ e ⟧) x

infix 5 _⊢a_≤_
infix 4 _⊢a_⇛_⇛_ 

data _⊢a_≤_ : Context → Hype → Hype → Set
data _⊢a_⇛_⇛_ : Context → Hype → Term → Type → Set

h : Type → Hype
h Int = Hnt
h Top = Hop
h (A ⇒ B) = (h A) *⇒ (h B)

-- unh : Hype → Type
-- unh Hnt = Int
-- unh Hop = Top
-- unh (A *⇒ B) = (unh A) ⇒ (unh B)

data _⊢a_≤_ where
  ≤a-int : ∀ {Γ}
    → Γ ⊢a Hnt ≤ Hnt
  ≤a-top : ∀ {Γ A}
    → Γ ⊢a A ≤ Hop
  ≤a-arr : ∀ {Γ A B C D}
    → Γ ⊢a C ≤ A
    → Γ ⊢a B ≤ D
    → Γ ⊢a (A *⇒ B) ≤ (C *⇒ D)
  ≤a-hole : ∀ {Γ A B e}
    → Γ ⊢a A ⇛ e ⇛ B
    → Γ ⊢a ⟦ e ⟧ ≤ A

data _⊢a_⇛_⇛_ where

  ⊢a-lit : ∀ {Γ A n}
    → Γ ⊢a Hnt ≤ A
    → Γ ⊢a A ⇛ lit n ⇛ Int

  ⊢a-var : ∀ {Γ A B x}
    → Γ ∋ x ⦂ B
    → Γ ⊢a h B ≤ A
    → Γ ⊢a A ⇛ ` x ⇛ B

  ⊢a-app : ∀ {Γ e₁ e₂ A C D}
    → Γ ⊢a ⟦ e₂ ⟧ *⇒ A ⇛ e₁ ⇛ (C ⇒ D)
    → Γ ⊢a A ⇛ e₁ · e₂ ⇛ D

  ⊢a-ann : ∀ {Γ e A B}
    → Γ ⊢a h B ⇛ e ⇛ B
    → Γ ⊢a h B ≤ A
    → Γ ⊢a A ⇛ e ⦂ B ⇛ B

  ⊢a-lam₁ : ∀ {Γ e₁ e x A B C}
    → Γ ⊢a Hop ⇛ e₁ ⇛ A
    → Γ , x ⦂ A ⊢a B ⇛ e ⇛ C
    → ¬ (freeT B x)
    → Γ ⊢a ⟦ e₁ ⟧ *⇒ B ⇛ ƛ x ⇒ e ⇛ A ⇒ C

  ⊢a-lam₂ : ∀ {Γ x e A B C}
    → Γ , x ⦂ A ⊢a B ⇛ e ⇛ C
    → Γ ⊢a h A *⇒ B ⇛ ƛ x ⇒ e ⇛ A ⇒ C


_ : ∅ ⊢a Hop ⇛ (ƛ "x" ⇒ ` "x") · lit 1 ⇛ Int
_ = ⊢a-app (⊢a-lam₁ (⊢a-lit ≤a-top) (⊢a-var Z ≤a-top) λ ())

_ : ∀ {x} → ¬ freeT Hop x
_ = λ ()

_ : ∅ ⊢a Hop ⇛ ((ƛ "f" ⇒ ` "f" · (lit 1)) ⦂ (Int ⇒ Int) ⇒ Int) · (ƛ "x" ⇒ ` "x") ⇛ Int
_ = ⊢a-app (⊢a-ann (⊢a-lam₂ (⊢a-app (⊢a-var Z (≤a-arr (≤a-hole (⊢a-lit ≤a-int)) ≤a-int)))) (≤a-arr (≤a-hole (⊢a-lam₂ {A = Int} (⊢a-var Z ≤a-int))) ≤a-top))
