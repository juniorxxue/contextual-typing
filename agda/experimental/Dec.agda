module Dec where

open import Data.Nat using (ℕ)
open import Data.String using (String)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl)
open import Common

infix 5 _≤d_

data _≤d_ : Type → Type → Set where
  ≤d-int :
      Int ≤d Int
  ≤d-top : ∀ {A}
    → A ≤d Top
  ≤d-arr : ∀ {A B C D}
    → C ≤d A
    → B ≤d D
    → A ⇒ B ≤d C ⇒ D    

data Mode : Set where
  ⇛ : Mode
  ⇚ : Mode

infix 4 _⊢d_∙_∙_

data _⊢d_∙_∙_ : Context → Term → Mode → Type → Set where
  ⊢d-int : ∀ {Γ n}
    → Γ ⊢d (lit n) ∙ ⇛ ∙ Int

  ⊢d-var : ∀ {Γ x A}
    → Γ ∋ x ⦂ A
    → Γ ⊢d ` x ∙ ⇛ ∙ A

  ⊢d-lam : ∀ {Γ x e A B}
    → Γ , x ⦂ A ⊢d e ∙ ⇚ ∙ B
    → Γ ⊢d (ƛ x ⇒ e) ∙ ⇚ ∙ A ⇒ B

  ⊢d-app₁ : ∀ {Γ e₁ e₂ A B}
    → Γ ⊢d e₁ ∙ ⇛ ∙ A ⇒ B
    → Γ ⊢d e₂ ∙ ⇚ ∙ A
    → Γ ⊢d e₁ · e₂ ∙ ⇛ ∙ B

  ⊢d-app₂ : ∀ {Γ e₁ e₂ A B}
    → Γ ⊢d e₁ ∙ ⇚ ∙ A ⇒ B
    → Γ ⊢d e₂ ∙ ⇛ ∙ A
    → Γ ⊢d e₁ · e₂ ∙ ⇛ ∙ B

  ⊢d-ann : ∀ {Γ e A}
    → Γ ⊢d e ∙ ⇚ ∙ A
    → Γ ⊢d e ⦂ A ∙ ⇛ ∙ A

  ⊢d-sub : ∀ {Γ e A B}
    → Γ ⊢d e ∙ ⇛ ∙ B
    → B ≤d A
    → Γ ⊢d e ∙ ⇚ ∙ A

_ : (Int ⇒ Int) ≤d (Int ⇒ Top)
_ = ≤d-arr ≤d-int ≤d-top

_ : ∅ ⊢d (ƛ "x" ⇒ ` "x") · lit 1 ∙ ⇛ ∙ Int
_ = ⊢d-app₂ (⊢d-lam (⊢d-sub (⊢d-var Z) ≤d-int)) ⊢d-int

≤d-refl : ∀ {A} → A ≤d A
≤d-refl {Int} = ≤d-int
≤d-refl {Top} = ≤d-top
≤d-refl {A ⇒ B} = ≤d-arr ≤d-refl ≤d-refl

_ : ∅ ⊢d ((ƛ "f" ⇒ ` "f" · (lit 1)) ⦂ (Int ⇒ Int) ⇒ Int) · (ƛ "x" ⇒ ` "x") ∙ ⇛ ∙ Int
_ = ⊢d-app₁ (⊢d-ann (⊢d-lam (⊢d-sub (⊢d-app₁ (⊢d-var Z) (⊢d-sub ⊢d-int ≤d-int)) ≤d-int))) (⊢d-lam (⊢d-sub (⊢d-var Z) ≤d-int))
