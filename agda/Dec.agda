module Dec where

open import Data.Nat using (ℕ)
open import Data.String using (String)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl)
open import Common

infix 5 _≤_

data _≤_ : Type → Type → Set where
  ≤-int :
      Int ≤ Int
  ≤-top : ∀ {A}
    → A ≤ Top
  ≤-arr : ∀ {A B C D}
    → C ≤ A
    → B ≤ D
    → A ⇒ B ≤ C ⇒ D    

data Mode : Set where
  ⇛ : Mode
  ⇚ : Mode

infix  4  _⊢_∙_∙_

data _⊢_∙_∙_ : Context → Term → Mode → Type → Set where
  ty-int : ∀ {Γ n}
    → Γ ⊢ (lit n) ∙ ⇛ ∙ Int

  ty-var : ∀ {Γ x A}
    → Γ ∋ x ⦂ A
    → Γ ⊢ ` x ∙ ⇛ ∙ A

  ty-lam : ∀ {Γ x e A B}
    → Γ , x ⦂ A ⊢ e ∙ ⇚ ∙ B
    → Γ ⊢ ƛ x ⇒ e ∙ ⇚ ∙ A ⇒ B

  ty-app₁ : ∀ {Γ e₁ e₂ A B}
    → Γ ⊢ e₁ ∙ ⇛ ∙ A ⇒ B
    → Γ ⊢ e₂ ∙ ⇚ ∙ A
    → Γ ⊢ e₁ · e₂ ∙ ⇛ ∙ B

  ty-app₂ : ∀ {Γ e₁ e₂ A B}
    → Γ ⊢ e₁ ∙ ⇚ ∙ A ⇒ B
    → Γ ⊢ e₂ ∙ ⇛ ∙ A
    → Γ ⊢ e₁ · e₂ ∙ ⇛ ∙ B

  ty-ann : ∀ {Γ e A}
    → Γ ⊢ e ∙ ⇚ ∙ A
    → Γ ⊢ e ⦂ A ∙ ⇛ ∙ A

  ty-sub : ∀ {Γ e A B}
    → Γ ⊢ e ∙ ⇛ ∙ B
    → B ≤ A
    → Γ ⊢ e ∙ ⇚ ∙ A

_ : (Int ⇒ Int) ≤ (Int ⇒ Top)
_ = ≤-arr ≤-int ≤-top

_ : ∅ ⊢ (ƛ "x" ⇒ ` "x") · lit 1 ∙ ⇛ ∙ Int
_ = ty-app₂ (ty-lam (ty-sub (ty-var Z) ≤-int)) ty-int

≤-refl : ∀ {A} → A ≤ A
≤-refl {Int} = ≤-int
≤-refl {Top} = ≤-top
≤-refl {A ⇒ B} = ≤-arr ≤-refl ≤-refl

_ : ∅ ⊢ ((ƛ "f" ⇒ ` "f" · (lit 1)) ⦂ (Int ⇒ Int) ⇒ Int) · (ƛ "x" ⇒ ` "x") ∙ ⇛ ∙ Int
_ = ty-app₁ (ty-ann (ty-lam (ty-sub (ty-app₁ (ty-var Z) (ty-sub ty-int ≤-int)) ≤-int))) (ty-lam (ty-sub (ty-var Z) ≤-int))
