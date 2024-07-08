module Elaboration.STLC.Target where

open import Elaboration.STLC.Common

infixr 5  ƛ_⇒_
infixl 7  _·_
infix  9  `_

data Term : Set where
  lit      : ℕ → Term
  `_       : Id → Term
  ƛ_⇒_     : Id → Term → Term
  _·_      : Term → Term → Term

infix  4  _⊢_⦂_

data _⊢_⦂_ : Context → Term → Type → Set where

  ⊢n : ∀ {Γ n}
    → Γ ⊢ (lit n) ⦂ Int
    
  ⊢` : ∀ {Γ x A}
    → Γ ∋ x ⦂ A
      -----------
    → Γ ⊢ ` x ⦂ A
    
  ⊢ƛ : ∀ {Γ x N A B}
    → Γ , x ⦂ A ⊢ N ⦂ B
      -------------------
    → Γ ⊢ ƛ x ⇒ N ⦂ A ⇒ B
    
  ⊢· : ∀ {Γ L M A B}
    → Γ ⊢ L ⦂ A ⇒ B
    → Γ ⊢ M ⦂ A
      -------------
    → Γ ⊢ L · M ⦂ B


