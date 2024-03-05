module STLC.Algo where

open import STLC.Prelude
open import STLC.Common

infixr 8 ⟦_⟧⇒_

data Hint : Set where
  □ : Hint
  τ : Type → Hint
  ⟦_⟧⇒_ : Term → Hint → Hint

infixl 7 _⇧_
_⇧_ : Hint → ℕ → Hint
τ A ⇧ n = τ A
□ ⇧ n = □
(⟦ e ⟧⇒ H) ⇧ n = ⟦ e ↑ n ⟧⇒ (H ⇧ n)

infixl 7 _⇩_
_⇩_ : Hint → ℕ → Hint
τ A ⇩ n = τ A
□ ⇩ n = □
(⟦ e ⟧⇒ H) ⇩ n = ⟦ e ↓ n ⟧⇒ (H ⇩ n)

data pv : Term → Set where

  pv-lit : ∀ {i}
    → pv (lit i)

  pv-var : ∀ {x}
    → pv (` x)

  pv-ann : ∀ {e A}
    → pv (e ⦂ A)
  
  
infix 4 _⊢a_≈_
infix 4 _⊢a_⇛_⇛_ 
 
data _⊢a_≈_ : Context → Type → Hint → Set
data _⊢a_⇛_⇛_ : Context → Hint → Term → Type → Set

data _⊢a_≈_ where

  ≈□ : ∀ {Γ A}
    → Γ ⊢a A ≈ □

  ≈τ : ∀ {Γ A}
    → Γ ⊢a A ≈ τ A

  ≈hole : ∀ {Γ H e A B C}
    → Γ ⊢a τ A ⇛ e ⇛ C
    → Γ ⊢a B ≈ H
    → Γ ⊢a (A ⇒ B) ≈ ⟦ e ⟧⇒ H

data _⊢a_⇛_⇛_ where

  ⊢a-lit : ∀ {Γ n}
    → Γ ⊢a □ ⇛ lit n ⇛ Int

  ⊢a-var : ∀ {Γ A x}
    → (x∈Γ : Γ ∋ x ⦂ A)
    → Γ ⊢a □ ⇛ ` x ⇛ A

  ⊢a-ann : ∀ {Γ e A B}
    → Γ ⊢a τ A ⇛ e ⇛ B
    → Γ ⊢a □ ⇛ e ⦂ A ⇛ A
    
  ⊢a-app : ∀ {Γ e₁ e₂ H A B}
    → Γ ⊢a ⟦ e₂ ⟧⇒ H ⇛ e₁ ⇛ A ⇒ B
    → Γ ⊢a H ⇛ e₁ · e₂ ⇛ B

  ⊢a-lam₁ : ∀ {Γ e A B C}
    → Γ , A ⊢a τ B ⇛ e ⇛ C
    → Γ ⊢a τ (A ⇒ B) ⇛ ƛ e ⇛ A ⇒ C

  ⊢a-lam₂ : ∀ {Γ e₁ e A B H}
    → Γ ⊢a □ ⇛ e₁ ⇛ A
    → Γ , A ⊢a (H ⇧ 0) ⇛ e ⇛ B
    → Γ ⊢a ⟦ e₁ ⟧⇒ H ⇛ ƛ e ⇛ A ⇒ B

  ⊢a-sub : ∀ {Γ e A H}
    → Γ ⊢a □ ⇛ e ⇛ A
    → (A≈H : Γ ⊢a A ≈ H)
    → (H≢□ : H ≢ □)
    → (pv-e : pv e)
    → Γ ⊢a H ⇛ e ⇛ A

----------------------------------------------------------------------
--+                                                                +--
--+                           Transform                            +--
--+                                                                +--
----------------------------------------------------------------------

_▻_ : Term → List Term → Term
e ▻ [] = e
e₁ ▻ (e₂ ∷ es) = (e₁ · e₂) ▻ es

infix 4 ❪_,_❫↣❪_,_,_,_❫

data ❪_,_❫↣❪_,_,_,_❫ : Hint → Type → List Term → Hint → List Type → Type → Set where

  none-□ : ∀ {A}
    → ❪ □ , A ❫↣❪ [] , □ , [] , A ❫

  none-τ : ∀ {A B}
    → ❪ τ A , B ❫↣❪ [] , τ A , [] , B ❫

  have : ∀ {e H A B es A' B' Bs}
    → ❪ H , B ❫↣❪ es , A' , Bs , B' ❫
    → ❪ ⟦ e ⟧⇒ H , A ⇒ B ❫↣❪ e ∷ es , A' , A ∷ Bs , B' ❫
