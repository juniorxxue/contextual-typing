module STLC.Algo where

open import STLC.Prelude
open import STLC.Common

infixr 8 [_]↝_

data Context : Set where
  □ : Context -- empty context
  τ_ : Type → Context -- full type context
  [_]↝_ : Term → Context → Context -- application term context

-- a context is non-empty
data ¬□ : Context → Set where
  ¬□-τ : ∀ {A} → ¬□ (τ A)
  ¬□-term : ∀ {e Σ} → ¬□ ([ e ]↝ Σ)

-- term shift onto context
infixl 7 _⇧_
_⇧_ : Context → ℕ → Context
τ A ⇧ n = τ A
□ ⇧ n = □
([ e ]↝ Σ) ⇧ n = [ e ↑ n ]↝ (Σ ⇧ n)

-- term unshift onto context
infixl 7 _⇩_
_⇩_ : Context → ℕ → Context
τ A ⇩ n = τ A
□ ⇩ n = □
([ e ]↝ Σ) ⇩ n = [ e ↓ n ]↝ (Σ ⇩ n)

-- generic application consumer
data GenericConsumer : Term → Set where
  gc-lit : ∀ {i} → GenericConsumer (lit i)
  gc-var : ∀ {x} → GenericConsumer (` x)
  gc-ann : ∀ {e A} → GenericConsumer (e ⦂ A)

-- matching
infix 4 _⊢_≈_
-- typing
infix 4 _⊢_⇒_⇒_
-- two judgments are mutually dependent
data _⊢_≈_ : Env → Type → Context → Set
data _⊢_⇒_⇒_ : Env → Context → Term → Type → Set

data _⊢_≈_ where

  ≈□ : ∀ {Γ A}
    → Γ ⊢ A ≈ □

  ≈τ : ∀ {Γ A}
    → Γ ⊢ A ≈ τ A

  ≈term : ∀ {Γ Σ e A B C}
    → Γ ⊢ τ A ⇒ e ⇒ C
    → Γ ⊢ B ≈ Σ
    → Γ ⊢ (A `→ B) ≈ [ e ]↝ Σ

data _⊢_⇒_⇒_ where

  ⊢lit : ∀ {Γ n}
    → Γ ⊢ □ ⇒ lit n ⇒ Int

  ⊢var : ∀ {Γ A x}
    → Γ ∋ x ⦂ A
    → Γ ⊢ □ ⇒ ` x ⇒ A

  ⊢ann : ∀ {Γ e A B}
    → Γ ⊢ τ A ⇒ e ⇒ B
    → Γ ⊢ □ ⇒ e ⦂ A ⇒ A
    
  ⊢app : ∀ {Γ e₁ e₂ Σ A B}
    → Γ ⊢ [ e₂ ]↝ Σ ⇒ e₁ ⇒ A `→ B
    → Γ ⊢ Σ ⇒ e₁ · e₂ ⇒ B

  ⊢lam₁ : ∀ {Γ e A B C}
    → Γ , A ⊢ τ B ⇒ e ⇒ C
    → Γ ⊢ τ (A `→ B) ⇒ ƛ e ⇒ A `→ C

  ⊢lam₂ : ∀ {Γ e₁ e A B Σ}
    → Γ ⊢ □ ⇒ e₁ ⇒ A
    → Γ , A ⊢ (Σ ⇧ 0) ⇒ e ⇒ B
    → Γ ⊢ [ e₁ ]↝ Σ ⇒ ƛ e ⇒ A `→ B

  ⊢sub : ∀ {Γ e A Σ}
    → Γ ⊢ □ ⇒ e ⇒ A
    → Γ ⊢ A ≈ Σ
    → GenericConsumer e
    → ¬□ Σ
    → Γ ⊢ Σ ⇒ e ⇒ A

----------------------------------------------------------------------
--+                           Splitting                            +--
----------------------------------------------------------------------

{-
a splitting judgment for soundness, and some other properties
⟦ Σ , A ⟧→⟦ e̅ , Σ' , A̅ , A' ⟧
Σ and A are parallely splitted,
Σ is splitted into (e̅ , Σ')
A is splitted into (A̅ , A' ⟧
thus there's an informal invariant, Σ ≡ e̅ ↝ Σ', A ≡ A̅ → A' where Σ' is empty or a full type
-}

infix 4 ⟦_,_⟧→⟦_,_,_,_⟧
data ⟦_,_⟧→⟦_,_,_,_⟧ : Context → Type → List Term → Context → List Type → Type → Set where

  none-□ : ∀ {A}
    → ⟦ □ , A ⟧→⟦ [] , □ , [] , A ⟧

  none-τ : ∀ {A B}
    → ⟦ τ A , B ⟧→⟦ [] , τ A , [] , B ⟧

  have : ∀ {e Σ A B e̅ Σ' A' A̅}
    → ⟦ Σ , B ⟧→⟦ e̅ , Σ' , A̅ , A' ⟧
    → ⟦ [ e ]↝ Σ , A `→ B ⟧→⟦ e ∷ e̅ , Σ' , A ∷ A̅ , A' ⟧
