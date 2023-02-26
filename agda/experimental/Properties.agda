module Properties where

open import Data.Nat using (ℕ)
open import Data.String using (String)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl)
open import Data.Product using (_×_; proj₁; proj₂; ∃; ∃-syntax) renaming (_,_ to ⟨_,_⟩)
open import Data.Sum using (_⊎_; inj₁; inj₂) renaming ([_,_] to case-⊎)
open import Data.Empty using (⊥; ⊥-elim)
open import Relation.Nullary using (¬_)

open import Data.List using (List; []; _∷_; _++_; length; reverse; map; foldr; downFrom)

open import Common
open import Dec
open import Algo

----------------------------------------------------------------------
--+                                                                +--
--+                           Soundness                            +--
--+                                                                +--
----------------------------------------------------------------------

⊢d-fun-elim : ∀ {Γ e es A A'}
  → Γ ⊢d e ∙ ⇛ ∙ A
  → Γ ⊢d e ▻ es ∙ ⇛ ∙ A' -- A' is the output part of A
  -- but we need es to be well-typed,

sound : ∀ {Γ e H A es T As A'}
  → Γ ⊢a H ⇛ e ⇛ A
  → split H A es T As A'
  → (T ≡ Top → Γ ⊢d e ▻ es ∙ ⇛ ∙ A') × (Γ ⊢d e ▻ es ∙ ⇚ ∙ T)
sound (⊢a-lit ≤a-int) none = {!!}
sound (⊢a-lit ≤a-top) none = {!!}
sound (⊢a-var x x₁) spl = {!!}
sound (⊢a-app ⊢a x) spl = sound ⊢a (have spl)
sound (⊢a-ann ⊢a x) spl = {!!}
sound (⊢a-lam₁ ⊢a ⊢a₁) spl = {!!}
sound (⊢a-lam₂ ⊢a) none = ⟨ (λ ()) , ⊢d-lam (proj₂ (sound ⊢a none)) ⟩

-- Corollary

sound-inf : ∀ {Γ e A}
  → Γ ⊢a τ Top ⇛ e ⇛ A
  → Γ ⊢d e ∙ ⇛ ∙ A
sound-inf ⊢a = proj₁ (sound ⊢a none) refl

sound-chk : ∀ {Γ e A B}
  → Γ ⊢a τ A ⇛ e ⇛ B
  → Γ ⊢d e ∙ ⇚ ∙ A
sound-chk ⊢a = proj₂ (sound ⊢a none)

----------------------------------------------------------------------
--+                                                                +--
--+                          Completeness                          +--
--+                                                                +--
----------------------------------------------------------------------
