module Properties where

open import Data.Nat using (ℕ)
open import Data.String using (String)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl)
open import Data.Product using (_×_; proj₁; proj₂; ∃; ∃-syntax) renaming (_,_ to ⟨_,_⟩)
open import Data.Empty using (⊥; ⊥-elim)
open import Relation.Nullary using (¬_)

open import Common
open import Dec
open import Algo

----------------------------------------------------------------------
--+                                                                +--
--+                           Soundness                            +--
--+                                                                +--
----------------------------------------------------------------------

sound : ∀ {Γ e A}
  → Γ ⊢a τ A ⇛ e ⇛ A
  → Γ ⊢d e ∙ ⇚ ∙ A
sound (⊢a-lit x) = ⊢d-sub ⊢d-int ≤d-int
sound (⊢a-var x x₁) = ⊢d-sub (⊢d-var x) ≤d-refl
sound (⊢a-app ⊢a) = {!!}
sound (⊢a-ann ⊢a x) = ⊢d-sub (⊢d-ann (sound ⊢a)) ≤d-refl
sound (⊢a-lam₂ ⊢a) = ⊢d-lam (sound ⊢a)

sound-inf : ∀ {Γ e A}
  → Γ ⊢a τ Top ⇛ e ⇛ A
  → Γ ⊢d e ∙ ⇛ ∙ A
sound-inf (⊢a-lit x) = ⊢d-int
sound-inf (⊢a-var x x₁) = ⊢d-var x
sound-inf (⊢a-app ⊢a) = {!!}
sound-inf (⊢a-ann ⊢a x) = ⊢d-ann {!!}

----------------------------------------------------------------------
--+                                                                +--
--+                          Completeness                          +--
--+                                                                +--
----------------------------------------------------------------------

f : Mode → Type → Type
f ⇛ A = Top
f ⇚ A = A

-- looks like we fail the completeness

-- 1 <= Top
-- Top => 1 => Top

-- ex <= Top
-- Top => e => Top

-- A => e => A

complete : ∀ {Γ e A ⇔}
  → Γ ⊢d e ∙ ⇔ ∙ A
  → ∃[ B ] (Γ ⊢a τ (f ⇔ A) ⇛ e ⇛ B × Γ ⊢a B ≤ τ A)
complete ⊢d-int = ⟨ Int , ⟨ (⊢a-lit ≤a-top) , ≤a-int ⟩ ⟩
complete {A = A} (⊢d-var x) = ⟨ A , ⟨ (⊢a-var x ≤a-top) , ≤a-refl-h ⟩ ⟩
complete (⊢d-lam ⊢d) = {!!}
complete (⊢d-app₁ ⊢d ⊢d₁) = {!!}
complete (⊢d-app₂ ⊢d ⊢d₁) = {!!}
complete (⊢d-ann ⊢d) = {!!}
complete (⊢d-sub ⊢d x) = {!!}

