module Properties where

open import Data.Nat using (ℕ)
open import Data.String using (String)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl)
open import Data.Product using (_×_; proj₁; proj₂; ∃; ∃-syntax) renaming (_,_ to ⟨_,_⟩)
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

sound-base : ∀ {Γ e A B}
  → Γ ⊢a τ B ⇛ e ⇛ A
  → Γ ⊢a A ≤ τ B
  → Γ ⊢d e ∙ ⇚ ∙ A
sound-base ⊢a ≤a-int = {!⊢a!}
sound-base ⊢a ≤a-top = {!!}
sound-base ⊢a (≤a-arr ≤a ≤a₁) = {!!}

sound : ∀ {Γ e H A es B A'}
  → Γ ⊢a H ⇛ e ⇛ A
  → split H A es B A'
  → Γ ⊢d e ▻ es ∙ ⇚ ∙ A'
sound (⊢a-lit x) spl = {!!}
sound (⊢a-var x x₁) spl = {!!}
sound (⊢a-app ⊢a x) spl = sound ⊢a {!!}
sound (⊢a-ann ⊢a x) spl = {!!}
sound (⊢a-lam₁ ⊢a ⊢a₁) spl = {!!}
sound (⊢a-lam₂ ⊢a) spl = {!!}

{-


sound : ∀ {Γ e H A es B A'}
  → Γ ⊢a H ⇛ e ⇛ A
  → split H A es B A'
  → Γ ⊢d e ▻ es ∙ ⇚ ∙ A'
sound ⊢a none = {!!}
sound ⊢a (have spl) with (⊢a-to-≤a ⊢a)
... | ≤a-hint x ≤ = sound (⊢a-app ⊢a ≤) spl

-}
{-
sound (⊢a-lit x) none = ⊢d-sub ⊢d-int ≤d-int
sound (⊢a-var x x₁) none = ⊢d-sub (⊢d-var x) ≤d-refl
sound ty-var@(⊢a-var x (≤a-hint x₁ x₂)) (have spl) = sound (⊢a-app ty-var x₂) spl -- not sure if there's a termination issue
sound (⊢a-app ⊢a x) spl = {!!}
sound (⊢a-ann ⊢a x) spl = {!!}
sound (⊢a-lam₁ ⊢a ⊢a₁) spl = {!!}
sound (⊢a-lam₂ ⊢a) spl = {!!}
-}

{-

sound : ∀ {Γ e A B}
  → Γ ⊢a τ A ⇛ e ⇛ B
  → Γ ⊢d e ∙ ⇚ ∙ A
sound (⊢a-lit x) = ⊢d-sub ⊢d-int {!!}
sound (⊢a-var x x₁) = ⊢d-sub (⊢d-var x) {!!}
sound (⊢a-app ⊢a ≤) = {!!}
sound (⊢a-ann ⊢a x) = ⊢d-sub (⊢d-ann (sound ⊢a)) {!!}
sound (⊢a-lam₂ ⊢a) = ⊢d-lam (sound ⊢a)

sound-inf : ∀ {Γ e A}
  → Γ ⊢a τ Top ⇛ e ⇛ A
  → Γ ⊢d e ∙ ⇛ ∙ A
sound-inf (⊢a-lit x) = ⊢d-int
sound-inf (⊢a-var x x₁) = ⊢d-var x
sound-inf (⊢a-app ⊢a ≤) = {!!}
sound-inf (⊢a-ann ⊢a x) = ⊢d-ann {!!} -- sound

-}
----------------------------------------------------------------------
--+                                                                +--
--+                          Completeness                          +--
--+                                                                +--
----------------------------------------------------------------------

