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

-- induction on spl is a wrong start

sound-aux : ∀ {Γ B e A}
  → Γ ⊢a τ B ⇛ e ⇛ A
  → Γ ⊢d e ∙ ⇚ ∙ A
sound-aux (⊢a-lit x) = ⊢d-sub ⊢d-int ≤d-int
sound-aux (⊢a-var x x₁) = ⊢d-sub (⊢d-var x) ≤d-refl
sound-aux (⊢a-app ⊢a x) = ⊢d-sub {!!} {!!}
sound-aux (⊢a-ann ⊢a x) = {!!}
sound-aux (⊢a-lam₂ ⊢a) = {!!}

sound : ∀ {Γ e H A es B A'}
  → Γ ⊢a H ⇛ e ⇛ A
  → split H A es B A'
  → Γ ⊢d e ▻ es ∙ ⇚ ∙ A'
sound (⊢a-lit x) none = ⊢d-sub ⊢d-int ≤d-int
sound (⊢a-var x x₁) none = ⊢d-sub (⊢d-var x) ≤d-refl
sound (⊢a-var x (≤a-hint x₁ x₂)) (have spl) = sound (⊢a-app (⊢a-var x ((≤a-hint x₁ x₂))) x₂) spl
sound (⊢a-app ⊢a x) spl = {!spl!}
sound (⊢a-ann ⊢a x) spl = {!!}
sound (⊢a-lam₁ ⊢a ⊢a₁) spl = {!!}
sound (⊢a-lam₂ ⊢a) spl = {!!}

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

