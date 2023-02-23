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

⊢d-fun-elim : ∀ {Γ e es A A'}
  → Γ ⊢d e ∙ ⇛ ∙ A
  → Γ ⊢d e ▻ es ∙ ⇛ ∙ A' -- A' is the output part of A
  -- but we need es to be well-typed,


ff : Type → Mode
ff Top = ⇛
ff _ = ⇚

sound-inf : ∀ {Γ e H A es T A'}
  → Γ ⊢a H ⇛ e ⇛ A
  → split H A es T A'
  → Γ ⊢d e ▻ es ∙ ff T ∙ A'
sound-inf (⊢a-lit ≤a-int) none = ⊢d-sub ⊢d-int ≤d-int
sound-inf (⊢a-lit ≤a-top) none = ⊢d-int
sound-inf (⊢a-var x x₁) spl = {!!}
sound-inf (⊢a-app ⊢a x) spl = sound-inf ⊢a (have spl)
sound-inf (⊢a-ann ⊢a x) spl = {!!}
sound-inf (⊢a-lam₁ ⊢e ⊢f) (have spl) = {!sound-inf ⊢e ?!}
sound-inf (⊢a-lam₂ {B = Int} ⊢a) none = ⊢d-lam (sound-inf ⊢a none)
sound-inf (⊢a-lam₂ {B = Top} ⊢a) none = ⊢d-lam (⊢d-sub (sound-inf ⊢a none) ≤d-refl)
sound-inf (⊢a-lam₂ {B = B ⇒ B₁} ⊢a) none = ⊢d-lam (sound-inf ⊢a none)

g : Type → Type → Mode × Type
g Top A = ⟨ ⇛ , A ⟩
g T _ = ⟨ ⇚ , T ⟩


sound-i : ∀ {Γ e H A es T A'}
  → Γ ⊢a H ⇛ e ⇛ A
  → split H A es T A'
  → Γ ⊢d e ▻ es ∙ proj₁ (g T A') ∙ proj₂ (g T A')
sound-i (⊢a-lit ≤a-int) none = ⊢d-sub ⊢d-int ≤d-int
sound-i (⊢a-lit ≤a-top) none = ⊢d-int
sound-i (⊢a-var x x₁) spl = {!!}
sound-i (⊢a-app ⊢e x) spl = sound-i ⊢e (have spl)
sound-i (⊢a-ann ⊢e x) spl = {!!}
sound-i (⊢a-lam₁ ⊢e ⊢e₁) (have spl) = {!sound-i ⊢e₁ spl!}
sound-i (⊢a-lam₂ {B = Int} ⊢e) none = ⊢d-lam (sound-i ⊢e none)
sound-i (⊢a-lam₂ {B = Top} ⊢e) none = ⊢d-lam (⊢d-sub (sound-i ⊢e none) ≤d-top)
sound-i (⊢a-lam₂ {B = B ⇒ B₁} ⊢e) none = ⊢d-lam (sound-i ⊢e none)


sound : ∀ {Γ e H A es T A'}
  → Γ ⊢a H ⇛ e ⇛ A
  → split H A es T A'
  → Γ ⊢d e ▻ es ∙ ⇚ ∙ A'
sound (⊢a-lit x) none = ⊢d-sub ⊢d-int ≤d-int
sound (⊢a-var ∋ ≤) spl = {!⊢d-var!}
sound (⊢a-app ⊢a x) spl = sound ⊢a (have spl)
sound (⊢a-ann ⊢a x) spl = {!sound ⊢a !}
sound (⊢a-lam₁ ⊢f ⊢e) (have spl) = {!sound ⊢e spl!}
sound (⊢a-lam₂ ⊢a) none = ⊢d-lam (sound ⊢a none)

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

