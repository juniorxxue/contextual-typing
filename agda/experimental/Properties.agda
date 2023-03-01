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

try : ∀ {Γ e₁ e₂ es x A}
  → Γ ⊢d (ƛ x ⇒ (e₁ ▻ es)) · e₂ ∙ ⇛ ∙ A
  → Γ ⊢d ((ƛ x ⇒ e₁) · e₂) ▻ es ∙ ⇛ ∙ A
try {es = []} ⊢ = {!!}
try {es = x ∷ es} ⊢ = {!!}

subst : ∀ {Γ e es A B ⇔ x e'}
  → Γ , x ⦂ A ⊢d e ▻ es ∙ ⇔ ∙ B
  → Γ ⊢d e' ∙ ⇛ ∙ A
  → Γ ⊢d ((ƛ x ⇒ e) · e') ▻ es ∙ ⇔ ∙ B
subst {e = e} {[]} {⇔ = ⇛} ⊢b ⊢a = ⊢d-app₂ (⊢d-lam (⊢d-sub ⊢b ≤d-refl)) ⊢a
subst {e = e} {[]} {⇔ = ⇚} ⊢b ⊢a = ⊢d-sub (⊢d-app₂ (⊢d-lam ⊢b) ⊢a) ≤d-refl
subst {e = e} {x ∷ es} ⊢b ⊢a = {!subst {es = es} ⊢b ⊢a!}


infix 4 _⊩_⇚_
data _⊩_⇚_ : Context → List Term → List Type → Set where
  ⊩-empty : ∀ {Γ}
    → Γ ⊩ [] ⇚ []

  ⊩-cons : ∀ {Γ es As e A}
    → Γ ⊩ es ⇚ As
    → Γ ⊢d e ∙ ⇚ ∙ A
    → Γ ⊩ (e ∷ es) ⇚ (A ∷ As)

⊩-elim : ∀ {Γ e H A es T As A'}
  → Γ ⊢d e ∙ ⇛ ∙ A
  → Γ ⊩ es ⇚ As
  → ❪ H , A ❫↣❪ es , T , As , A' ❫
  → Γ ⊢d e ▻ es ∙ ⇛ ∙ A'
⊩-elim ⊢d ⊩-empty none = ⊢d
⊩-elim ⊢d (⊩-cons ⊩es ⊢e) (have spl) = ⊩-elim (⊢d-app₁ ⊢d ⊢e) ⊩es spl

sound-≤ : ∀ {Γ H A es T As A'}
  → Γ ⊢a A ≤ H
  → ❪ H , A ❫↣❪ es , T , As , A' ❫
  → (A' ≤d T) × (Γ ⊩ es ⇚ As)

sound : ∀ {Γ e H A es T As A'}
  → Γ ⊢a H ⇛ e ⇛ A
  → ❪ H , A ❫↣❪ es , T , As , A' ❫
  → (T ≡ Top → Γ ⊢d e ▻ es ∙ ⇛ ∙ A') × (Γ ⊢d e ▻ es ∙ ⇚ ∙ T)

sound-≤ ≤a-int none = ⟨ ≤d-int , ⊩-empty ⟩
sound-≤ ≤a-top none = ⟨ ≤d-top , ⊩-empty ⟩
sound-≤ (≤a-arr ≤a ≤a₁) none = ⟨ ≤d-arr (proj₁ (sound-≤ ≤a none)) (proj₁ (sound-≤ ≤a₁ none)) , ⊩-empty ⟩
sound-≤ (≤a-hint ⊢e ≤a) (have spl) = ⟨ proj₁ (sound-≤ ≤a spl) , ⊩-cons (proj₂ (sound-≤ ≤a spl)) (proj₂ (sound ⊢e none)) ⟩

sound (⊢a-lit ≤a-int) none = {!!}
sound (⊢a-lit ≤a-top) none = {!!}
sound (⊢a-var Γ∋x A≤H) spl = ⟨ (λ T≡Top → ⊩-elim (⊢d-var Γ∋x) (proj₂ (sound-≤ A≤H spl)) spl) ,
                               {!!} ⟩
sound (⊢a-app ⊢a x) spl = sound ⊢a (have spl)
sound (⊢a-ann ⊢a x) spl = {!!}
sound (⊢a-lam₁ ⊢e ⊢f) (have {es = es} spl) = ⟨ (λ T≡Top → subst {es = es} ((proj₁ (sound ⊢f spl)) T≡Top) (proj₁ (sound ⊢e none) refl))
                                               , subst {es = es} (proj₂ (sound ⊢f spl)) (proj₁ (sound ⊢e none) refl) ⟩
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

-- if it infers a minimal type A, our algo. can infer it
-- 

complete : ∀ {Γ e ⇔ A}
  → Γ ⊢d e ∙ ⇔ ∙ A
  → ((⇔ ≡ ⇚) → ∃[ B ] (Γ ⊢a τ A ⇛ e ⇛ B)) × ((⇔ ≡ ⇛) → (∀ {C} → Γ ⊢d e ∙ ⇔ ∙ C → A ≤d C) → Γ ⊢a τ Top ⇛ e ⇛ A)
complete ⊢d-int = ⟨ (λ ()) , {!!} ⟩
complete (⊢d-var x) = ⟨ (λ x₂ → {!!}) , {!!} ⟩
complete (⊢d-lam ⊢d) = {!!}
complete (⊢d-app₁ ⊢d ⊢d₁) = {!!}
complete (⊢d-app₂ ⊢d ⊢d₁) = ⟨ (λ ()) , {!!} ⟩
complete (⊢d-ann ⊢d) = {!!}
complete (⊢d-sub ⊢d x) = {!!}
