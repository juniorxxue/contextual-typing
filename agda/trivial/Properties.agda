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

sound (⊢a-lit ≤a-int) none = ⟨ (λ ()) , ⊢d-sub ⊢d-int ≤d-refl ⟩
sound (⊢a-lit ≤a-top) none = ⟨ (λ _ → ⊢d-int) , ⊢d-sub ⊢d-int ≤d-top ⟩
sound (⊢a-var Γ∋x A≤H) spl = ⟨ (λ T≡Top → ⊩-elim (⊢d-var Γ∋x) (proj₂ (sound-≤ A≤H spl)) spl)
                             , ⊢d-sub (⊩-elim (⊢d-var Γ∋x) (proj₂ (sound-≤ A≤H spl)) spl) (proj₁ (sound-≤ A≤H spl)) ⟩
sound (⊢a-app ⊢a x) spl = sound ⊢a (have spl)
sound (⊢a-ann ⊢a A≤H) spl = ⟨ (λ T≡Top → ⊩-elim (⊢d-ann ( proj₂ (sound ⊢a none))) ( proj₂ (sound-≤ A≤H spl)) spl)
                            , ⊢d-sub (⊩-elim (⊢d-ann ( proj₂ (sound ⊢a none))) ( proj₂ (sound-≤ A≤H spl)) spl) ((proj₁ (sound-≤ A≤H spl))) ⟩
sound (⊢a-lam₁ ⊢a) none = ⟨ (λ ()) , ⊢d-lam (proj₂ (sound ⊢a none)) ⟩
sound (⊢a-lam₂ ⊢e ⊢f) spl = {!!}

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

infix 4 _⊩a_⇛_⇛_

-- note that we use Type instead of Hint here
data _⊩a_⇛_⇛_ : Context → List Type → List Term → List Type → Set where

  ⊩a-empty : ∀ {Γ}
    → Γ ⊩a [] ⇛ [] ⇛ []

  ⊩a-cons : ∀ {Γ es As Bs e A B}
    → Γ ⊩a As ⇛ es ⇛ Bs
    → Γ ⊢a τ A ⇛ e ⇛ B
    → Γ ⊩a (A ∷ As) ⇛ (e ∷ es) ⇛ (B ∷ Bs)

infix 6 _↦_

_↦_ : List Type → Type → Type
[] ↦ A = A
(A ∷ As) ↦ B = A ⇒ (As ↦ B)

algon : ∀ {Γ e es As B Cs}
  → Γ ⊢a τ Top ⇛ e ⇛ As ↦ B
  → Γ ⊩a As ⇛ es ⇛ Cs
  → Γ ⊢a τ Top ⇛ e ▻ es ⇛ B
algon = {!!}

algo1 : ∀ {Γ e₁ e₂ A B C}
  → Γ ⊢a τ Top ⇛ e₁ ⇛ A ⇒ B
  → Γ ⊢a τ A ⇛ e₂ ⇛ C
  → Γ ⊢a τ Top ⇛ e₁ · e₂ ⇛ B
algo1 ⊢f ⊢e = algon ⊢f (⊩a-cons ⊩a-empty ⊢e)

{-

subsumption : ∀ {Γ H e A H'}
  → Γ ⊢a H ⇛ e ⇛ A
  → Γ ⊢a A ≤ H'
  → ∃[ B ] Γ ⊢a H' ⇛ e ⇛ B
subsumption (⊢a-lit x) A≤H' = ⟨ Int , ⊢a-lit A≤H' ⟩
subsumption {A = A} (⊢a-var x x₁) A≤H' = ⟨ A , ⊢a-var x A≤H' ⟩
subsumption {Γ = Γ} {H = H'} (⊢a-app {e₂ = e₂} {A = A} {B = B} ⊢e B≤H) B≤H' = {!!} -- solved
  where sub-ins : Γ ⊢a A ⇒ B ≤ ⟦ e₂ ⟧⇒ H'
        sub-ins = {!!}
subsumption {A = A} (⊢a-ann ⊢e x) A≤H' = ⟨ A , ⊢a-ann ⊢e A≤H' ⟩
subsumption (⊢a-lam ⊢e) A≤H' = {!subsumption ⊢e!}

problems with lam case, seems not provable

-}


complete : ∀ {Γ e ⇔ A}
  → Γ ⊢d e ∙ ⇔ ∙ A
  → ((⇔ ≡ ⇚) → ∃[ B ] (Γ ⊢a τ A ⇛ e ⇛ B)) × ((⇔ ≡ ⇛) → Γ ⊢a τ Top ⇛ e ⇛ A)
complete ⊢d-int = ⟨ (λ ()) , (λ _ → ⊢a-lit ≤a-top) ⟩
complete (⊢d-var x) = ⟨ (λ ()) , (λ _ → ⊢a-var x ≤a-top) ⟩

complete (⊢d-lam {A = A} {B = B} ⊢d) with (proj₁ (complete ⊢d)) refl
... | ⟨ C , ⊢a-e ⟩ = ⟨ (λ _ → ⟨ A ⇒ C , ⊢a-lam₁ ⊢a-e ⟩) , (λ ()) ⟩

complete (⊢d-app₁ ⊢f ⊢e) with proj₁ (complete ⊢e) refl
... | ⟨ C , ⊢a-e ⟩ = ⟨ (λ ()) , (λ _ → algo1 ind-f ⊢a-e) ⟩
  where ind-f = proj₂ (complete ⊢f) refl

complete (⊢d-app₂ ⊢e₁ ⊢e₂) = ⟨ (λ _ → ⟨ {!!} , {!!} ⟩) , (λ ()) ⟩

complete (⊢d-ann ⊢d) with (proj₁ (complete ⊢d)) refl
... | ⟨ B , ⊢a-e ⟩ = ⟨ (λ ()) , (λ _ → ⊢a-ann ⊢a-e ≤a-top) ⟩

complete (⊢d-sub ⊢d B≤A) = ⟨ (λ _ → {!!}) , (λ ()) ⟩
