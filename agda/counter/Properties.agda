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
    → Γ ⊢d ∘ ╏ e ∙ ⇚ ∙ A
    → Γ ⊩ (e ∷ es) ⇚ (A ∷ As)

⊩-elim : ∀ {Γ e H A es T As A'}
  → Γ ⊢d c 0 ╏ e ∙ ⇛ ∙ A
  → Γ ⊩ es ⇚ As
  → ❪ H , A ❫↣❪ es , T , As , A' ❫ 
  → Γ ⊢d c 0 ╏ e ▻ es ∙ ⇛ ∙ A'
⊩-elim ⊢d ⊩-empty none = ⊢d
⊩-elim ⊢d (⊩-cons ⊩es ⊢e) (have spl) = ⊩-elim (⊢d-app₁ ⊢d ⊢e) ⊩es spl
  

sound-≤ : ∀ {Γ H A es T As A'}
  → Γ ⊢a A ≤ H
  → ❪ H , A ❫↣❪ es , T , As , A' ❫
  → (A' ≤d T) × (Γ ⊩ es ⇚ As)

sound : ∀ {Γ e H A es T As A'}
  → Γ ⊢a H ⇛ e ⇛ A
  → ❪ H , A ❫↣❪ es , T , As , A' ❫
  → (T ≡ Top → Γ ⊢d c 0 ╏ e ▻ es ∙ ⇛ ∙ A') × (Γ ⊢d ∘ ╏ e ▻ es ∙ ⇚ ∙ T)

sound-≤ ≤a-int none = ⟨ ≤d-int , ⊩-empty ⟩
sound-≤ ≤a-top none = ⟨ ≤d-top , ⊩-empty ⟩
sound-≤ (≤a-arr ≤a ≤a₁) none = ⟨ ≤d-arr (proj₁ (sound-≤ ≤a none)) (proj₁ (sound-≤ ≤a₁ none)) , ⊩-empty ⟩
sound-≤ (≤a-hint ⊢e ≤a) (have spl) = ⟨ proj₁ (sound-≤ ≤a spl) , ⊩-cons (proj₂ (sound-≤ ≤a spl)) (proj₂ (sound ⊢e none)) ⟩

sound (⊢a-lit ≤a-int) none = ⟨ (λ T≡Top → ⊢d-int) , ⊢d-sub ⊢d-int ≤d-int ⟩
sound (⊢a-lit ≤a-top) none = ⟨ (λ T≡Top → ⊢d-int) , ⊢d-sub ⊢d-int ≤d-top ⟩

sound (⊢a-var Γ∋x A≤H) spl = ⟨ (λ T≡Top → ⊩-elim (⊢d-var Γ∋x) (proj₂ (sound-≤ A≤H spl)) spl)
                             , ⊢d-sub (⊩-elim (⊢d-var Γ∋x) (proj₂ (sound-≤ A≤H spl)) spl) (proj₁ (sound-≤ A≤H spl)) ⟩                             
                             
sound (⊢a-app ⊢a x) spl = sound ⊢a (have spl)

sound (⊢a-ann ⊢a A≤H) spl = ⟨ (λ T≡Top → ⊩-elim (⊢d-ann ( proj₂ (sound ⊢a none))) ( proj₂ (sound-≤ A≤H spl)) spl)
                            , ⊢d-sub (⊩-elim (⊢d-ann ( proj₂ (sound ⊢a none))) ( proj₂ (sound-≤ A≤H spl)) spl) ((proj₁ (sound-≤ A≤H spl))) ⟩
                            
sound (⊢a-lam₁ ⊢e) none = ⟨ (λ ()) , ⊢d-lam₁ (proj₂ (sound ⊢e none)) ⟩

sound (⊢a-lam₂ ⊢e ⊢e₁ B≤H) (have spl) = ⟨ (λ T≡Top → {!(proj₁ (sound ⊢e₁ spl)) T≡Top!}) , {!!} ⟩

{-

⟨ (λ T≡Top → ⊩-elim (⊢d-app₂ (⊢d-lam₂ {!sound ⊢e₁!}) ((proj₁ (sound ⊢e none)) refl)) (proj₂ (sound-≤ B≤H spl)) spl) , {!!} ⟩

-}

sound-inf : ∀ {Γ e A}
  → Γ ⊢a τ Top ⇛ e ⇛ A
  → Γ ⊢d c 0 ╏ e ∙ ⇛ ∙ A
sound-inf ⊢a = proj₁ (sound ⊢a none) refl

sound-chk : ∀ {Γ e A B}
  → Γ ⊢a τ A ⇛ e ⇛ B
  → Γ ⊢d ∘ ╏ e ∙ ⇚ ∙ A
sound-chk ⊢a = proj₂ (sound ⊢a none)

----------------------------------------------------------------------
--+                                                                +--
--+                          Completeness                          +--
--+                                                                +--
----------------------------------------------------------------------

-- subtyping complete

≤d-to-≤a : ∀ {Γ A B}
  → B ≤d A
  → Γ ⊢a B ≤ τ A
≤d-to-≤a ≤d-int = ≤a-int
≤d-to-≤a ≤d-top = ≤a-top
≤d-to-≤a (≤d-arr ≤d ≤d₁) = ≤a-arr (≤d-to-≤a ≤d) (≤d-to-≤a ≤d₁)

-- completeness theorem

complete : ∀ {Γ e ⇔ A cc}
  → Γ ⊢d cc ╏ e ∙ ⇔ ∙ A
  → ((⇔ ≡ ⇚) → ∃[ B ] (Γ ⊢a τ A ⇛ e ⇛ B)) × ((⇔ ≡ ⇛) → Γ ⊢a τ Top ⇛ e ⇛ A)
