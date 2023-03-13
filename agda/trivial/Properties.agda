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
⊩-elim ⊢d (⊩-cons ⊩es ⊢e) (have spl) = ⊩-elim (⊢d-app ⊢d ⊢e) ⊩es spl

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
sound (⊢a-lam ⊢a) none = ⟨ (λ ()) , ⊢d-lam (proj₂ (sound ⊢a none)) ⟩

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

≤d-to-≤a : ∀ {Γ A B}
  → B ≤d A
  → Γ ⊢a B ≤ τ A
≤d-to-≤a ≤d-int = ≤a-int
≤d-to-≤a ≤d-top = ≤a-top
≤d-to-≤a (≤d-arr ≤d ≤d₁) = ≤a-arr (≤d-to-≤a ≤d) (≤d-to-≤a ≤d₁)

≤a-hint-inv₁ : ∀ {Γ H A B e}
  → Γ ⊢a A ⇒ B ≤ ⟦ e ⟧⇒ H
  → ∃[ C ] Γ ⊢a τ A ⇛ e ⇛ C
≤a-hint-inv₁ (≤a-hint {C = C} x ≤a) = ⟨ C , x ⟩

≤a-hint-inv₂ : ∀ {Γ H A B e}
  → Γ ⊢a A ⇒ B ≤ ⟦ e ⟧⇒ H
  → Γ ⊢a B ≤ H
≤a-hint-inv₂ (≤a-hint x ≤) = ≤

subsumption : ∀ {Γ H e A H' es As A'}
  → Γ ⊢a H ⇛ e ⇛ A
  → ❪ H , A ❫↣❪ es , Top , As , A' ❫
  → Γ ⊢a A ≤ H'
  → ∃[ B ] Γ ⊢a H' ⇛ e ⇛ B
subsumption (⊢a-lit x) spl A≤H' = ⟨ Int , ⊢a-lit A≤H' ⟩
subsumption {A = A} (⊢a-var x x₁) spl A≤H' = ⟨ A , ⊢a-var x A≤H' ⟩
subsumption (⊢a-app {A = A} ⊢e B≤H) spl B≤H' with subsumption ⊢e (have spl) (≤a-hint (proj₂ (≤a-hint-inv₁ (⊢a-to-≤a ⊢e))) B≤H')
... | ⟨ A ⇒ C , ⊢e₁ ⟩ = ⟨ C , (⊢a-app ⊢e₁ (≤a-hint-inv₂ (⊢a-to-≤a ⊢e₁))) ⟩
... | ⟨ Top , ⊢a-var x () ⟩
... | ⟨ Top , ⊢a-app ⊢e₁ () ⟩
... | ⟨ Top , ⊢a-ann ⊢e₁ () ⟩
... | ⟨ Int , ⊢a-lit () ⟩
... | ⟨ Int , ⊢a-var x () ⟩
... | ⟨ Int , ⊢a-app ⊢e₁ () ⟩
... | ⟨ Int , ⊢a-ann ⊢e₁ () ⟩
subsumption {A = A} (⊢a-ann ⊢e x) spl A≤H' = ⟨ A , ⊢a-ann ⊢e A≤H' ⟩

subsumption-strong : ∀ {Γ H e A H' es As A'}
  → Γ ⊢a H ⇛ e ⇛ A
  → ❪ H , A ❫↣❪ es , Top , As , A' ❫
  → Γ ⊢a A ≤ H'
  → Γ ⊢a H' ⇛ e ⇛ A
subsumption-strong (⊢a-lit x) spl A≤H' = ⊢a-lit A≤H'
subsumption-strong (⊢a-var x x₁) spl A≤H' = ⊢a-var x A≤H'
subsumption-strong (⊢a-app ⊢f x) spl A≤H' = ⊢a-app (subsumption-strong ⊢f (have spl) (≤a-hint (proj₂ (≤a-hint-inv₁ (⊢a-to-≤a ⊢f))) A≤H')) A≤H'
subsumption-strong (⊢a-ann ⊢f x) spl A≤H' = ⊢a-ann ⊢f A≤H'

sub-case : ∀ {Γ e A B}
  → Γ ⊢a τ Top ⇛ e ⇛ A
  → Γ ⊢a A ≤ τ B
  → ∃[ C ] Γ ⊢a τ B ⇛ e ⇛ C
sub-case ⊢a A≤B = subsumption ⊢a none A≤B

sub-args : ∀ {Γ e A H}
  → Γ ⊢a τ Top ⇛ e ⇛ A
  → Γ ⊢a A ≤ H
  → Γ ⊢a H ⇛ e ⇛ A
sub-args ⊢a A≤H = subsumption-strong ⊢a none A≤H

algo1'' : ∀ {Γ e₁ e₂ A B C}
  → Γ ⊢a τ Top ⇛ e₁ ⇛ A ⇒ B
  → Γ ⊢a τ A ⇛ e₂ ⇛ C
  → Γ ⊢a τ Top ⇛ e₁ · e₂ ⇛ B
algo1'' ⊢f ⊢e = ⊢a-app (sub-args ⊢f (≤a-hint ⊢e ≤a-top)) ≤a-top

complete : ∀ {Γ e ⇔ A}
  → Γ ⊢d e ∙ ⇔ ∙ A
  → ((⇔ ≡ ⇚) → ∃[ B ] (Γ ⊢a τ A ⇛ e ⇛ B)) × ((⇔ ≡ ⇛) → Γ ⊢a τ Top ⇛ e ⇛ A)
complete ⊢d-int = ⟨ (λ ()) , (λ _ → ⊢a-lit ≤a-top) ⟩
complete (⊢d-var x) = ⟨ (λ ()) , (λ _ → ⊢a-var x ≤a-top) ⟩

complete (⊢d-lam {A = A} {B = B} ⊢d) with (proj₁ (complete ⊢d)) refl
... | ⟨ C , ⊢a-e ⟩ = ⟨ (λ _ → ⟨ A ⇒ C , ⊢a-lam ⊢a-e ⟩) , (λ ()) ⟩

complete (⊢d-app ⊢f ⊢e) with proj₁ (complete ⊢e) refl
... | ⟨ C , ⊢a-e ⟩ = ⟨ (λ ()) , (λ _ → algo1'' ind-f ⊢a-e) ⟩
  where ind-f = proj₂ (complete ⊢f) refl

complete (⊢d-ann ⊢d) with (proj₁ (complete ⊢d)) refl
... | ⟨ B , ⊢a-e ⟩ = ⟨ (λ ()) , (λ _ → ⊢a-ann ⊢a-e ≤a-top) ⟩

complete (⊢d-sub ⊢d B≤A) = ⟨ (λ _ →  sub-case ((proj₂ (complete ⊢d)) refl) (≤d-to-≤a B≤A)) , (λ ()) ⟩
