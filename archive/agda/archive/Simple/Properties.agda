module Simple.Properties where

open import Data.Nat using (ℕ)
open import Data.String using (String)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl)
open import Data.Product using (_×_; proj₁; proj₂; ∃; ∃-syntax) renaming (_,_ to ⟨_,_⟩)
open import Data.Sum using (_⊎_; inj₁; inj₂) renaming ([_,_] to case-⊎)
open import Data.Empty using (⊥; ⊥-elim)
open import Relation.Nullary using (¬_)

open import Data.List using (List; []; _∷_; _++_; length; reverse; map; foldr; downFrom)

open import Simple.Common
open import Simple.Decl
open import Simple.Algo

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
sound (⊢a-app ⊢a) spl = sound ⊢a (have spl)
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

-- subtyping complete

≤d-to-≤a : ∀ {Γ A B}
  → B ≤d A
  → Γ ⊢a B ≤ τ A
≤d-to-≤a ≤d-int = ≤a-int
≤d-to-≤a ≤d-top = ≤a-top
≤d-to-≤a (≤d-arr ≤d ≤d₁) = ≤a-arr (≤d-to-≤a ≤d) (≤d-to-≤a ≤d₁)

-- subsumption lemma ans its following corollaries
subsumption : ∀ {Γ H e A H' es As A'}
  → Γ ⊢a H ⇛ e ⇛ A
  → ❪ H , A ❫↣❪ es , Top , As , A' ❫
  → Γ ⊢a A ≤ H'
  → Γ ⊢a H' ⇛ e ⇛ A
subsumption (⊢a-lit x) spl A≤H' = ⊢a-lit A≤H'
subsumption (⊢a-var x x₁) spl A≤H' = ⊢a-var x A≤H'
subsumption (⊢a-app ⊢f) spl A≤H' = ⊢a-app (subsumption ⊢f (have spl) (≤a-hint (proj₂ (≤a-hint-inv₁ (⊢a-to-≤a ⊢f))) A≤H'))
subsumption (⊢a-ann ⊢f x) spl A≤H' = ⊢a-ann ⊢f A≤H'

sub-args : ∀ {Γ e A H}
  → Γ ⊢a τ Top ⇛ e ⇛ A
  → Γ ⊢a A ≤ H
  → Γ ⊢a H ⇛ e ⇛ A
sub-args ⊢a A≤H = subsumption ⊢a none A≤H

-- completeness theorem

complete-inf : ∀ {Γ e A}
  → Γ ⊢d e ∙ ⇛ ∙ A
  → Γ ⊢a τ Top ⇛ e ⇛ A

complete-chk : ∀ {Γ e A}
  → Γ ⊢d e ∙ ⇚ ∙ A
  → ∃[ B ] (Γ ⊢a τ A ⇛ e ⇛ B)

complete-inf ⊢d-int = ⊢a-lit ≤a-top
complete-inf (⊢d-var x) = ⊢a-var x ≤a-top
complete-inf (⊢d-app ⊢f ⊢e) with complete-chk ⊢e
... |  ⟨ C , ⊢a-e ⟩ =  complete-app (complete-inf ⊢f) ⊢a-e
  where
    complete-app : ∀ {Γ e₁ e₂ A B C}
      → Γ ⊢a τ Top ⇛ e₁ ⇛ A ⇒ B
      → Γ ⊢a τ A ⇛ e₂ ⇛ C
      → Γ ⊢a τ Top ⇛ e₁ · e₂ ⇛ B
    complete-app ⊢f ⊢e = ⊢a-app (sub-args ⊢f (≤a-hint ⊢e ≤a-top))    

complete-inf (⊢d-ann ⊢d) with complete-chk ⊢d
... | ⟨ B , ⊢a-e ⟩ = ⊢a-ann ⊢a-e ≤a-top

complete-chk (⊢d-lam {A = A} ⊢d) with complete-chk ⊢d
... | ⟨ C , ⊢a-e ⟩ = ⟨ A ⇒ C , ⊢a-lam ⊢a-e ⟩

complete-chk (⊢d-sub ⊢d B≤A) = complete-sub (complete-inf ⊢d) (≤d-to-≤a B≤A)
  where
    complete-sub : ∀ {Γ e A B}
      → Γ ⊢a τ Top ⇛ e ⇛ A
      → Γ ⊢a A ≤ τ B
      → ∃[ C ] Γ ⊢a τ B ⇛ e ⇛ C
    complete-sub {A = A} ⊢a A≤B with subsumption ⊢a none A≤B
    ... | ⊢e = ⟨ A , ⊢e ⟩

complete : ∀ {Γ e ⇔ A}
  → Γ ⊢d e ∙ ⇔ ∙ A
  → ((⇔ ≡ ⇚) → ∃[ B ] (Γ ⊢a τ A ⇛ e ⇛ B)) × ((⇔ ≡ ⇛) → Γ ⊢a τ Top ⇛ e ⇛ A)
complete {⇔ = ⇛} ⊢d = ⟨ (λ ()) , (λ _ → complete-inf ⊢d) ⟩
complete {⇔ = ⇚} ⊢d = ⟨ (λ _ → complete-chk ⊢d) , (λ ()) ⟩
