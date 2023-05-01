module Soundness where

open import Data.Nat using (ℕ; zero; suc; _+_; _*_; _^_; _∸_)
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

infix 4 _⊩_⇚_
data _⊩_⇚_ : Context → List Term → List Type → Set where
  ⊩none⇚ : ∀ {Γ}
    → Γ ⊩ [] ⇚ []

  ⊩cons⇚ : ∀ {Γ es As e A}
    → Γ ⊩ es ⇚ As
    → Γ ⊢d ∞ ╏ e ⦂ A
    → Γ ⊩ (e ∷ es) ⇚ (A ∷ As)

⊩-elim : ∀ {Γ e H A es T As A'}
  → Γ ⊢d c 0 ╏ e ⦂ A
  → Γ ⊩ es ⇚ As
  → ❪ H , A ❫↣❪ es , T , As , A' ❫ 
  → Γ ⊢d c 0 ╏ e ▻ es ⦂ A'
⊩-elim ⊢d ⊩empty⇚ none = ⊢d
⊩-elim ⊢d (⊩cons⇚ ⊩es ⊢e) (have spl) = ⊩-elim (⊢d-app₁ ⊢d ⊢e) ⊩es spl

infix 4 _⊩_⇛_
data _⊩_⇛_ : Context → List Term → List Type → Set where
  ⊩none⇛ : ∀ {Γ}
    → Γ ⊩ [] ⇛ []

  ⊩cons⇛ : ∀ {Γ es As e A}
    → Γ ⊩ es ⇛ As
    → Γ ⊢d c 0 ╏ e ⦂ A
    → Γ ⊩ (e ∷ es) ⇛ (A ∷ As)

sound-≤ : ∀ {Γ H A es T As A'}
  → Γ ⊢a A ≤ H
  → ❪ H , A ❫↣❪ es , T , As , A' ❫
  → (A' ≤d T) × (Γ ⊩ es ⇚ As)

sound-inf : ∀ {Γ e H A es As A'}
  → Γ ⊢a H ⇛ e ⇛ A
  → ❪ H , A ❫↣❪ es , Top , As , A' ❫
  → Γ ⊢d c 0 ╏ e ▻ es ⦂ A'

sound-chk : ∀ {Γ e H A es T As A'}
  → Γ ⊢a H ⇛ e ⇛ A
  → ❪ H , A ❫↣❪ es , T , As , A' ❫
  → Γ ⊢d ∞ ╏ e ▻ es ⦂ T

-- looks like we haven't used new 2 apps rules in soundness proof so far (1 essential case left)

subst :  ∀ {Γ A B e es e₁}
  → Γ , A ⊢d c 0 ╏ e ▻ es ⦂ B
  → Γ ⊢d c 0 ╏ e₁ ⦂ A
  → Γ ⊢d c 0 ╏ ((ƛ e) · e₁) ▻ es ⦂ B
subst {es = []} ⊢e ⊢e₁ = ⊢d-app₂ (⊢d-lam₂ ⊢e) ⊢e₁
subst {es = e₂ ∷ es} ⊢e ⊢e₁ = {!subst {es = es} ⊢e ⊢e₁!}

sound-≤ ≤a-int none = ⟨ ≤d-int , ⊩none⇚ ⟩
sound-≤ ≤a-top none = ⟨ ≤d-top , ⊩none⇚ ⟩
sound-≤ (≤a-arr C≤A B≤D) none = ⟨ (≤d-arr ΓC≤A ΓB≤D) , ⊩none⇚ ⟩
  where ΓB≤D = proj₁ (sound-≤ B≤D none)
        ΓC≤A = proj₁ (sound-≤ C≤A none)
sound-≤ (≤a-hint ⊢e A≤H) (have spl) = ⟨ (proj₁ (sound-≤ A≤H spl)) , ⊩cons⇚ (proj₂ (sound-≤ A≤H spl)) (sound-chk ⊢e none) ⟩

sound-inf (⊢a-lit _) none = ⊢d-int
sound-inf (⊢a-var ∋ A≤H) spl = ⊩-elim (⊢d-var ∋) arg-chks spl
  where arg-chks = proj₂ (sound-≤ A≤H spl)
sound-inf (⊢a-app ⊢e) spl = sound-inf ⊢e (have spl)
sound-inf (⊢a-ann ⊢e A≤H) spl = ⊩-elim (⊢d-ann (sound-chk ⊢e none)) arg-chks spl
  where arg-chks = proj₂ (sound-≤ A≤H spl)
sound-inf (⊢a-lam₂ ⊢e ⊢f) (have spl) = {!sound-inf ⊢f ?!}
-- sound-inf (⊢a-lam₂ ⊢e ⊢f) (have none) = ⊢d-app₂ (⊢d-lam₂ (sound-inf ⊢f none)) (sound-inf ⊢e none)
-- sound-inf (⊢a-lam₂ ⊢e ⊢f) (have (have spl)) = {!!}

sound-chk (⊢a-lit ≤a-int) none = ⊢d-sub ⊢d-int ≤d-refl
sound-chk (⊢a-lit ≤a-top) none = ⊢d-sub ⊢d-int ≤d-top
sound-chk (⊢a-var ∋ A≤H) spl = ⊢d-sub elims A'≤T
  where arg-chks = proj₂ (sound-≤ A≤H spl)
        elims = ⊩-elim (⊢d-var ∋) arg-chks spl
        A'≤T = proj₁ (sound-≤ A≤H spl)
sound-chk (⊢a-app ⊢e) spl = sound-chk ⊢e (have spl)
sound-chk (⊢a-ann ⊢e A≤H) spl = ⊢d-sub elims A'≤T
  where arg-chks = proj₂ (sound-≤ A≤H spl)
        elims = ⊩-elim (⊢d-ann (sound-chk ⊢e none)) arg-chks spl
        A'≤T = proj₁ (sound-≤ A≤H spl)        
sound-chk (⊢a-lam₁ ⊢e) none = ⊢d-lam₁ (sound-chk ⊢e none)
sound-chk (⊢a-lam₂ ⊢e ⊢f) (have spl) = {!!}
