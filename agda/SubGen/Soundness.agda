module SubGen.Soundness where

open import SubGen.Prelude
open import SubGen.Common
open import SubGen.Decl
open import SubGen.Decl.Properties
open import SubGen.Algo
open import SubGen.Algo.Properties

import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; trans; sym; cong; cong-app; subst)
open Eq.≡-Reasoning using (begin_; _≡⟨⟩_; step-≡; _∎)


-- j represents the length of H
len : Hint → Counter
len □ = Z
len (τ A) = ∞
len (⟦ e ⟧⇒ H) = S (len H)

-- this should be a corollary of it
sound-≤ : ∀ {Γ A H A'}
  → Γ ⊢a A ≤ H ⇝ A'
  → A ≤d (len H) # A'

sound-≤ ≤a-int = ≤d-int∞
sound-≤ ≤a-base = ≤d-base∞
sound-≤ ≤a-top = ≤d-top
sound-≤ ≤a-□ = ≤d-Z
sound-≤ (≤a-arr A≤H A≤H₁) = ≤d-arr-∞ (sound-≤ A≤H) (sound-≤ A≤H₁)
sound-≤ {Γ = Γ} (≤a-hint x A≤H) = ≤d-arr-S ≤d-refl∞ (sound-≤ A≤H)
sound-≤ (≤a-and-l A≤H) = ≤d-and₁ (sound-≤ A≤H)
sound-≤ (≤a-and-r A≤H) = ≤d-and₂ (sound-≤ A≤H)
sound-≤ (≤a-and A≤H A≤H₁) = ≤d-and (sound-≤ A≤H) (sound-≤ A≤H₁)

infix 4 _⊩_⇚_
data _⊩_⇚_ : Context → List Term → List Type → Set where
  ⊩none⇚ : ∀ {Γ}
    → Γ ⊩ [] ⇚ []

  ⊩cons⇚ : ∀ {Γ es As e A}
    → Γ ⊩ es ⇚ As
    → Γ ⊢d ∞ # e ⦂ A
    → Γ ⊩ (e ∷ es) ⇚ (A ∷ As)

⊩-elim : ∀ {Γ e H A es T As A'}
  → Γ ⊢d Z # e ⦂ A
  → Γ ⊩ es ⇚ As
  → ❪ H , A ❫↣❪ es , T , As , A' ❫ 
  → Γ ⊢d Z # e ▻ es ⦂ A'
⊩-elim ⊢d ⊩none⇚ none-□ = ⊢d
⊩-elim ⊢d ⊩none⇚ none-τ = ⊢d
⊩-elim ⊢d (⊩cons⇚ ⊩es ⊢e) (have spl) = ⊩-elim (⊢d-app₁ ⊢d ⊢e) ⊩es spl

infix 4 _⊩_⇛_
data _⊩_⇛_ : Context → List Term → List Type → Set where
  ⊩none⇛ : ∀ {Γ}
    → Γ ⊩ [] ⇛ []

  ⊩cons⇛ : ∀ {Γ es As e A}
    → Γ ⊩ es ⇛ As
    → Γ ⊢d Z # e ⦂ A
    → Γ ⊩ (e ∷ es) ⇛ (A ∷ As)

sound-inf : ∀ {Γ e H A es As A'}
  → Γ ⊢a H ⇛ e ⇛ A
  → ❪ H , A ❫↣❪ es , □ , As , A' ❫
  → Γ ⊢d Z # e ▻ es ⦂ A'

sound-chk : ∀ {Γ e H A es T As A'}
  → Γ ⊢a H ⇛ e ⇛ A
  → ❪ H , A ❫↣❪ es , τ T , As , A' ❫
  → Γ ⊢d ∞ # e ▻ es ⦂ T

sound-inf-0 : ∀ {Γ e A}
  → Γ ⊢a □ ⇛ e ⇛ A
  → Γ ⊢d Z # e ⦂ A
sound-inf-0 ⊢e = sound-inf ⊢e none-□

sound-chk-0 : ∀ {Γ e A}
  → Γ ⊢a τ A ⇛ e ⇛ A
  → Γ ⊢d ∞ # e ⦂ A
sound-chk-0 ⊢e = sound-chk ⊢e none-τ

sound-inf ⊢a-lit none-□ = ⊢d-int
sound-inf (⊢a-var x) none-□ = ⊢d-var x

sound-inf (⊢a-ann ⊢e) none-□ = ⊢d-ann (sound-chk-0 ⊢e)

sound-inf (⊢a-app ⊢e) spl = sound-inf ⊢e (have spl)
sound-inf (⊢a-lam₂ ⊢e ⊢e₁) spl = {!!}
sound-inf (⊢a-sub x ⊢e x₁) spl = {!!}
-- ⊩-elim (⊢d-sub (sound-inf-0 ⊢e) {!!} {!!}) {!!} spl
-- ⊩-elim (sound-inf-0 ⊢e) {!!} {!spl!}

sound-chk (⊢a-app ⊢e) spl = {!!}
sound-chk (⊢a-lam₁ ⊢e) spl = {!!}
sound-chk (⊢a-lam₂ ⊢e ⊢e₁) spl = {!!}
sound-chk (⊢a-sub x ⊢e x₁) spl = ⊢d-sub (⊩-elim {!!} {!!} spl) {!!} (λ ())
sound-chk (⊢a-& ⊢e ⊢e₁) none-τ = ⊢d-& (sound-chk ⊢e none-τ) (sound-chk ⊢e₁ none-τ)
