module STLC.Soundness where

open import STLC.Prelude
open import STLC.Common
open import STLC.Decl
open import STLC.Decl.Properties
open import STLC.Algo
open import STLC.Algo.Properties

sound-inf : ∀ {Γ e H A es As A'}
  → Γ ⊢a H ⇛ e ⇛ A
  → ❪ H , A ❫↣❪ es , □ , As , A' ❫
  → Γ ⊢d Z # e ▻ es ⦂ A'

sound-chk : ∀ {Γ e H A es T As A'}
  → Γ ⊢a H ⇛ e ⇛ A
  → ❪ H , A ❫↣❪ es , τ T , As , A' ❫
  → Γ ⊢d ∞ # e ▻ es ⦂ T

sound-inf ⊢a-lit none-□ = ⊢d-int
sound-inf (⊢a-var x) none-□ = ⊢d-var x
sound-inf (⊢a-ann ⊢e) none-□ = ⊢d-ann (sound-chk ⊢e none-τ)
sound-inf (⊢a-app ⊢e) spl = sound-inf ⊢e (have spl)
sound-inf (⊢a-lam₂ ⊢e ⊢e₁) (have spl) = {!!}
sound-inf (⊢a-sub ⊢e A≈H p) none-□ = sound-inf ⊢e none-□
sound-inf (⊢a-sub ⊢e A≈H p) (have spl) = {!!}

sound-chk (⊢a-app ⊢e) spl = sound-chk ⊢e (have spl)
sound-chk (⊢a-lam₁ ⊢e) none-τ = ⊢d-lam-∞ (sound-chk ⊢e none-τ)
sound-chk (⊢a-lam₂ ⊢e ⊢e₁) (have spl) = {!!}
sound-chk (⊢a-sub ⊢e x x₁) spl = {!!}


→ Γ ⊢ H ⇒ e ⇒ A
→ f H j
→ Γ ⊢j e : A
