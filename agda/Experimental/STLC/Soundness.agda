module STLC.Soundness where

open import STLC.Prelude
open import STLC.Common
open import STLC.Decl
open import STLC.Decl.Properties
open import STLC.Algo
open import STLC.Algo.Properties

subst :  ∀ {Γ A B e e₁ j} (es : List Term)
  → Γ , A ⊢d j # e ▻ map (_↑ 0) es ⦂ B
  → Γ ⊢d 0 # e₁ ⦂ A
  → Γ ⊢d j # ((ƛ e) · e₁) ▻ es ⦂ B
subst {j = j} es ⊢1 ⊢2 = {!!}

sound-inf : ∀ {Γ e H A es As A'}
  → Γ ⊢a H ⇛ e ⇛ A
  → ❪ H , A ❫↣❪ es , □ , As , A' ❫
  → Γ ⊢d 0 # e ▻ es ⦂ A'

sound-chk : ∀ {Γ e H A es T As A'}
  → Γ ⊢a H ⇛ e ⇛ A
  → ❪ H , A ❫↣❪ es , τ T , As , A' ❫
  → ∃[ j ](Γ ⊢d j # e ▻ es ⦂ T)

sound-inf ⊢a-lit none-□ = ⊢d-int
sound-inf (⊢a-var x) none-□ = ⊢d-var x
sound-inf (⊢a-ann ⊢e) none-□ with sound-chk ⊢e none-τ
... | ⟨ j , ⊢e' ⟩ = ⊢d-ann ⊢e'
sound-inf (⊢a-app ⊢e) spl = sound-inf ⊢e (have spl)
sound-inf {es = e ∷ es} (⊢a-lam₂ ⊢e ⊢e₁) (have spl) = subst es (sound-inf ⊢e₁ (spl-weaken spl)) (sound-inf ⊢e none-□)
sound-inf (⊢a-sub ⊢e x x₁) spl = {!!}

sound-chk (⊢a-app ⊢e) spl = {!!}
sound-chk (⊢a-lam₁ ⊢e) none-τ with sound-chk ⊢e none-τ
... | ⟨ j , ⊢e' ⟩ = ⟨ suc j , ⊢d-lam ⊢e' ⟩
sound-chk {es = e ∷ es} (⊢a-lam₂ ⊢e ⊢e₁) (have spl) with sound-chk ⊢e₁ (spl-weaken spl)
... | ⟨ j , ⊢e' ⟩ = ⟨ j , subst es ⊢e' (sound-inf ⊢e none-□) ⟩
sound-chk (⊢a-sub ⊢e x x₁) spl with sound-inf ⊢e none-□
... | ⊢e' = ⟨ 0 , {!!} ⟩
