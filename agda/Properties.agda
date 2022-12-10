module Properties where

open import Common
open import Dec
open import Algo

sound-chk : ∀ {Γ e A}
  → Γ ⊢d e ∙ ⇚ ∙ A
  → Γ ⊢a h A ⇛ e ⇛ A
sound-chk (⊢d-lam ⊢d) = ⊢a-lam₂ (sound-chk ⊢d)
sound-chk (⊢d-sub ⊢d x) = {!!}

sound : ∀ {Γ e A}
  → Γ ⊢d e ∙ ⇛ ∙ A
  → Γ ⊢a Hop ⇛ e ⇛ A
sound ⊢d-int = ⊢a-lit ≤a-top
sound (⊢d-var x) = ⊢a-var x ≤a-top
sound (⊢d-app₁ ⊢de₁ ⊢de₂) = {!!}
sound (⊢d-app₂ ⊢d ⊢d₁) = {!!}
sound (⊢d-ann ⊢d) = ⊢a-ann (sound-chk ⊢d) ≤a-top


