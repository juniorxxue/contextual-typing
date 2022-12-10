module Properties where

open import Common
open import Dec
open import Algo

sound : ∀ {Γ e A}
  → Γ ⊢d e ∙ ⇛ ∙ A
  → Γ ⊢a Hop ⇛ e ⇛ A
sound ⊢d-int = ⊢a-lit ≤a-top
sound (⊢d-var x) = ⊢a-var x ≤a-top
sound (⊢d-app₁ ⊢d ⊢d₁) = {!!}
sound (⊢d-app₂ ⊢d ⊢d₁) = {!!}
sound (⊢d-ann ⊢d) = {!!}


