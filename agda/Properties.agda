module Properties where

open import Common
open import Dec using (_⊢_∙_∙_; ⇛; ⇚)
open import Algo using (_⊢_⇛_⇛_; Hop)

sound : ∀ {Γ e A}
  → Γ ⊢ Hop ⇛ e ⇛ A
  → Γ ⊢ e ∙ ⇛ ∙ A
sound = {!!}

