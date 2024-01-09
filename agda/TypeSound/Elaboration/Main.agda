module TypeSound.Elaboration.Main where

open import TypeSound.Elaboration.Common
import TypeSound.Elaboration.Target as T
import TypeSound.Elaboration.Source as S
open import TypeSound.Elaboration.Target using (_⊢_⦂_)
open import TypeSound.Elaboration.Source using (_⊢d_#_⦂_)

∥_∥ : S.Term → T.Term
∥ S.lit x ∥ = T.lit x
∥ S.` x ∥ = T.` x
∥ S.ƛ x ⇒ e ∥ = T.ƛ x ⇒ ∥ e ∥
∥ e₁ S.· e₂ ∥ = ∥ e₁ ∥ T.· ∥ e₂ ∥
∥ e S.⦂ A ∥ = ∥ e ∥

preserve : ∀ {Γ e j A}
  → Γ ⊢d j # e ⦂ A
  → Γ ⊢ ∥ e ∥ ⦂ A
preserve _⊢d_#_⦂_.⊢d-int = _⊢_⦂_.⊢n
preserve (_⊢d_#_⦂_.⊢d-var x) = _⊢_⦂_.⊢` x
preserve (_⊢d_#_⦂_.⊢d-ann ⊢e) = preserve ⊢e
preserve (_⊢d_#_⦂_.⊢d-lam-∞ ⊢e) = _⊢_⦂_.⊢ƛ (preserve ⊢e)
preserve (_⊢d_#_⦂_.⊢d-lam-n ⊢e) = _⊢_⦂_.⊢ƛ (preserve ⊢e)
preserve (_⊢d_#_⦂_.⊢d-app₁ ⊢e ⊢e₁) = _⊢_⦂_.⊢· (preserve ⊢e) (preserve ⊢e₁)
preserve (_⊢d_#_⦂_.⊢d-app₂ ⊢e ⊢e₁) = _⊢_⦂_.⊢· (preserve ⊢e) (preserve ⊢e₁)
preserve (_⊢d_#_⦂_.⊢d-sub ⊢e x) = preserve ⊢e
