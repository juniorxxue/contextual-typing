module TypeSound.Elaboration.STLC.Main where

open import TypeSound.Elaboration.STLC.Common
import TypeSound.Elaboration.STLC.Target as T
import TypeSound.Elaboration.STLC.Source as S

∥_∥ : S.Term → T.Term
∥ S.lit x ∥ = T.lit x
∥ S.` x ∥ = T.` x
∥ S.ƛ x ⇒ e ∥ = T.ƛ x ⇒ ∥ e ∥
∥ e₁ S.· e₂ ∥ = ∥ e₁ ∥ T.· ∥ e₂ ∥
∥ e S.⦂ A ∥ = ∥ e ∥

preserve : ∀ {Γ e j A}
  → Γ S.⊢d j # e ⦂ A
  → Γ T.⊢ ∥ e ∥ ⦂ A
preserve S.⊢d-int = T.⊢n
preserve (S.⊢d-var x) = T.⊢` x
preserve (S.⊢d-ann ⊢e) = preserve ⊢e
preserve (S.⊢d-lam-∞ ⊢e) = T.⊢ƛ (preserve ⊢e)
preserve (S.⊢d-lam-n ⊢e) = T.⊢ƛ (preserve ⊢e)
preserve (S.⊢d-app₁ ⊢e ⊢e₁) = T.⊢· (preserve ⊢e) (preserve ⊢e₁)
preserve (S.⊢d-app₂ ⊢e ⊢e₁) = T.⊢· (preserve ⊢e) (preserve ⊢e₁)
preserve (S.⊢d-sub ⊢e x) = preserve ⊢e
