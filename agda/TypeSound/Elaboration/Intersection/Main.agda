module TypeSound.Elaboration.Intersection.Main where

open import TypeSound.Elaboration.Intersection.Common
import TypeSound.Elaboration.Intersection.Target as T
import TypeSound.Elaboration.Intersection.Source as S

∥_∥ : S.Term → T.Term
∥ S.lit x ∥ = T.lit x
∥ S.` x ∥ = T.` x
∥ S.ƛ x ⇒ e ∥ = T.ƛ x ⇒ ∥ e ∥
∥ e₁ S.· e₂ ∥ = ∥ e₁ ∥ T.· ∥ e₂ ∥
∥ e S.⦂ A ∥ = ∥ e ∥

preserve-sub : ∀ {B j A}
  → B S.≤d j # A
  → B T.≤ A
preserve-sub S.≤d-Z = T.s-refl
preserve-sub S.≤d-int∞ = T.s-refl
preserve-sub S.≤d-top = T.s-top
preserve-sub (S.≤d-arr-∞ B≤A B≤A₁) = T.s-arr (preserve-sub B≤A) (preserve-sub B≤A₁)
preserve-sub (S.≤d-arr-S⇐ B≤A B≤A₁) = T.s-arr T.s-refl (preserve-sub B≤A₁)
preserve-sub (S.≤d-and₁ B≤A x) = T.s-and-l (preserve-sub B≤A)
preserve-sub (S.≤d-and₂ B≤A x) = T.s-and-r (preserve-sub B≤A)
preserve-sub (S.≤d-and B≤A B≤A₁) = T.s-and (preserve-sub B≤A) (preserve-sub B≤A₁)

preserve : ∀ {Γ e j A}
  → Γ S.⊢d j # e ⦂ A
  → Γ T.⊢ ∥ e ∥ ⦂ A
preserve S.⊢d-int = T.⊢n
preserve (S.⊢d-var x) = T.⊢` x
preserve (S.⊢d-ann ⊢e) = preserve ⊢e
preserve (S.⊢d-lam₁ ⊢e) = T.⊢ƛ (preserve ⊢e)
preserve (S.⊢d-lam₂ ⊢e) = T.⊢ƛ (preserve ⊢e)
preserve (S.⊢d-app⇐ ⊢e ⊢e₁) = T.⊢· (preserve ⊢e) (preserve ⊢e₁)
preserve (S.⊢d-app⇒ ⊢e ⊢e₁) = T.⊢· (preserve ⊢e) (preserve ⊢e₁)
preserve (S.⊢d-sub ⊢e x x₁) = T.⊢sub (preserve ⊢e) (preserve-sub x)
preserve (S.⊢d-& ⊢e ⊢e₁) = T.⊢& (preserve ⊢e) (preserve ⊢e₁)
