module TypeSound.Elaboration.Overloading.Main where

open import TypeSound.Elaboration.Overloading.Common
import TypeSound.Elaboration.Overloading.Target as T
import TypeSound.Elaboration.Overloading.Source as S

∥_∥ : S.Term → T.Term
∥ S.lit x ∥ = T.lit x
∥ S.flt x ∥ = T.flt x
∥ S.` x ∥ = T.` x
∥ S.ƛ x ⇒ s ∥ = T.ƛ x ⇒ ∥ s ∥
∥ s S.· s₁ ∥ = ∥ s ∥ T.· ∥ s₁ ∥ 
∥ s S.⦂ x ∥ = ∥ s ∥
∥ S.+ ∥ = T.+
∥ S.+i x ∥ = T.+i x
∥ S.+f x ∥ = T.+f x

preserve-sub : ∀ {B j A}
  → B S.≤d j # A
  → B T.≤ A
preserve-sub S.≤d-Z = T.s-refl
preserve-sub S.≤d-int∞ = T.s-refl
preserve-sub S.≤d-float∞ = T.s-refl
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
preserve S.⊢d-+ = T.⊢+
preserve S.⊢d-+i = T.⊢+i
preserve S.⊢d-+f = T.⊢+f
