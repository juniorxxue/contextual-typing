module TypeSound.Main where

open import TypeSound.Common
import TypeSound.Target as T
import TypeSound.Source as S

∥_∥ : S.Term → T.Term
∥_∥r : S.Record → T.Record

∥ S.rnil ∥r = T.rnil
∥ S.r⟦ l ↦ e ⟧ rs ∥r =  T.r⟦ l  ↦ ∥ e ∥ ⟧ (∥ rs ∥r)

∥ S.𝕔 S.lit x ∥ = T.lit x
∥ S.𝕔 S.flt x ∥ = T.flt x
∥ S.𝕔 S.+s ∥ = T.+
∥ S.𝕔 S.+i x ∥ = T.+i x
∥ S.𝕔 S.+f x ∥ = T.+f x
∥ S.` x ∥ = T.` x
∥ S.ƛ x ⇒ e ∥ = T.ƛ x ⇒ ∥ e ∥
∥ e S.· e₁ ∥ = ∥ e ∥ T.· ∥ e₁ ∥ 
∥ e S.⦂ x ∥ = ∥ e ∥
∥ S.𝕣 x ∥ = T.𝕣 ∥ x ∥r
∥ e S.𝕡 x ∥ = ∥ e ∥ T.𝕡 x

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
preserve-sub (S.≤d-rcd∞ x) = T.s-rcd (preserve-sub x)
preserve-sub (S.≤d-arr-S⇒ x x₁) = T.s-arr (preserve-sub x) (preserve-sub x₁)
preserve-sub (S.≤d-rcd-Sl x) = T.s-rcd (preserve-sub x)

preserve : ∀ {Γ e j A}
  → Γ S.⊢d j # e ⦂ A
  → Γ T.⊢ ∥ e ∥ ⦂ A
preserve-r : ∀ {Γ j rs As}
  → Γ S.⊢r j # rs ⦂ As
  → Γ T.⊢r ∥ rs ∥r ⦂ As

preserve-r S.⊢r-nil = T.⊢r-nil
preserve-r (S.⊢r-one x) = T.⊢r-one (preserve x)
preserve-r (S.⊢r-cons x ⊢rs x₁) = T.⊢r-cons (preserve x) (preserve-r ⊢rs)

preserve (S.⊢d-c {c = S.lit x}) = T.⊢n
preserve (S.⊢d-c {c = S.flt x}) = T.⊢m
preserve (S.⊢d-c {c = S.+s}) = T.⊢+
preserve (S.⊢d-c {c = S.+i x}) = T.⊢+i
preserve (S.⊢d-c {c = S.+f x}) = T.⊢+f
preserve (S.⊢d-var x) = T.⊢` x
preserve (S.⊢d-ann ⊢e) = preserve ⊢e
preserve (S.⊢d-lam₁ ⊢e) = T.⊢ƛ (preserve ⊢e)
preserve (S.⊢d-lam₂ ⊢e) = T.⊢ƛ (preserve ⊢e)
preserve (S.⊢d-app⇐ ⊢e ⊢e₁) = T.⊢· (preserve ⊢e) (preserve ⊢e₁)
preserve (S.⊢d-app⇒ ⊢e ⊢e₁) = T.⊢· (preserve ⊢e) (preserve ⊢e₁)
preserve (S.⊢d-sub ⊢e x x₁) = T.⊢sub (preserve ⊢e) (preserve-sub x)
preserve (S.⊢d-rcd x) = T.⊢rcd (preserve-r x)
preserve (S.⊢d-prj ⊢e) = T.⊢prj (preserve ⊢e)
