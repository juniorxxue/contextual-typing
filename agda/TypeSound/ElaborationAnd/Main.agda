module TypeSound.ElaborationAnd.Main where

open import TypeSound.ElaborationAnd.Common
import TypeSound.ElaborationAnd.Target as T
import TypeSound.ElaborationAnd.Source as S
open import TypeSound.ElaborationAnd.Target using (_⊢_⦂_)
open import TypeSound.ElaborationAnd.Source using (_⊢d_#_⦂_)

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
preserve _⊢d_#_⦂_.⊢d-int = _⊢_⦂_.⊢n
preserve (_⊢d_#_⦂_.⊢d-var x) = _⊢_⦂_.⊢` x
preserve (_⊢d_#_⦂_.⊢d-ann ⊢e) = preserve ⊢e
preserve (_⊢d_#_⦂_.⊢d-lam₁ ⊢e) = _⊢_⦂_.⊢ƛ (preserve ⊢e)
preserve (_⊢d_#_⦂_.⊢d-lam₂ ⊢e) = _⊢_⦂_.⊢ƛ (preserve ⊢e)
preserve (_⊢d_#_⦂_.⊢d-app⇐ ⊢e ⊢e₁) = _⊢_⦂_.⊢· (preserve ⊢e) (preserve ⊢e₁)
preserve (_⊢d_#_⦂_.⊢d-app⇒ ⊢e ⊢e₁) = _⊢_⦂_.⊢· (preserve ⊢e) (preserve ⊢e₁)
preserve (_⊢d_#_⦂_.⊢d-sub ⊢e x x₁) = _⊢_⦂_.⊢sub (preserve ⊢e) (preserve-sub x)
preserve (_⊢d_#_⦂_.⊢d-& ⊢e ⊢e₁) = _⊢_⦂_.⊢& (preserve ⊢e) (preserve ⊢e₁)
