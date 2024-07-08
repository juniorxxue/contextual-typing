module Elaboration.STLC.Anno3 where

open import Elaboration.STLC.Common
import Elaboration.STLC.Target as T
import Elaboration.STLC.Source as S

req : T.Term → ℕ
req (T.lit x) = 0
req (T.` x) = 0
req (T.ƛ x ⇒ e) = suc (req e)
req (e₁ T.· e₂) with req e₁
... | 0 = 0
... | suc n = n


infix 3 _⊢_⦂_⟶_

data _⊢_⦂_⟶_ : Context → T.Term → Type → S.Term → Set where

  e-int : ∀ {Γ n}
    → Γ ⊢ (T.lit n) ⦂ Int ⟶ (S.lit n)

  e-var : ∀ {Γ x A}
    → Γ ∋ x ⦂ A
    → Γ ⊢ (T.` x) ⦂ A ⟶ (S.` x)

  e-lam : ∀ {Γ x e A B e'}
    → Γ , x ⦂ A ⊢ e ⦂ B ⟶ e'
    → Γ ⊢ T.ƛ x ⇒ e ⦂ A ⇒ B ⟶ (S.ƛ x ⇒ e')

  e-app1 : ∀ {Γ e₁ e₂ A B e₁' e₂'}
    → req e₁ ≡ 0 ⊎ req e₂ ≡ 0
    → Γ ⊢ e₁ ⦂ A ⇒ B ⟶ e₁'
    → Γ ⊢ e₂ ⦂ A ⟶ e₂'
    → Γ ⊢ e₁ T.· e₂ ⦂ B ⟶ e₁' S.· e₂'

  e-app2 : ∀ {Γ e₁ e₂ A B e₁' e₂' m n}
    → req e₂ ≡ suc n
    → req e₁ ≡ suc m
    → Γ ⊢ e₁ ⦂ A ⇒ B ⟶ e₁'
    → Γ ⊢ e₂ ⦂ A ⟶ e₂'
    → Γ ⊢ e₁ T.· e₂ ⦂ B ⟶ e₁' S.· (e₂' S.⦂ A)

  e-app3 : ∀ {Γ e₁ e₂ A B e₁' e₂' m n}
    → req e₂ ≡ suc n
    → req e₁ ≡ suc m
    → Γ ⊢ e₁ ⦂ A ⇒ B ⟶ e₁'
    → Γ ⊢ e₂ ⦂ A ⟶ e₂'
    → Γ ⊢ e₁ T.· e₂ ⦂ B ⟶ (e₁' S.⦂ A ⇒ B) S.· e₂'

annotability : ∀ {Γ e A e'}
  → Γ ⊢ e ⦂ A ⟶ e'
  → Γ S.⊢d S.‶ (req e) # e' ⦂ A
annotability e-int = S.⊢d-int
annotability (e-var x) = S.⊢d-var x
annotability (e-lam e-e) = S.⊢d-lam-n (annotability e-e)
annotability (e-app1 {e₁ = e₁} (inj₁ x) ⊢e₁ ⊢e₂) with req e₁ | annotability ⊢e₁ | annotability ⊢e₂
... | zero | ⊢e₁' | ⊢e₂' = S.⊢d-app₁ ⊢e₁' (S.⊢d-∞ ⊢e₂')
annotability (e-app1 {e₁ = e₁} {e₂ = e₂} (inj₂ y) ⊢e₁ ⊢e₂) with req e₁ | req e₂ | annotability ⊢e₁ | annotability ⊢e₂
... | zero | zero | ⊢e₁' | ⊢e₂' = S.⊢d-app₁ ⊢e₁' (S.⊢d-∞ ⊢e₂')
... | suc n | zero | ⊢e₁' | ⊢e₂' = S.⊢d-app₂ ⊢e₁' ⊢e₂'
annotability (e-app2 {e₁ = e₁} {e₂ = e₂} eq1 eq2 ⊢e₁ ⊢e₂) with req e₁ | req e₂ | annotability ⊢e₁ | annotability ⊢e₂
... | suc r1 | suc r2 | ⊢e₁' | ⊢e₂' = S.⊢d-app₂ ⊢e₁' (S.⊢d-ann (S.⊢d-∞ ⊢e₂'))
annotability (e-app3 {e₁ = e₁} {e₂ = e₂} eq1 eq2 ⊢e₁ ⊢e₂) with req e₁ | req e₂ | annotability ⊢e₁ | annotability ⊢e₂
... | suc r1 | suc r2 | ⊢e₁' | ⊢e₂' = S.⊢d-sub' (S.⊢d-app₁ (S.⊢d-ann (S.⊢d-∞ ⊢e₁')) (S.⊢d-∞ ⊢e₂'))
