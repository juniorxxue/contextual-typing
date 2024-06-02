module Elaboration.Overloading.Anno1 where

open import Elaboration.Overloading.Common
import Elaboration.Overloading.Target as T
import Elaboration.Overloading.Source as S

-- 𝕫 : S.ICounter
pattern 𝕫 = S.𝕔 S.Z

req : T.Term → S.ICounter
req (T.lit x) = 𝕫
req (T.flt x) = 𝕫
req (T.` x) = 𝕫
req (T.ƛ x ⇒ e) = S.S⇒ (req e)
req (e₁ T.· e₂) with req e₁
... | 𝕫 = 𝕫
... | S.𝕔 S.S⇐ x = 𝕫
... | S.S⇒ r = r
req T.+ = 𝕫
req (T.+i x) = 𝕫
req (T.+f x) = 𝕫

infix 3 _⊢_⦂_⟶_
data _⊢_⦂_⟶_ : Context → T.Term → Type → S.Term → Set where

  e-int : ∀ {Γ n}
    → Γ ⊢ (T.lit n) ⦂ Int ⟶ (S.lit n)

  e-flt : ∀ {Γ n}
    → Γ ⊢ (T.flt n) ⦂ Float ⟶ (S.flt n)

  e-var : ∀ {Γ x A}
    → Γ ∋ x ⦂ A
    → Γ ⊢ (T.` x) ⦂ A ⟶ (S.` x)

  e-lam : ∀ {Γ x e A B e'}
    → Γ , x ⦂ A ⊢ e ⦂ B ⟶ e'
    → Γ ⊢ T.ƛ x ⇒ e ⦂ A ⇒ B ⟶ (S.ƛ x ⇒ e')

  e-app1 : ∀ {Γ e₁ e₂ A B e₁' e₂'}
    → req e₁ ≡ 𝕫 ⊎ req e₂ ≡ 𝕫
    → Γ ⊢ e₁ ⦂ A ⇒ B ⟶ e₁'
    → Γ ⊢ e₂ ⦂ A ⟶ e₂'
    → Γ ⊢ e₁ T.· e₂ ⦂ B ⟶ e₁' S.· e₂'

  e-app2 : ∀ {Γ e₁ e₂ A B e₁' e₂' m n}
    → req e₂ ≡ S.S⇒ n
    → req e₁ ≡ S.S⇒ m
    → Γ ⊢ e₁ ⦂ A ⇒ B ⟶ e₁'
    → Γ ⊢ e₂ ⦂ A ⟶ e₂'
    → Γ ⊢ e₁ T.· e₂ ⦂ B ⟶ e₁' S.· (e₂' S.⦂ A)

annotability : ∀ {Γ e A e'}
  → Γ ⊢ e ⦂ A ⟶ e'
  → Γ S.⊢d S.‶ (req e) # e' ⦂ A
annotability e-int = S.⊢d-int
annotability e-flt = S.⊢d-flt
annotability (e-var x) = S.⊢d-var x
annotability (e-lam ⊢e) = S.⊢d-lam₂ (annotability ⊢e)
annotability (e-app1 {e₁ = e₁} (inj₁ x) ⊢e₁ ⊢e₂) with req e₁ | annotability ⊢e₁ | annotability ⊢e₂
... | 𝕫 | ⊢e₁' | ⊢e₂' = S.⊢d-app⇐ (S.⊢d-sub' ⊢e₁' (S.≤d-arr-S⇐ S.≤d-refl∞ S.≤d-Z)) (S.⊢d-∞ ⊢e₂') -- desire a property
annotability (e-app1 {e₁ = e₁} {e₂ = e₂} (inj₂ y) ⊢e₁ ⊢e₂) with req e₁ | req e₂ | annotability ⊢e₁ | annotability ⊢e₂
... | 𝕫 | 𝕫 | ⊢e₁' | ⊢e₂' = S.⊢d-app⇒ (S.⊢d-sub' ⊢e₁' (S.≤d-arr-S⇒ S.≤d-refl∞ S.≤d-Z)) ⊢e₂'
... | S.𝕔 S.S⇐ r | 𝕫 | ⊢e₁' | ⊢e₂' = {!!} -- absurd case
... | S.S⇒ r1 | 𝕫 | ⊢e₁' | ⊢e₂' = S.⊢d-app⇒ ⊢e₁' ⊢e₂'
annotability (e-app2 {e₁ = e₁} {e₂ = e₂} eq1 eq2 ⊢e₁ ⊢e₂)  with req e₁ | req e₂ | annotability ⊢e₁ | annotability ⊢e₂
... | S.S⇒ r1 | S.S⇒ r2 | ⊢e₁' | ⊢e₂' = S.⊢d-app⇒ ⊢e₁' (S.⊢d-ann (S.⊢d-∞ ⊢e₂'))
