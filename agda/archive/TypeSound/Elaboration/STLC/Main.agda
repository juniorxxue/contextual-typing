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
preserve (S.⊢d-lam-n ⊢e) = T.⊢ƛ (preserve ⊢e)
preserve (S.⊢d-app₁ ⊢e ⊢e₁) = T.⊢· (preserve ⊢e) (preserve ⊢e₁)
preserve (S.⊢d-app₂ ⊢e ⊢e₁) = T.⊢· (preserve ⊢e) (preserve ⊢e₁)
preserve (S.⊢d-sub ⊢e x) = preserve ⊢e


req : T.Term → S.Counter
req (T.lit x) = S.Z
req (T.` x) = S.Z
req (T.ƛ x ⇒ e) = S.S (req e)
req (e₁ T.· e₂) with req e₁
... | S.Z = S.Z
... | S.S r = r


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
    → req e₁ ≡ S.Z ⊎ req e₂ ≡ S.Z
    → Γ ⊢ e₁ ⦂ A ⇒ B ⟶ e₁'
    → Γ ⊢ e₂ ⦂ A ⟶ e₂'
    → Γ ⊢ e₁ T.· e₂ ⦂ B ⟶ e₁' S.· e₂'

  e-app2 : ∀ {Γ e₁ e₂ A B e₁' e₂' m n}
    → req e₂ ≡ S.S n
    → req e₁ ≡ S.S m
    → Γ ⊢ e₁ ⦂ A ⇒ B ⟶ e₁'
    → Γ ⊢ e₂ ⦂ A ⟶ e₂'
    → Γ ⊢ e₁ T.· e₂ ⦂ B ⟶ e₁' S.· (e₂' S.⦂ A)

annotability : ∀ {Γ e A e'}
  → Γ ⊢ e ⦂ A ⟶ e'
  → Γ S.⊢d (req e) # e' ⦂ A
annotability e-int = S.⊢d-int
annotability (e-var x) = S.⊢d-var x
annotability (e-lam ⊢e) = S.⊢d-lam-n (annotability ⊢e)
annotability (e-app1 {e₁ = e₁} (inj₁ x) ⊢e₁ ⊢e₂) with req e₁ | annotability ⊢e₁
... | S.Z | ⊢e₁' = S.⊢d-app₁ ⊢e₁' (annotability ⊢e₂)
annotability (e-app1 {e₁ = e₁} {e₂ = e₂} (inj₂ y) ⊢e₁ ⊢e₂) with req e₂ | req e₁ | annotability ⊢e₁ | annotability ⊢e₂
... | S.Z | S.Z | ⊢e₁' | ⊢e₂' = S.⊢d-app₁ ⊢e₁' (annotability ⊢e₂)
... | S.Z | S.S r | ⊢e₁' | ⊢e₂' = S.⊢d-app₂ ⊢e₁' ⊢e₂'
annotability (e-app2  {e₁ = e₁} {e₂ = e₂} eq1 eq2 ⊢e₁ ⊢e₂) with req e₁ | req e₂ | annotability ⊢e₁ | annotability ⊢e₂
... | S.S r1 | S.S r2 | ⊢e₁' | ⊢e₂' = S.⊢d-app₂ ⊢e₁' (S.⊢d-ann ⊢e₂')
