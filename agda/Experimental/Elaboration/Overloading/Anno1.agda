module Elaboration.Overloading.Anno1 where

open import Elaboration.Overloading.Common
import Elaboration.Overloading.Target as T
import Elaboration.Overloading.Source as S

req : T.Term → S.Counter
req (T.lit x) = S.♭ S.Z
req (T.flt x) =  S.♭ S.Z
req (T.` x) =  S.♭ S.Z
req (T.ƛ x ⇒ e) = S.S⇒ (req e)
req (e₁ T.· e₂) with req e₁
... | S.♭ x = S.♭ S.Z
... | S.S⇒ r = r
req T.+ = S.♭ S.Z
req (T.+i x) = S.♭ S.Z
req (T.+f x) = S.♭ S.Z

data plusS⇒ : S.Counter → Set where

  plusS⇒-base :
    plusS⇒ (S.♭ S.Z)

  plusS-S⇒ : ∀ {i}
    → plusS⇒ i
    → plusS⇒ (S.S⇒ i)

data plusS⇒∞ : S.Counter → Set where

  plusS⇒-base∞ :
    plusS⇒∞ (S.♭ S.∞)

  plusS-S⇒∞ : ∀ {i}
    → plusS⇒∞ i
    → plusS⇒∞ (S.S⇒ i)

req-plusS⇒ : ∀ e
  → plusS⇒ (req e)
req-plusS⇒ (T.lit x) = plusS⇒-base
req-plusS⇒ (T.flt x) = plusS⇒-base
req-plusS⇒ (T.` x) = plusS⇒-base
req-plusS⇒ (T.ƛ x ⇒ e) = plusS-S⇒ (req-plusS⇒ e)
req-plusS⇒ (e₁ T.· e₂) with req e₁ | req-plusS⇒ e₁ 
... | S.♭ x | IH = plusS⇒-base
... | S.S⇒ r | plusS-S⇒ IH = IH
req-plusS⇒ T.+ = plusS⇒-base
req-plusS⇒ (T.+i x) = plusS⇒-base
req-plusS⇒ (T.+f x) = plusS⇒-base

≤d-refl∞' : ∀ {i A}
  → plusS⇒∞ i
  → A S.≤d i # A
≤d-refl∞' plusS⇒-base∞ = S.≤d-refl∞
≤d-refl∞' (plusS-S⇒∞ ps) = S.≤d-S⇒ (≤d-refl∞' ps)

plusS∞-¬Z : ∀ {i}
  → plusS⇒∞ i
  → i ≢ S.♭ S.Z
plusS∞-¬Z plusS⇒-base∞ = λ ()
plusS∞-¬Z (plusS-S⇒∞ ps) = λ ()

≤d-∞-z-plus : ∀ {i i' B A}
  → B S.≤d i # A
  → plusS⇒ i
  → plusS⇒∞ i'
  → B S.≤d i' # A
≤d-∞-z-plus S.≤d-Z plusS⇒-base ps' = ≤d-refl∞' ps'
≤d-∞-z-plus (S.≤d-and₁ B≤A x) plusS⇒-base ps' = ⊥-elim (x refl)
≤d-∞-z-plus (S.≤d-and₂ B≤A x) plusS⇒-base ps' = ⊥-elim (x refl)
≤d-∞-z-plus (S.≤d-S⇒ B≤A) (plusS-S⇒ ps) ps' = ≤d-∞-z-plus B≤A ps ps'
≤d-∞-z-plus (S.≤d-and₁ B≤A x) (plusS-S⇒ ps) ps' = S.≤d-and₁ (≤d-∞-z-plus B≤A (plusS-S⇒ ps) ps') (plusS∞-¬Z ps')
≤d-∞-z-plus (S.≤d-and₂ B≤A x) (plusS-S⇒ ps) ps' = S.≤d-and₂ (≤d-∞-z-plus B≤A (plusS-S⇒ ps) ps') (plusS∞-¬Z ps')

⊢d-sub-∞' : ∀ {Γ i e A i'}
  → Γ S.⊢d i # e ⦂ A
  → plusS⇒ i
  → plusS⇒∞ i'
  → Γ S.⊢d i' # e ⦂ A
⊢d-sub-∞' ⊢e plusS⇒-base plusS⇒-base∞ = S.⊢d-sub ⊢e S.≤d-refl∞ (λ ())
⊢d-sub-∞' ⊢e plusS⇒-base (plusS-S⇒∞ ps') = S.⊢d-sub ⊢e (≤d-refl∞' (plusS-S⇒∞ ps')) (λ ())
⊢d-sub-∞' (S.⊢d-lam₂ ⊢e) (plusS-S⇒ ps) plusS⇒-base∞ = S.⊢d-lam₁ (⊢d-sub-∞' ⊢e ps plusS⇒-base∞)
⊢d-sub-∞' (S.⊢d-lam₂ ⊢e) (plusS-S⇒ ps) (plusS-S⇒∞ ps') = S.⊢d-lam₂ (⊢d-sub-∞' ⊢e ps ps')
⊢d-sub-∞' (S.⊢d-app⇒ ⊢e ⊢e₁) (plusS-S⇒ ps) plusS⇒-base∞ = S.⊢d-app⇒ (⊢d-sub-∞' ⊢e (plusS-S⇒ (plusS-S⇒ ps)) (plusS-S⇒∞ plusS⇒-base∞)) ⊢e₁
⊢d-sub-∞' (S.⊢d-app⇒ ⊢e ⊢e₁) (plusS-S⇒ ps) (plusS-S⇒∞ ps') = S.⊢d-app⇒ (⊢d-sub-∞' ⊢e (plusS-S⇒ (plusS-S⇒ ps)) (plusS-S⇒∞ (plusS-S⇒∞ ps'))) ⊢e₁
⊢d-sub-∞' (S.⊢d-sub ⊢e x x₁) (plusS-S⇒ ps) ps' = S.⊢d-sub ⊢e (≤d-∞-z-plus x (plusS-S⇒ ps) ps') (plusS∞-¬Z ps')
  
⊢d-sub-∞ : ∀ {Γ i e A}
  → Γ S.⊢d i # e ⦂ A
  → plusS⇒ i
  → Γ S.⊢d S.♭ S.∞ # e ⦂ A
⊢d-sub-∞ ⊢e ps = ⊢d-sub-∞' ⊢e ps plusS⇒-base∞

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
    → req e₁ ≡ S.♭ S.Z ⊎ req e₂ ≡ S.♭ S.Z
    → Γ ⊢ e₁ ⦂ A ⇒ B ⟶ e₁'
    → Γ ⊢ e₂ ⦂ A ⟶ e₂'
    → Γ ⊢ e₁ T.· e₂ ⦂ B ⟶ e₁' S.· e₂'

  e-app2 : ∀ {Γ e₁ e₂ A B e₁' e₂' i₁ i₂}
    → req e₂ ≡ S.S⇒ i₁
    → req e₁ ≡ S.S⇒ i₂
    → Γ ⊢ e₁ ⦂ A ⇒ B ⟶ e₁'
    → Γ ⊢ e₂ ⦂ A ⟶ e₂'
    → Γ ⊢ e₁ T.· e₂ ⦂ B ⟶ e₁' S.· (e₂' S.⦂ A)

annotability : ∀ {Γ e A e'}
  → Γ ⊢ e ⦂ A ⟶ e'
  → Γ S.⊢d (req e) # e' ⦂ A
annotability e-int = S.⊢d-int
annotability (e-var x) = S.⊢d-var x
annotability (e-lam ⊢e) = S.⊢d-lam₂ (annotability ⊢e)
annotability (e-app1 {e₁ = e₁} {e₂ = e₂} (inj₁ x) ⊢e₁ ⊢e₂) with req e₁ | annotability ⊢e₁
... | S.♭ S.Z | ⊢e₁' = S.⊢d-app⇐ (S.⊢d-sub ⊢e₁' (S.≤d-arr-S⇐ S.≤d-refl∞ S.≤d-Z) (λ ())) (⊢d-sub-∞ (annotability ⊢e₂) (req-plusS⇒ e₂)) -- trivial
annotability (e-app1 {e₁ = e₁} {e₂ = e₂} (inj₂ y) ⊢e₁ ⊢e₂)  with req e₁ | req-plusS⇒ e₁ | req e₂ | req-plusS⇒ e₂ | annotability ⊢e₁  | annotability ⊢e₂
... | S.♭ S.Z | r1S | S.♭ S.Z | plusS⇒-base | ⊢e₁' | ⊢e₂' = S.⊢d-app⇐ (S.⊢d-sub ⊢e₁' (S.≤d-arr-S⇐ S.≤d-refl∞ S.≤d-Z) (λ ())) (S.⊢d-sub ⊢e₂' S.≤d-refl∞ (λ ()))
... | S.S⇒ r1 | r1S | S.♭ S.Z | plusS⇒-base | ⊢e₁' | ⊢e₂' = S.⊢d-app⇒ ⊢e₁' ⊢e₂'
annotability (e-app2 {e₁ = e₁} {e₂ = e₂} eq1 eq2 ⊢e₁ ⊢e₂) with req e₁ | req-plusS⇒ e₁ | req e₂ | req-plusS⇒ e₂ | annotability ⊢e₁  | annotability ⊢e₂
... | S.S⇒ r1 | plusS-S⇒ r1S | S.S⇒ r2 | plusS-S⇒ r2S | ⊢e₁' | ⊢e₂' = S.⊢d-app⇒ ⊢e₁' (S.⊢d-ann (⊢d-sub-∞ ⊢e₂' (plusS-S⇒ r2S)))
