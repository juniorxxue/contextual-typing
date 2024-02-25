module Record.Annotatability.Elaboration where

open import Record.Prelude
open import Record.Common
import Record.Decl as S
import Record.Annotatability.Target as T

need : T.Term → S.Counter

{-
need-r : T.Record → S.Counter

need-r T.rnil = S.♭ S.Z
need-r (T.r⟦ l ↦ e ⟧ rs) = {!!}
-}

need (T.𝕔 x) = S.♭ S.Z
need (T.` x) = S.♭ S.Z
need (T.ƛ e) = S.S⇒ (need e)
need (e₁ T.· e₂) with need e₁
... | S.♭ j = S.♭ S.Z
... | S.S⇒ r = r
need (T.𝕣 x) = S.♭ S.Z
need (e T.𝕡 l) = need e

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

data plusS⇒∞A : S.Counter → Type → Set where

  plusS⇒-base∞A : ∀ {A}
    → plusS⇒∞A (S.♭ S.∞) A

  plusS-S⇒∞A : ∀ {i A B}
    → plusS⇒∞A i B
    → plusS⇒∞A (S.S⇒ i) (A ⇒ B)


req-plusS⇒ : ∀ e
  → plusS⇒ (need e)
req-plusS⇒ (T.𝕔 x) = plusS⇒-base
req-plusS⇒ (T.` x) = plusS⇒-base
req-plusS⇒ (T.ƛ e) = plusS-S⇒ (req-plusS⇒ e)
req-plusS⇒ (e₁ T.· e₂) with need e₁ | req-plusS⇒ e₁ 
... | S.♭ x | IH = plusS⇒-base
... | S.S⇒ r | plusS-S⇒ IH = IH
req-plusS⇒ (T.𝕣 x) = plusS⇒-base
req-plusS⇒ (e T.𝕡 x) = req-plusS⇒ e

≤d-refl∞' : ∀ {i A}
  → plusS⇒∞A i A
  → A S.≤d i # A
≤d-refl∞' plusS⇒-base∞A = S.≤d-refl∞
≤d-refl∞' (plusS-S⇒∞A ps) = S.≤d-arr-S⇒ S.≤d-refl∞ (≤d-refl∞' ps)

plusS∞-¬Z : ∀ {i A}
  → plusS⇒∞A i A
  → i ≢ S.♭ S.Z
plusS∞-¬Z plusS⇒-base∞A = λ ()
plusS∞-¬Z (plusS-S⇒∞A ps) = λ ()

≤d-∞-z-plus : ∀ {i i' B A}
  → B S.≤d i # A
  → plusS⇒ i
  → plusS⇒∞A i' A
  → B S.≤d i' # A
≤d-∞-z-plus S.≤d-Z plusS⇒-base ps' = ≤d-refl∞' ps'
≤d-∞-z-plus (S.≤d-arr-S⇒ B≤A B≤A₁) (plusS-S⇒ ps) plusS⇒-base∞A = S.≤d-arr-∞ (≤d-∞-z-plus S.≤d-Z plusS⇒-base plusS⇒-base∞A)
                                                                  (≤d-∞-z-plus B≤A₁ ps plusS⇒-base∞A)
≤d-∞-z-plus (S.≤d-arr-S⇒ B≤A B≤A₁) (plusS-S⇒ ps) (plusS-S⇒∞A ps') = S.≤d-arr-S⇒ B≤A (≤d-∞-z-plus B≤A₁ ps ps')
≤d-∞-z-plus (S.≤d-and₁ B≤A x) ps ps' = S.≤d-and₁ (≤d-∞-z-plus B≤A ps ps') (plusS∞-¬Z ps')
≤d-∞-z-plus (S.≤d-and₂ B≤A x) ps ps' = S.≤d-and₂ (≤d-∞-z-plus B≤A ps ps') (plusS∞-¬Z ps')

⊢d-sub-∞'' : ∀ {Γ i e A i'}
  → Γ S.⊢d i # e ⦂ A
  → plusS⇒ i
  → plusS⇒∞A i' A
  → Γ S.⊢d i' # e ⦂ A
⊢d-sub-∞'' ⊢e plusS⇒-base plusS⇒-base∞A = S.⊢d-sub ⊢e S.≤d-refl∞ (λ ())
⊢d-sub-∞'' ⊢e plusS⇒-base (plusS-S⇒∞A ps') = S.⊢d-sub ⊢e (S.≤d-arr-S⇒ S.≤d-refl∞ (≤d-refl∞' ps')) λ ()
⊢d-sub-∞'' (S.⊢d-lam₂ ⊢e) (plusS-S⇒ ps) plusS⇒-base∞A = S.⊢d-lam₁ (⊢d-sub-∞'' ⊢e ps plusS⇒-base∞A)
⊢d-sub-∞'' (S.⊢d-lam₂ ⊢e) (plusS-S⇒ ps) (plusS-S⇒∞A ps') = S.⊢d-lam₂ (⊢d-sub-∞'' ⊢e ps ps')
⊢d-sub-∞'' (S.⊢d-app⇒ ⊢e ⊢e₁) (plusS-S⇒ ps) plusS⇒-base∞A = S.⊢d-app⇒ (⊢d-sub-∞'' ⊢e (plusS-S⇒ (plusS-S⇒ ps)) (plusS-S⇒∞A plusS⇒-base∞A)) ⊢e₁
⊢d-sub-∞'' (S.⊢d-app⇒ ⊢e ⊢e₁) (plusS-S⇒ ps) (plusS-S⇒∞A ps') = S.⊢d-app⇒ (⊢d-sub-∞'' ⊢e (plusS-S⇒ (plusS-S⇒ ps)) (plusS-S⇒∞A (plusS-S⇒∞A ps'))) ⊢e₁
⊢d-sub-∞'' (S.⊢d-sub ⊢e x x₁) (plusS-S⇒ ps) ps' = S.⊢d-sub ⊢e (≤d-∞-z-plus x (plusS-S⇒ ps) ps') (plusS∞-¬Z ps')

⊢d-sub-∞ : ∀ {Γ i e A}
  → Γ S.⊢d i # e ⦂ A
  → plusS⇒ i
  → Γ S.⊢d S.♭ S.∞ # e ⦂ A
⊢d-sub-∞ ⊢e ps = ⊢d-sub-∞'' ⊢e ps plusS⇒-base∞A

infix 3 _⊢_⦂_⟶_
infix 3 _⊢r_⦂_⟶_

data _⊢_⦂_⟶_ : Context → T.Term → Type → Term → Set
data _⊢r_⦂_⟶_ : Context → T.Record → Type → Record → Set

data _⊢_⦂_⟶_  where

  e-con : ∀ {Γ c}
    → Γ ⊢ (T.𝕔 c) ⦂ c-τ c ⟶ (𝕔 c)

  e-var : ∀ {Γ x A}
    → Γ ∋ x ⦂ A
    → Γ ⊢ (T.` x) ⦂ A ⟶ (` x)

  e-lam : ∀ {Γ e A B e'}
    → Γ , A ⊢ e ⦂ B ⟶ e'
    → Γ ⊢ T.ƛ e ⦂ A ⇒ B ⟶ (ƛ e')

  e-app1 : ∀ {Γ e₁ e₂ A B e₁' e₂'}
    → need e₁ ≡ S.♭ S.Z ⊎ need e₂ ≡ S.♭ S.Z
    → Γ ⊢ e₁ ⦂ A ⇒ B ⟶ e₁'
    → Γ ⊢ e₂ ⦂ A ⟶ e₂'
    → Γ ⊢ e₁ T.· e₂ ⦂ B ⟶ e₁' · e₂'

  e-app2 : ∀ {Γ e₁ e₂ A B e₁' e₂' i₁ i₂}
    → need e₂ ≡ S.S⇒ i₁
    → need e₁ ≡ S.S⇒ i₂
    → Γ ⊢ e₁ ⦂ A ⇒ B ⟶ e₁'
    → Γ ⊢ e₂ ⦂ A ⟶ e₂'
    → Γ ⊢ e₁ T.· e₂ ⦂ B ⟶ e₁' · (e₂' ⦂ A)

data _⊢r_⦂_⟶_ where

  e-rnil : ∀ {Γ}
    → Γ ⊢r T.rnil ⦂ Top ⟶ rnil

  e-one : ∀ {Γ e e' A l}
    → Γ ⊢ e ⦂ A ⟶ e'
    → Γ ⊢r T.r⟦ l ↦ e ⟧ T.rnil ⦂ τ⟦ l ↦ A ⟧  ⟶  r⟦ l ↦ e' ⟧ rnil

  e-cons : ∀ {Γ l e e' rs rs' A As}
    → Γ ⊢ e ⦂ A ⟶ e'
    → Γ ⊢r rs ⦂ As ⟶ rs'
    → Γ ⊢r T.r⟦ l ↦ e ⟧ rs ⦂ (τ⟦ l ↦ A ⟧ & As) ⟶ r⟦ l ↦ e' ⟧ rs'


annotatability : ∀ {Γ e A e'}
  → Γ ⊢ e ⦂ A ⟶ e'
  → Γ S.⊢d (need e) # e' ⦂ A

annotatability e-con = S.⊢d-c
annotatability (e-var x) = S.⊢d-var x
annotatability (e-lam ⊢e) = S.⊢d-lam₂ (annotatability ⊢e)
annotatability (e-app1 {e₁ = e₁} {e₂ = e₂} (inj₁ x) ⊢e₁ ⊢e₂) with need e₁ |  annotatability ⊢e₁
... | S.♭ S.Z | ⊢e₁' = S.⊢d-app⇐ (S.⊢d-sub ⊢e₁' (S.≤d-arr-S⇐ S.≤d-refl∞ S.≤d-Z) (λ ())) (⊢d-sub-∞ (annotatability ⊢e₂) (req-plusS⇒ e₂))
annotatability (e-app1 {e₁ = e₁} {e₂ = e₂} (inj₂ y) ⊢e₁ ⊢e₂) with need e₁
                                                                | req-plusS⇒ e₁
                                                                | need e₂
                                                                | req-plusS⇒ e₂
                                                                | annotatability ⊢e₁
                                                                | annotatability ⊢e₂
... | S.♭ S.Z | r1S | S.♭ S.Z | plusS⇒-base | ⊢e₁' | ⊢e₂' =
  S.⊢d-app⇐ (S.⊢d-sub ⊢e₁' (S.≤d-arr-S⇐ S.≤d-refl∞ S.≤d-Z) (λ ())) (S.⊢d-sub ⊢e₂' S.≤d-refl∞ (λ ()))
... | S.S⇒ r1 | r1S | S.♭ S.Z | plusS⇒-base | ⊢e₁' | ⊢e₂' = S.⊢d-app⇒ ⊢e₁' ⊢e₂'
annotatability (e-app2 {e₁ = e₁} {e₂ = e₂} eq1 eq2 ⊢e₁ ⊢e₂) with need e₁
                                                               | req-plusS⇒ e₁
                                                               | need e₂
                                                               | req-plusS⇒ e₂
                                                               | annotatability ⊢e₁
                                                               | annotatability ⊢e₂
... | S.S⇒ r1 | plusS-S⇒ r1S | S.S⇒ r2 | plusS-S⇒ r2S | ⊢e₁' | ⊢e₂' = S.⊢d-app⇒ ⊢e₁' (S.⊢d-ann (⊢d-sub-∞ ⊢e₂' (plusS-S⇒ r2S)))
