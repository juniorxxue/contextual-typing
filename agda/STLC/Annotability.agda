module STLC.Annotability where

open import STLC.Prelude
open import STLC.Common
open import STLC.Decl

data TTerm : Set where
  tlit : ℕ → TTerm
  tvar : ℕ → TTerm
  tlam : TTerm → TTerm
  tapp : TTerm → TTerm → TTerm

{-
infix  4  _⊢_⦂_

data _⊢_⦂_ : Context → TTerm → Type → Set where

  ⊢n : ∀ {Γ n}
    → Γ ⊢ (tlit n) ⦂ Int
    
  ⊢` : ∀ {Γ x A}
    → Γ ∋ x ⦂ A
      -----------
    → Γ ⊢ tvar x ⦂ A
    
  ⊢ƛ : ∀ {Γ e A B}
    → Γ , A ⊢ e ⦂ B
      -------------------
    → Γ ⊢ tlam e ⦂ A ⇒ B
    
  ⊢· : ∀ {Γ e₁ e₂ A B}
    → Γ ⊢ e₁ ⦂ A ⇒ B
    → Γ ⊢ e₂ ⦂ A
      -------------
    → Γ ⊢ tapp e₁ e₂ ⦂ B
-}

req : TTerm → Counter
req (tlit x) = Z
req (tvar x) = Z
req (tlam e) = S (req e)
req (tapp e₁ e₂) with req e₁
... | ∞ = Z
... | Z = Z
... | S r = r

infix 3 _⊢1_⦂_⟶_

data _⊢1_⦂_⟶_ : Context → TTerm → Type → Term → Set where

  e-int : ∀ {Γ n}
    → Γ ⊢1 (tlit n) ⦂ Int ⟶ (lit n)

  e-var : ∀ {Γ x A}
    → Γ ∋ x ⦂ A
    → Γ ⊢1 (tvar x) ⦂ A ⟶ (` x)

  e-lam : ∀ {Γ e A B e'}
    → Γ , A ⊢1 e ⦂ B ⟶ e'
    → Γ ⊢1 tlam e ⦂ A ⇒ B ⟶ (ƛ e')

  e-app1 : ∀ {Γ e₁ e₂ A B e₁' e₂'}
    → req e₁ ≡ Z ⊎ req e₂ ≡ Z
    → Γ ⊢1 e₁ ⦂ A ⇒ B ⟶ e₁'
    → Γ ⊢1 e₂ ⦂ A ⟶ e₂'
    → Γ ⊢1 tapp e₁ e₂ ⦂ B ⟶ e₁' · e₂'

  e-app2 : ∀ {Γ e₁ e₂ A B e₁' e₂' m n}
    → req e₂ ≡ S n
    → req e₁ ≡ S m
    → Γ ⊢1 e₁ ⦂ A ⇒ B ⟶ e₁'
    → Γ ⊢1 e₂ ⦂ A ⟶ e₂'
    → Γ ⊢1 tapp e₁ e₂ ⦂ B ⟶ e₁' · (e₂' ⦂ A)


data plusS⇒ : Counter → Set where

  plusS⇒-base :
    plusS⇒ Z

  plusS-S⇒ : ∀ {i}
    → plusS⇒ i
    → plusS⇒ (S i)

data plusS⇒∞A : Counter → Type → Set where

  plusS⇒-base∞A : ∀ {A}
    → plusS⇒∞A ∞ A

  plusS-S⇒∞A : ∀ {i A B}
    → plusS⇒∞A i B
    → plusS⇒∞A (S i) (A ⇒ B)

req-plusS⇒ : ∀ e
  → plusS⇒ (req e)
req-plusS⇒ (tlit x) = plusS⇒-base
req-plusS⇒ (tvar x) = plusS⇒-base
req-plusS⇒ (tlam e) = plusS-S⇒ (req-plusS⇒ e)
req-plusS⇒ (tapp e e₁) with req e | req-plusS⇒ e
... | ∞ | IH = plusS⇒-base
... | Z | IH = plusS⇒-base
... | S r | plusS-S⇒ IH = IH

⊢d-sub-∞' : ∀ {Γ i e A i'}
  → Γ ⊢d i # e ⦂ A
  → plusS⇒ i
  → plusS⇒∞A i' A
  → Γ ⊢d i' # e ⦂ A
⊢d-sub-∞' ⊢e plusS⇒-base plusS⇒-base∞A = ⊢d-sub ⊢e (λ ())
⊢d-sub-∞' ⊢e plusS⇒-base (plusS-S⇒∞A ps') = ⊢d-sub ⊢e (λ ())
⊢d-sub-∞' (⊢d-lam-n ⊢e) (plusS-S⇒ ps) plusS⇒-base∞A = ⊢d-lam-∞ (⊢d-sub-∞' ⊢e ps plusS⇒-base∞A)
⊢d-sub-∞' (⊢d-lam-n ⊢e) (plusS-S⇒ ps) (plusS-S⇒∞A ps') = ⊢d-lam-n (⊢d-sub-∞' ⊢e ps ps')
⊢d-sub-∞' (⊢d-app₂ ⊢e ⊢e₁) (plusS-S⇒ ps) plusS⇒-base∞A = ⊢d-app₂ (⊢d-sub-∞' ⊢e (plusS-S⇒ (plusS-S⇒ ps)) (plusS-S⇒∞A plusS⇒-base∞A)) ⊢e₁
⊢d-sub-∞' (⊢d-app₂ ⊢e ⊢e₁) (plusS-S⇒ ps) (plusS-S⇒∞A ps') = ⊢d-app₂ (⊢d-sub-∞' ⊢e (plusS-S⇒ (plusS-S⇒ ps)) (plusS-S⇒∞A (plusS-S⇒∞A ps'))) ⊢e₁
⊢d-sub-∞' (⊢d-sub ⊢e x) (plusS-S⇒ ps) plusS⇒-base∞A = ⊢d-sub ⊢e (λ ())
⊢d-sub-∞' (⊢d-sub ⊢e x) (plusS-S⇒ ps) (plusS-S⇒∞A ps') = ⊢d-sub ⊢e (λ ())

⊢d-sub-∞ : ∀ {Γ j e A}
  → Γ ⊢d j # e ⦂ A
  → plusS⇒ j
  → Γ ⊢d ∞ # e ⦂ A
⊢d-sub-∞ ⊢e ps = ⊢d-sub-∞' ⊢e ps plusS⇒-base∞A  

annotability : ∀ {Γ e A e'}
  → Γ ⊢1 e ⦂ A ⟶ e'
  → Γ ⊢d (req e) # e' ⦂ A
annotability e-int = ⊢d-int
annotability (e-var x) = ⊢d-var x
annotability (e-lam ⊢e) = ⊢d-lam-n (annotability ⊢e)
annotability (e-app1 {e₁ = e₁} {e₂ = e₂} (inj₁ x) ⊢e₁ ⊢e₂) with req e₁ | annotability ⊢e₁ | annotability ⊢e₂
... | Z | ⊢e₁' | ⊢e₂' = ⊢d-app₁ ⊢e₁' (⊢d-sub-∞ ⊢e₂' (req-plusS⇒ e₂))
annotability (e-app1 {e₁ = e₁} {e₂ = e₂} (inj₂ y) ⊢e₁ ⊢e₂) with req e₁ | req-plusS⇒ e₁
                                                              | req e₂ | req-plusS⇒ e₂
                                                              | annotability ⊢e₁ | annotability ⊢e₂
... | Z | r1S | Z | r2S | ⊢e₁' | ⊢e₂' = ⊢d-app₁ ⊢e₁' (⊢d-sub ⊢e₂' (λ ()))
... | S r1 | r1S | Z | r2S | ⊢e₁' | ⊢e₂' = ⊢d-app₂ ⊢e₁' ⊢e₂'
annotability (e-app2 {e₁ = e₁} {e₂ = e₂} eq1 eq2 ⊢e₁ ⊢e₂) with req e₁ | req-plusS⇒ e₁
                                                            | req e₂ | req-plusS⇒ e₂
                                                            | annotability ⊢e₁ | annotability ⊢e₂
... | S r1 | r1S | S r2 | r2S | ⊢e₁' | ⊢e₂' = ⊢d-app₂ ⊢e₁' (⊢d-ann (⊢d-sub-∞ ⊢e₂' r2S))
