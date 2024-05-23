module STLC.Annotatability where

open import STLC.Prelude
open import STLC.Common
open import STLC.Decl
open import STLC.Decl.Properties

----------------------------------------------------------------------
--+                                                                +--
--+                              TAS                               +--
--+                                                                +--
----------------------------------------------------------------------

data TTerm : Set where
  tlit : ℕ → TTerm
  tvar : ℕ → TTerm
  tlam : TTerm → TTerm
  tapp : TTerm → TTerm → TTerm

infix  4  _⊢_⦂_

data _⊢_⦂_ : Env → TTerm → Type → Set where

  ⊢n : ∀ {Γ n}
    → Γ ⊢ (tlit n) ⦂ Int
    
  ⊢` : ∀ {Γ x A}
    → Γ ∋ x ⦂ A
      -----------
    → Γ ⊢ tvar x ⦂ A
    
  ⊢ƛ : ∀ {Γ e A B}
    → Γ , A ⊢ e ⦂ B
      -------------------
    → Γ ⊢ tlam e ⦂ A `→ B
    
  ⊢· : ∀ {Γ e₁ e₂ A B}
    → Γ ⊢ e₁ ⦂ A `→ B
    → Γ ⊢ e₂ ⦂ A
      -------------
    → Γ ⊢ tapp e₁ e₂ ⦂ B


----------------------------------------------------------------------
--+                                                                +--
--+                         need function                          +--
--+                                                                +--
----------------------------------------------------------------------

need : TTerm → Counter
need (tlit x) = Z
need (tvar x) = Z
need (tlam e) = S (need e)
need (tapp e₁ e₂) with need e₁
... | ∞ = Z
... | Z = Z
... | S r = r

----------------------------------------------------------------------
--+                                                                +--
--+                          Elaboration                           +--
--+                                                                +--
----------------------------------------------------------------------

infix 3 _⊢1_⦂_⟶_

data _⊢1_⦂_⟶_ : Env → TTerm → Type → Term → Set where

  e-int : ∀ {Γ n}
    → Γ ⊢1 (tlit n) ⦂ Int ⟶ (lit n)

  e-var : ∀ {Γ x A}
    → Γ ∋ x ⦂ A
    → Γ ⊢1 (tvar x) ⦂ A ⟶ (` x)

  e-lam : ∀ {Γ e A B e'}
    → Γ , A ⊢1 e ⦂ B ⟶ e'
    → Γ ⊢1 tlam e ⦂ A `→ B ⟶ (ƛ e')

  e-app1 : ∀ {Γ e₁ e₂ A B e₁' e₂'}
    → need e₁ ≡ Z ⊎ need e₂ ≡ Z
    → Γ ⊢1 e₁ ⦂ A `→ B ⟶ e₁'
    → Γ ⊢1 e₂ ⦂ A ⟶ e₂'
    → Γ ⊢1 tapp e₁ e₂ ⦂ B ⟶ e₁' · e₂'

  e-app2 : ∀ {Γ e₁ e₂ A B e₁' e₂' m n}
    → need e₂ ≡ S n
    → need e₁ ≡ S m
    → Γ ⊢1 e₁ ⦂ A `→ B ⟶ e₁'
    → Γ ⊢1 e₂ ⦂ A ⟶ e₂'
    → Γ ⊢1 tapp e₁ e₂ ⦂ B ⟶ e₁' · (e₂' ⦂ A)

----------------------------------------------------------------------
--+                                                                +--
--+                           Aux Lemmas                           +--
--+                                                                +--
----------------------------------------------------------------------

data plusS`→ : Counter → Set where

  plusS`→-base :
    plusS`→ Z

  plusS-S`→ : ∀ {i}
    → plusS`→ i
    → plusS`→ (S i)

data plusS`→∞A : Counter → Type → Set where

  plusS`→-base∞A : ∀ {A}
    → plusS`→∞A ∞ A

  plusS-S`→∞A : ∀ {i A B}
    → plusS`→∞A i B
    → plusS`→∞A (S i) (A `→ B)

need-plusS`→ : ∀ e
  → plusS`→ (need e)
need-plusS`→ (tlit x) = plusS`→-base
need-plusS`→ (tvar x) = plusS`→-base
need-plusS`→ (tlam e) = plusS-S`→ (need-plusS`→ e)
need-plusS`→ (tapp e e₁) with need e | need-plusS`→ e
... | ∞ | IH = plusS`→-base
... | Z | IH = plusS`→-base
... | S r | plusS-S`→ IH = IH

⊢sub-∞' : ∀ {Γ i e A i'}
  → Γ ⊢ i # e ⦂ A
  → plusS`→ i
  → plusS`→∞A i' A
  → Γ ⊢ i' # e ⦂ A
⊢sub-∞' ⊢e plusS`→-base plusS`→-base∞A = ⊢sub ⊢e ¬Z-∞
⊢sub-∞' ⊢e plusS`→-base (plusS-S`→∞A ps') = ⊢sub ⊢e ¬Z-S
⊢sub-∞' (⊢lam-n ⊢e) (plusS-S`→ ps) plusS`→-base∞A = ⊢lam-∞ (⊢sub-∞' ⊢e ps plusS`→-base∞A)
⊢sub-∞' (⊢lam-n ⊢e) (plusS-S`→ ps) (plusS-S`→∞A ps') = ⊢lam-n (⊢sub-∞' ⊢e ps ps')
⊢sub-∞' (⊢app₂ ⊢e ⊢e₁) (plusS-S`→ ps) plusS`→-base∞A = ⊢app₂ (⊢sub-∞' ⊢e (plusS-S`→ (plusS-S`→ ps)) (plusS-S`→∞A plusS`→-base∞A)) ⊢e₁
⊢sub-∞' (⊢app₂ ⊢e ⊢e₁) (plusS-S`→ ps) (plusS-S`→∞A ps') = ⊢app₂ (⊢sub-∞' ⊢e (plusS-S`→ (plusS-S`→ ps)) (plusS-S`→∞A (plusS-S`→∞A ps'))) ⊢e₁
⊢sub-∞' (⊢sub ⊢e x) (plusS-S`→ ps) plusS`→-base∞A = ⊢sub ⊢e ¬Z-∞
⊢sub-∞' (⊢sub ⊢e x) (plusS-S`→ ps) (plusS-S`→∞A ps') = ⊢sub ⊢e ¬Z-S

⊢sub-∞ : ∀ {Γ j e A}
  → Γ ⊢ j # e ⦂ A
  → plusS`→ j
  → Γ ⊢ ∞ # e ⦂ A
⊢sub-∞ ⊢e ps = ⊢sub-∞' ⊢e ps plusS`→-base∞A

----------------------------------------------------------------------
--+                                                                +--
--+                     Strong Annotatability                      +--
--+                                                                +--
----------------------------------------------------------------------

annotatability : ∀ {Γ e A e'}
  → Γ ⊢1 e ⦂ A ⟶ e'
  → Γ ⊢ (need e) # e' ⦂ A
annotatability e-int = ⊢int
annotatability (e-var x) = ⊢var x
annotatability (e-lam ⊢e) = ⊢lam-n (annotatability ⊢e)
annotatability (e-app1 {e₁ = e₁} {e₂ = e₂} (inj₁ x) ⊢e₁ ⊢e₂) with need e₁ | annotatability ⊢e₁ | annotatability ⊢e₂
... | Z | ⊢e₁' | ⊢e₂' = ⊢app₁ ⊢e₁' (⊢sub-∞ ⊢e₂' (need-plusS`→ e₂))
annotatability (e-app1 {e₁ = e₁} {e₂ = e₂} (inj₂ y) ⊢e₁ ⊢e₂) with need e₁ | need-plusS`→ e₁
                                                              | need e₂ | need-plusS`→ e₂
                                                              | annotatability ⊢e₁ | annotatability ⊢e₂
... | Z | r1S | Z | r2S | ⊢e₁' | ⊢e₂' = ⊢app₁ ⊢e₁' (⊢sub ⊢e₂' ¬Z-∞)
... | S r1 | r1S | Z | r2S | ⊢e₁' | ⊢e₂' = ⊢app₂ ⊢e₁' ⊢e₂'
annotatability (e-app2 {e₁ = e₁} {e₂ = e₂} eq1 eq2 ⊢e₁ ⊢e₂) with need e₁ | need-plusS`→ e₁
                                                            | need e₂ | need-plusS`→ e₂
                                                            | annotatability ⊢e₁ | annotatability ⊢e₂
... | S r1 | r1S | S r2 | r2S | ⊢e₁' | ⊢e₂' = ⊢app₂ ⊢e₁' (⊢ann (⊢sub-∞ ⊢e₂' r2S))

annotatability' : ∀ {Γ e A e'}
  → Γ ⊢1 e ⦂ A ⟶ e'
  → Γ ⊢ Z # (e' ⦂ A) ⦂ A
annotatability' {e = e} ⊢e = ⊢ann (⊢sub-∞ (annotatability ⊢e) (need-plusS`→ e))  

----------------------------------------------------------------------
--+                                                                +--
--+                      Weak Annotatability                       +--
--+                                                                +--
----------------------------------------------------------------------

∥_∥ : Term → TTerm
∥ lit x ∥ = tlit x
∥ ` x ∥ = tvar x
∥ ƛ e ∥ = tlam (∥ e ∥)
∥ e₁ · e₂ ∥ = tapp ∥ e₁ ∥ ∥ e₂ ∥
∥ e ⦂ A ∥ = ∥ e ∥

data Complete (Γ : Env) (e : TTerm) (A : Type) : Set where

  ok : ∀ {e'}
    → (eq : ∥ e' ∥ ≡ e)
    → (⊢e : Γ ⊢ Z # e' ⦂ A)
    → Complete Γ e A

complete : ∀ {Γ e A}
  → Γ ⊢ e ⦂ A
  → Complete Γ e A
complete ⊢n = ok refl ⊢int
complete (⊢` x) = ok refl (⊢var x)
complete (⊢ƛ ⊢e) with complete ⊢e
... | ok eq ⊢e₁ = ok (cong tlam eq) (⊢ann (⊢lam-∞ (⊢sub ⊢e₁ ¬Z-∞)))
complete (⊢· ⊢e₁ ⊢e₂) with complete ⊢e₁ | complete ⊢e₂
... | ok eq₁ ⊢e₁' | ok eq₂ ⊢e₂' = ok (cong₂ tapp eq₁ eq₂) (⊢app₁ ⊢e₁' (⊢sub ⊢e₂' ¬Z-∞))

----------------------------------------------------------------------
--+                                                                +--
--+                    Alternative Elaboration                     +--
--+                                                                +--
----------------------------------------------------------------------

infix 3 _⊢2_⦂_⟶_
data _⊢2_⦂_⟶_ : Env → TTerm → Type → Term → Set where

  e-int : ∀ {Γ n}
    → Γ ⊢2 (tlit n) ⦂ Int ⟶ (lit n)

  e-var : ∀ {Γ x A}
    → Γ ∋ x ⦂ A
    → Γ ⊢2 (tvar x) ⦂ A ⟶ (` x)

  e-lam : ∀ {Γ e A B e'}
    → Γ , A ⊢2 e ⦂ B ⟶ e'
    → Γ ⊢2 tlam e ⦂ A `→ B ⟶ (ƛ e')

  e-app1 : ∀ {Γ e₁ e₂ A B e₁' e₂'}
    → need e₁ ≡ Z ⊎ need e₂ ≡ Z
    → Γ ⊢2 e₁ ⦂ A `→ B ⟶ e₁'
    → Γ ⊢2 e₂ ⦂ A ⟶ e₂'
    → Γ ⊢2 tapp e₁ e₂ ⦂ B ⟶ e₁' · e₂'

  e-app3 : ∀ {Γ e₁ e₂ A B e₁' e₂' m n}
    → need e₂ ≡ S n
    → need e₁ ≡ S m
    → Γ ⊢2 e₁ ⦂ A `→ B ⟶ e₁'
    → Γ ⊢2 e₂ ⦂ A ⟶ e₂'
    → Γ ⊢2 tapp e₁ e₂ ⦂ B ⟶ (e₁' ⦂ A `→ B) · e₂'

annotatability2 : ∀ {Γ e A e'}
  → Γ ⊢2 e ⦂ A ⟶ e'
  → Γ ⊢ (need e) # e' ⦂ A
annotatability2 e-int = ⊢int
annotatability2 (e-var x) = ⊢var x
annotatability2 (e-lam ⊢e) = ⊢lam-n (annotatability2 ⊢e)
annotatability2 (e-app1 {e₁ = e₁} {e₂ = e₂} (inj₁ x) ⊢e₁ ⊢e₂) with need e₁ | annotatability2 ⊢e₁ | annotatability2 ⊢e₂
... | Z | ⊢e₁' | ⊢e₂' = ⊢app₁ ⊢e₁' (⊢sub-∞ ⊢e₂' (need-plusS`→ e₂))
annotatability2 (e-app1 {e₁ = e₁} {e₂ = e₂} (inj₂ y) ⊢e₁ ⊢e₂) with need e₁ | need-plusS`→ e₁
                                                              | need e₂ | need-plusS`→ e₂
                                                              | annotatability2 ⊢e₁ | annotatability2 ⊢e₂
... | Z | r1S | Z | r2S | ⊢e₁' | ⊢e₂' = ⊢app₁ ⊢e₁' (⊢sub ⊢e₂' ¬Z-∞)
... | S r1 | r1S | Z | r2S | ⊢e₁' | ⊢e₂' = ⊢app₂ ⊢e₁' ⊢e₂'
annotatability2 (e-app3 {e₁ = e₁} {e₂ = e₂} eq1 eq2 ⊢e₁ ⊢e₂) with need e₁ | need-plusS`→ e₁
                                                            | need e₂ | need-plusS`→ e₂
                                                            | annotatability2 ⊢e₁ | annotatability2 ⊢e₂
... | S r1 | r1S | S r2 | r2S | ⊢e₁' | ⊢e₂' = ⊢sub' (⊢app₁ (⊢ann (⊢sub-∞ ⊢e₁' r1S)) (⊢sub-∞ ⊢e₂' r2S))

annotatability2' : ∀ {Γ e A e'}
  → Γ ⊢2 e ⦂ A ⟶ e'
  → Γ ⊢ Z # (e' ⦂ A) ⦂ A
annotatability2' {e = e} ⊢e = ⊢ann (⊢sub-∞ (annotatability2 ⊢e) (need-plusS`→ e))


----------------------------------------------------------------------
--+                                                                +--
--+                    Alternative Elaboration (Both)              +--
--+                                                                +--
----------------------------------------------------------------------

infix 3 _⊢3_⦂_⟶_
data _⊢3_⦂_⟶_ : Env → TTerm → Type → Term → Set where

  e-int : ∀ {Γ n}
    → Γ ⊢3 (tlit n) ⦂ Int ⟶ (lit n)

  e-var : ∀ {Γ x A}
    → Γ ∋ x ⦂ A
    → Γ ⊢3 (tvar x) ⦂ A ⟶ (` x)

  e-lam : ∀ {Γ e A B e'}
    → Γ , A ⊢3 e ⦂ B ⟶ e'
    → Γ ⊢3 tlam e ⦂ A `→ B ⟶ (ƛ e')

  e-app1 : ∀ {Γ e₁ e₂ A B e₁' e₂'}
    → need e₁ ≡ Z ⊎ need e₂ ≡ Z
    → Γ ⊢3 e₁ ⦂ A `→ B ⟶ e₁'
    → Γ ⊢3 e₂ ⦂ A ⟶ e₂'
    → Γ ⊢3 tapp e₁ e₂ ⦂ B ⟶ e₁' · e₂'

  e-app2 : ∀ {Γ e₁ e₂ A B e₁' e₂' m n}
    → need e₂ ≡ S n
    → need e₁ ≡ S m
    → Γ ⊢3 e₁ ⦂ A `→ B ⟶ e₁'
    → Γ ⊢3 e₂ ⦂ A ⟶ e₂'
    → Γ ⊢3 tapp e₁ e₂ ⦂ B ⟶ e₁' · (e₂' ⦂ A)

  e-app3 : ∀ {Γ e₁ e₂ A B e₁' e₂' m n}
    → need e₂ ≡ S n
    → need e₁ ≡ S m
    → Γ ⊢3 e₁ ⦂ A `→ B ⟶ e₁'
    → Γ ⊢3 e₂ ⦂ A ⟶ e₂'
    → Γ ⊢3 tapp e₁ e₂ ⦂ B ⟶ (e₁' ⦂ A `→ B) · e₂'

annotatability3 : ∀ {Γ e A e'}
  → Γ ⊢3 e ⦂ A ⟶ e'
  → Γ ⊢ (need e) # e' ⦂ A
annotatability3 e-int = ⊢int
annotatability3 (e-var x) = ⊢var x
annotatability3 (e-lam ⊢e) = ⊢lam-n (annotatability3 ⊢e)
annotatability3 (e-app1 {e₁ = e₁} {e₂ = e₂} (inj₁ x) ⊢e₁ ⊢e₂) with need e₁ | annotatability3 ⊢e₁ | annotatability3 ⊢e₂
... | Z | ⊢e₁' | ⊢e₂' = ⊢app₁ ⊢e₁' (⊢sub-∞ ⊢e₂' (need-plusS`→ e₂))
annotatability3 (e-app1 {e₁ = e₁} {e₂ = e₂} (inj₂ y) ⊢e₁ ⊢e₂) with need e₁ | need-plusS`→ e₁
                                                              | need e₂ | need-plusS`→ e₂
                                                              | annotatability3 ⊢e₁ | annotatability3 ⊢e₂
... | Z | r1S | Z | r2S | ⊢e₁' | ⊢e₂' = ⊢app₁ ⊢e₁' (⊢sub ⊢e₂' ¬Z-∞)
... | S r1 | r1S | Z | r2S | ⊢e₁' | ⊢e₂' = ⊢app₂ ⊢e₁' ⊢e₂'
annotatability3 (e-app2 {e₁ = e₁} {e₂ = e₂} eq1 eq2 ⊢e₁ ⊢e₂) with need e₁ | need-plusS`→ e₁
                                                            | need e₂ | need-plusS`→ e₂
                                                            | annotatability3 ⊢e₁ | annotatability3 ⊢e₂
... | S r1 | r1S | S r2 | r2S | ⊢e₁' | ⊢e₂' = ⊢app₂ ⊢e₁' (⊢ann (⊢sub-∞ ⊢e₂' r2S))
annotatability3 (e-app3 {e₁ = e₁} {e₂ = e₂} eq1 eq2 ⊢e₁ ⊢e₂) with need e₁ | need-plusS`→ e₁
                                                            | need e₂ | need-plusS`→ e₂
                                                            | annotatability3 ⊢e₁ | annotatability3 ⊢e₂
... | S r1 | r1S | S r2 | r2S | ⊢e₁' | ⊢e₂' = ⊢sub' (⊢app₁ (⊢ann (⊢sub-∞ ⊢e₁' r1S)) (⊢sub-∞ ⊢e₂' r2S))

annotatability3' : ∀ {Γ e A e'}
  → Γ ⊢3 e ⦂ A ⟶ e'
  → Γ ⊢ Z # (e' ⦂ A) ⦂ A
annotatability3' {e = e} ⊢e = ⊢ann (⊢sub-∞ (annotatability3 ⊢e) (need-plusS`→ e))  

