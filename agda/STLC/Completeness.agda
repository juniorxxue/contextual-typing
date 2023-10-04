module STLC.Completeness where

open import STLC.Prelude hiding (_≤?_) renaming (_≤_ to _≤n_)
open import STLC.Common
open import STLC.Decl
open import STLC.Algo
open import STLC.Algo.Properties

----------------------------------------------------------------------
--+                                                                +--
--+                          Subsumption                           +--
--+                                                                +--
----------------------------------------------------------------------


----------------------------------------------------------------------
--+                                                                +--
--+                          Completeness                          +--
--+                                                                +--
----------------------------------------------------------------------

infix 4 _⊢r_#_⦂_

data _⊢r_#_⦂_ : Context → Counter → Term → Type → Set where

  RZ : ∀ {Γ A e}
    → Γ ⊢a □ ⇛ e ⇛ A
    → Γ ⊢r Z # e ⦂ A

  R∞ : ∀ {Γ A e}
    → Γ ⊢a τ A ⇛ e ⇛ A
    → Γ ⊢r ∞ # e ⦂ A

  RS : ∀ {Γ e j A B}
    → (∀ e' → Γ ⊢d Z # e' ⦂ A → Γ ⊢r j # (e · e') ⦂ B)
    → Γ ⊢r (S j) # e ⦂ (A ⇒ B)


⊢r-lam : ∀ {Γ e A B j}
  → Γ , A ⊢r j # e ⦂ B
  → Γ ⊢r S j # ƛ e ⦂ A ⇒ B
⊢r-lam (RZ x) = RS (λ e' x₁ → RZ (⊢a-app (⊢a-lam₂ {!!} x)))
⊢r-lam (R∞ x) = {!!}
⊢r-lam (RS x) = {!!}

⊢r-app : ∀ {Γ e e' A B j}
  → Γ ⊢r S j # e ⦂ A ⇒ B
  → Γ ⊢d Z # e' ⦂ A
  → Γ ⊢r j # (e · e') ⦂ B
⊢r-app {e' = e'} (RS x) ⊢2 = x e' ⊢2

complete : ∀ {Γ j e A}
  → Γ ⊢d j # e ⦂ A
  → Γ ⊢r j # e ⦂ A
  
complete ⊢d-int = RZ ⊢a-lit

complete (⊢d-var x) = RZ (⊢a-var x)
complete (⊢d-ann ⊢e) with complete ⊢e
... | R∞ ⊢a = RZ (⊢a-ann ⊢a)
complete (⊢d-lam-∞ ⊢e) with complete ⊢e
... | R∞ ⊢a = R∞ (⊢a-lam₁ ⊢a)
complete (⊢d-lam-n ⊢e) with complete ⊢e
... | ⊢r = RS (λ e' ⊢e' → ⊢r-app {!!} ⊢e')
-- RS (λ e' ⊢e' → {!!})
-- RS λ e' ⊢e' → complete (⊢d-app₂ (⊢d-lam-n ⊢e) ⊢e')
complete (⊢d-app₁ ⊢f ⊢e) with complete ⊢f | complete ⊢e
... | RZ ⊢f' | R∞ ⊢e' = RZ (⊢a-app (subsumption-0 ⊢f' (≈hole ⊢e' ≈□)))
complete (⊢d-app₂ {e₂ = e₂} ⊢f ⊢e) with complete ⊢f | complete ⊢e
... | RS ⊢f' | RZ ⊢e' = ⊢f' e₂ ⊢e
complete {j = ∞} (⊢d-sub ⊢e A~j) with complete ⊢e
... | RZ ⊢e' = R∞ (subsumption-0 ⊢e' ≈τ)
complete {j = Z} (⊢d-sub ⊢e A~j) with complete ⊢e
... | RZ ⊢e' = RZ ⊢e'
complete {j = S j} (⊢d-sub ⊢e (~S A~j)) with complete ⊢e
... | RZ ⊢e' = RS (λ e' ⊢e'' → {!!})


complete' : ∀ {Γ j e A}
  → Γ ⊢d j # e ⦂ A
  → A ~ j 
  → Γ ⊢r j # e ⦂ A
complete' {j = ∞} ⊢e ~∞ = R∞ {!!}

complete' {j = Z} ⊢d-int ~0 = RZ {!!}
complete' {j = Z} (⊢d-var x) ~0 = RZ {!!}
complete' {j = Z} (⊢d-ann ⊢e) ~0 = RZ {!!}
complete' {j = Z} (⊢d-app₁ ⊢e ⊢e₁) ~0 = RZ {!!}
complete' {j = Z} (⊢d-app₂ ⊢e ⊢e₁) ~0 = RZ {!!}
complete' {j = Z} (⊢d-sub ⊢e x) ~0 = RZ {!!}

complete' {j = S j} ⊢e (~S A~j) = RS (λ e' x → complete' (⊢d-app₂ ⊢e x) A~j)
