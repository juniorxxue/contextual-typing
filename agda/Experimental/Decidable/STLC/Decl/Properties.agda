module STLC.Decl.Properties where

open import STLC.Prelude
open import STLC.Common
open import STLC.Decl
open import STLC.Properties

----------------------------------------------------------------------
--+                                                                +--
--+                           Weakening                            +--
--+                                                                +--
----------------------------------------------------------------------

⊢d-weaken : ∀ {Γ j e A B n}
  → Γ ⊢d j # e ⦂ B
  → (n≤l : n ≤ length Γ)
  → Γ ↑ n [ n≤l ] A ⊢d j # (e ↑ n) ⦂ B
⊢d-weaken ⊢d-int n≤l = ⊢d-int
⊢d-weaken (⊢d-var x∈Γ) n≤l = ⊢d-var (∋-weaken x∈Γ n≤l)
⊢d-weaken (⊢d-lam-n ⊢e) n≤l = ⊢d-lam-n (⊢d-weaken ⊢e (s≤s n≤l))
⊢d-weaken (⊢d-lam-∞ ⊢e) n≤l = ⊢d-lam-∞ (⊢d-weaken ⊢e (s≤s n≤l))
⊢d-weaken (⊢d-app₁ ⊢f ⊢e) n≤l = ⊢d-app₁ (⊢d-weaken ⊢f n≤l) (⊢d-weaken ⊢e n≤l)
⊢d-weaken (⊢d-app₂ ⊢f ⊢e) n≤l = ⊢d-app₂ (⊢d-weaken ⊢f n≤l) (⊢d-weaken ⊢e n≤l)
⊢d-weaken (⊢d-ann ⊢e) n≤l = ⊢d-ann (⊢d-weaken ⊢e n≤l)
⊢d-weaken (⊢d-sub ⊢e j≢Z) n≤l = ⊢d-sub (⊢d-weaken ⊢e n≤l) j≢Z

⊢d-weaken-0 : ∀ {Γ cc e A B}
  → Γ ⊢d cc # e ⦂ B
  → Γ , A ⊢d cc # e ↑ 0 ⦂ B
⊢d-weaken-0 ⊢e = ⊢d-weaken ⊢e z≤n  

----------------------------------------------------------------------
--+                                                                +--
--+                         Strengthening                          +--
--+                                                                +--
----------------------------------------------------------------------

⊢d-strengthen : ∀ {Γ cc e A n}
  → Γ ⊢d cc # e ⦂ A
  → e ~↑~ n
  → (n≤l : n ≤ length Γ)
  → Γ ↓ n [ n≤l ] ⊢d cc # e ↓ n ⦂ A
⊢d-strengthen ⊢d-int sd n≤l = ⊢d-int
⊢d-strengthen (⊢d-var x∈Γ) sd n≤l = ⊢d-var (∋-strenghthen x∈Γ sd n≤l)
⊢d-strengthen (⊢d-lam-∞ ⊢e) (sd-lam sd) n≤l = ⊢d-lam-∞ (⊢d-strengthen ⊢e sd (s≤s n≤l))
⊢d-strengthen (⊢d-lam-n ⊢e) (sd-lam sd) n≤l = ⊢d-lam-n (⊢d-strengthen ⊢e sd (s≤s n≤l))
⊢d-strengthen (⊢d-app₁ ⊢f ⊢e) (sd-app sd sd₁) n≤l = ⊢d-app₁ (⊢d-strengthen ⊢f sd n≤l) (⊢d-strengthen ⊢e sd₁ n≤l)
⊢d-strengthen (⊢d-app₂ ⊢f ⊢e) (sd-app sd sd₁) n≤l = ⊢d-app₂ (⊢d-strengthen ⊢f sd n≤l) (⊢d-strengthen ⊢e sd₁ n≤l)
⊢d-strengthen (⊢d-ann ⊢e) (sd-ann sd) n≤l = ⊢d-ann (⊢d-strengthen ⊢e sd n≤l)
⊢d-strengthen (⊢d-sub ⊢e j≢Z) sd n≤l = ⊢d-sub (⊢d-strengthen ⊢e sd n≤l) j≢Z

⊢d-strengthen-0 : ∀ {Γ cc e A B}
  → Γ , A ⊢d cc # e ↑ 0 ⦂ B
  → Γ ⊢d cc # e ⦂ B
⊢d-strengthen-0 {e = e} ⊢e with ⊢d-strengthen ⊢e ↑-shifted z≤n
... | ind-e rewrite ↑-↓-id e 0 = ind-e


----------------------------------------------------------------------
--+                                                                +--
--+                          Subsumptions                          +--
--+                                                                +--
----------------------------------------------------------------------

⊢d-sub' : ∀ {Γ e A j}
  → Γ ⊢d Z # e ⦂ A
  → Γ ⊢d j # e ⦂ A
⊢d-sub' {j = ∞} ⊢e = ⊢d-sub ⊢e (λ ())
⊢d-sub' {j = Z} ⊢e = ⊢e
⊢d-sub' {j = S j} ⊢e = ⊢d-sub ⊢e (λ ())
