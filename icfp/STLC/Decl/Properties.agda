module STLC.Decl.Properties where

open import STLC.Prelude
open import STLC.Common
open import STLC.Decl
open import STLC.Properties

----------------------------------------------------------------------
--+                           Weakening                            +--
----------------------------------------------------------------------

⊢weaken : ∀ {Γ j e A B n}
  → Γ ⊢ j # e ⦂ B
  → (n≤l : n ≤ length Γ)
  → Γ ↑ n [ n≤l ] A ⊢ j # (e ↑ n) ⦂ B
⊢weaken ⊢int n≤l = ⊢int
⊢weaken (⊢var x∈Γ) n≤l = ⊢var (∋-weaken x∈Γ n≤l)
⊢weaken (⊢lam-n ⊢e) n≤l = ⊢lam-n (⊢weaken ⊢e (s≤s n≤l))
⊢weaken (⊢lam-∞ ⊢e) n≤l = ⊢lam-∞ (⊢weaken ⊢e (s≤s n≤l))
⊢weaken (⊢app₁ ⊢f ⊢e) n≤l = ⊢app₁ (⊢weaken ⊢f n≤l) (⊢weaken ⊢e n≤l)
⊢weaken (⊢app₂ ⊢f ⊢e) n≤l = ⊢app₂ (⊢weaken ⊢f n≤l) (⊢weaken ⊢e n≤l)
⊢weaken (⊢ann ⊢e) n≤l = ⊢ann (⊢weaken ⊢e n≤l)
⊢weaken (⊢sub ⊢e j≢Z) n≤l = ⊢sub (⊢weaken ⊢e n≤l) j≢Z

⊢weaken-0 : ∀ {Γ j e A B}
  → Γ ⊢ j # e ⦂ B
  → Γ , A ⊢ j # e ↑ 0 ⦂ B
⊢weaken-0 ⊢e = ⊢weaken ⊢e z≤n  

----------------------------------------------------------------------
--+                         Strengthening                          +--
----------------------------------------------------------------------

⊢strengthen : ∀ {Γ j e A n}
  → Γ ⊢ j # e ⦂ A
  → e ~↑~ n -- shifted
  → (n≤l : n ≤ length Γ)
  → Γ ↓ n [ n≤l ] ⊢ j # e ↓ n ⦂ A
⊢strengthen ⊢int sd n≤l = ⊢int
⊢strengthen (⊢var x∈Γ) sd n≤l = ⊢var (∋-strenghthen x∈Γ sd n≤l)
⊢strengthen (⊢lam-∞ ⊢e) (sd-lam sd) n≤l = ⊢lam-∞ (⊢strengthen ⊢e sd (s≤s n≤l))
⊢strengthen (⊢lam-n ⊢e) (sd-lam sd) n≤l = ⊢lam-n (⊢strengthen ⊢e sd (s≤s n≤l))
⊢strengthen (⊢app₁ ⊢f ⊢e) (sd-app sd sd₁) n≤l = ⊢app₁ (⊢strengthen ⊢f sd n≤l) (⊢strengthen ⊢e sd₁ n≤l)
⊢strengthen (⊢app₂ ⊢f ⊢e) (sd-app sd sd₁) n≤l = ⊢app₂ (⊢strengthen ⊢f sd n≤l) (⊢strengthen ⊢e sd₁ n≤l)
⊢strengthen (⊢ann ⊢e) (sd-ann sd) n≤l = ⊢ann (⊢strengthen ⊢e sd n≤l)
⊢strengthen (⊢sub ⊢e j≢Z) sd n≤l = ⊢sub (⊢strengthen ⊢e sd n≤l) j≢Z

⊢strengthen-0 : ∀ {Γ j e A B}
  → Γ , A ⊢ j # e ↑ 0 ⦂ B
  → Γ ⊢ j # e ⦂ B
⊢strengthen-0 {e = e} ⊢e with ⊢strengthen ⊢e ↑-shifted z≤n
... | ind-e rewrite ↑-↓-id e 0 = ind-e

----------------------------------------------------------------------
--+                          Subsumptions                          +--
----------------------------------------------------------------------

-- a general subsumption rule can be derived
⊢sub' : ∀ {Γ e A j}
  → Γ ⊢ Z # e ⦂ A
  → Γ ⊢ j # e ⦂ A
⊢sub' {j = ∞} ⊢e = ⊢sub ⊢e ¬Z-∞
⊢sub' {j = Z} ⊢e = ⊢e
⊢sub' {j = S j} ⊢e = ⊢sub ⊢e ¬Z-S
