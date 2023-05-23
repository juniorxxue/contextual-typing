module Counter.Dec.Properties where

open import Counter.Prelude
open import Counter.Common
open import Counter.Dec
open import Counter.Properties

----------------------------------------------------------------------
--+                                                                +--
--+                           Weakening                            +--
--+                                                                +--
----------------------------------------------------------------------

⊢d-weaken : ∀ {Γ cc e A B n}
  → Γ ⊢d cc ╏ e ⦂ B
  → (n≤l : n ≤ length Γ)
  → Γ ↑ n [ n≤l ] A ⊢d cc ╏ (e ↑ n) ⦂ B
⊢d-weaken ⊢d-int n≤l = ⊢d-int
⊢d-weaken (⊢d-var x∈Γ) n≤l = ⊢d-var (∋-weaken x∈Γ n≤l)
⊢d-weaken (⊢d-lam₁ ⊢e) n≤l = ⊢d-lam₁ (⊢d-weaken ⊢e (s≤s n≤l))
⊢d-weaken (⊢d-lam₂ ⊢e) n≤l = ⊢d-lam₂ (⊢d-weaken ⊢e (s≤s n≤l))
⊢d-weaken (⊢d-app₁ ⊢f ⊢e) n≤l = ⊢d-app₁ (⊢d-weaken ⊢f n≤l) (⊢d-weaken ⊢e n≤l)
⊢d-weaken (⊢d-app₂ ⊢f ⊢e) n≤l = ⊢d-app₂ (⊢d-weaken ⊢f n≤l) (⊢d-weaken ⊢e n≤l)
⊢d-weaken (⊢d-app₃ ⊢f ⊢e) n≤l = ⊢d-app₃ (⊢d-weaken ⊢f n≤l) (⊢d-weaken ⊢e n≤l)
⊢d-weaken (⊢d-ann ⊢e) n≤l = ⊢d-ann (⊢d-weaken ⊢e n≤l)
⊢d-weaken (⊢d-sub ⊢e A≤B) n≤l = ⊢d-sub (⊢d-weaken ⊢e n≤l) A≤B

⊢d-weaken-0 : ∀ {Γ cc e A B}
  → Γ ⊢d cc ╏ e ⦂ B
  → Γ , A ⊢d cc ╏ e ↑ 0 ⦂ B
⊢d-weaken-0 ⊢e = ⊢d-weaken ⊢e z≤n  

----------------------------------------------------------------------
--+                                                                +--
--+                         Strengthening                          +--
--+                                                                +--
----------------------------------------------------------------------

⊢d-strengthen : ∀ {Γ cc e A n}
  → Γ ⊢d cc ╏ e ⦂ A
  → e ~↑~ n
  → (n≤l : n ≤ length Γ)
  → Γ ↓ n [ n≤l ] ⊢d cc ╏ e ↓ n ⦂ A
⊢d-strengthen ⊢d-int sd n≤l = ⊢d-int
⊢d-strengthen (⊢d-var x∈Γ) sd n≤l = ⊢d-var (∋-strenghthen x∈Γ sd n≤l)
⊢d-strengthen (⊢d-lam₁ ⊢e) (sd-lam sd) n≤l = ⊢d-lam₁ (⊢d-strengthen ⊢e sd (s≤s n≤l))
⊢d-strengthen (⊢d-lam₂ ⊢e) (sd-lam sd) n≤l = ⊢d-lam₂ (⊢d-strengthen ⊢e sd (s≤s n≤l))
⊢d-strengthen (⊢d-app₁ ⊢f ⊢e) (sd-app sd sd₁) n≤l = ⊢d-app₁ (⊢d-strengthen ⊢f sd n≤l) (⊢d-strengthen ⊢e sd₁ n≤l)
⊢d-strengthen (⊢d-app₂ ⊢f ⊢e) (sd-app sd sd₁) n≤l = ⊢d-app₂ (⊢d-strengthen ⊢f sd n≤l) (⊢d-strengthen ⊢e sd₁ n≤l)
⊢d-strengthen (⊢d-app₃ ⊢f ⊢e) (sd-app sd sd₁) n≤l = ⊢d-app₃ (⊢d-strengthen ⊢f sd n≤l) (⊢d-strengthen ⊢e sd₁ n≤l)
⊢d-strengthen (⊢d-ann ⊢e) (sd-ann sd) n≤l = ⊢d-ann (⊢d-strengthen ⊢e sd n≤l)
⊢d-strengthen (⊢d-sub ⊢e A≤B) sd n≤l = ⊢d-sub (⊢d-strengthen ⊢e sd n≤l) A≤B

⊢d-strengthen-0 : ∀ {Γ cc e A B}
  → Γ , A ⊢d cc ╏ e ↑ 0 ⦂ B
  → Γ ⊢d cc ╏ e ⦂ B
⊢d-strengthen-0 {e = e} ⊢e with ⊢d-strengthen ⊢e ↑-shifted z≤n
... | ind-e rewrite ↑-↓-id e 0 = ind-e
