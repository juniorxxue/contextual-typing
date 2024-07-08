module Record.Decl.Properties where

open import Record.Prelude
open import Record.Common
open import Record.Decl
open import Record.Properties

----------------------------------------------------------------------
--+                                                                +--
--+                           Weakening                            +--
--+                                                                +--
----------------------------------------------------------------------

rs≢rnil-↑r : ∀ {rs n}
  → rs ≢ rnil
  → rs ↑r n ≢ rnil
rs≢rnil-↑r {rnil} neq = neq
rs≢rnil-↑r {r⟦ x ↦ x₁ ⟧ rs} neq = λ ()

rs≢rnil-↓r : ∀ {rs n}
  → rs ≢ rnil
  → rs ↓r n ≢ rnil
rs≢rnil-↓r {rnil} neq = neq
rs≢rnil-↓r {r⟦ x ↦ x₁ ⟧ rs} neq = λ ()

⊢d-weaken : ∀ {Γ cc e A B n}
  → Γ ⊢d cc # e ⦂ B
  → (n≤l : n ≤ length Γ)
  → Γ ↑ n [ n≤l ] A ⊢d cc # (e ↑ n) ⦂ B

⊢r-weaken : ∀ {Γ rs A B n}
  → Γ ⊢r Z # rs ⦂ B
  → (n≤l : n ≤ length Γ)
  → Γ ↑ n [ n≤l ] A ⊢r Z # (rs ↑r n) ⦂ B

⊢d-weaken ⊢d-c n≤l = ⊢d-c
⊢d-weaken (⊢d-var x∈Γ) n≤l = ⊢d-var (∋-weaken x∈Γ n≤l)
⊢d-weaken (⊢d-lam₁ ⊢e) n≤l = ⊢d-lam₁ (⊢d-weaken ⊢e (s≤s n≤l))
⊢d-weaken (⊢d-lam₂ ⊢e) n≤l = ⊢d-lam₂ (⊢d-weaken ⊢e (s≤s n≤l))
⊢d-weaken (⊢d-app⇐ ⊢f ⊢e) n≤l = ⊢d-app⇐ (⊢d-weaken ⊢f n≤l) (⊢d-weaken ⊢e n≤l)
⊢d-weaken (⊢d-app⇒ ⊢f ⊢e) n≤l = ⊢d-app⇒ (⊢d-weaken ⊢f n≤l) (⊢d-weaken ⊢e n≤l)
⊢d-weaken (⊢d-ann ⊢e) n≤l = ⊢d-ann (⊢d-weaken ⊢e n≤l)
⊢d-weaken (⊢d-sub ⊢e A≤B neq) n≤l = ⊢d-sub (⊢d-weaken ⊢e n≤l) A≤B neq
⊢d-weaken (⊢d-rcd ⊢e) n≤l = ⊢d-rcd (⊢r-weaken ⊢e n≤l)
⊢d-weaken (⊢d-prj ⊢e) n≤l = ⊢d-prj (⊢d-weaken ⊢e n≤l)

⊢r-weaken ⊢r-nil n≤l = ⊢r-nil
⊢r-weaken (⊢r-one x) n≤l = ⊢r-one (⊢d-weaken x n≤l)
⊢r-weaken (⊢r-cons x ⊢rs nnil) n≤l = ⊢r-cons (⊢d-weaken x n≤l) (⊢r-weaken ⊢rs n≤l) (rs≢rnil-↑r nnil)

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
  
⊢r-strengthen : ∀ {Γ rs A n}
  → Γ ⊢r Z # rs ⦂ A
  → rs ~↑r~ n
  → (n≤l : n ≤ length Γ)
  → Γ ↓ n [ n≤l ] ⊢r Z # rs ↓r n ⦂ A
  
⊢d-strengthen ⊢d-c sd n≤l = ⊢d-c
⊢d-strengthen (⊢d-var x∈Γ) sd n≤l = ⊢d-var (∋-strenghthen x∈Γ sd n≤l)
⊢d-strengthen (⊢d-lam₁ ⊢e) (sd-lam sd) n≤l = ⊢d-lam₁ (⊢d-strengthen ⊢e sd (s≤s n≤l))
⊢d-strengthen (⊢d-lam₂ ⊢e) (sd-lam sd) n≤l = ⊢d-lam₂ (⊢d-strengthen ⊢e sd (s≤s n≤l))
⊢d-strengthen (⊢d-app⇐ ⊢f ⊢e) (sd-app sd sd₁) n≤l = ⊢d-app⇐ (⊢d-strengthen ⊢f sd n≤l) (⊢d-strengthen ⊢e sd₁ n≤l)
⊢d-strengthen (⊢d-app⇒ ⊢f ⊢e) (sd-app sd sd₁) n≤l = ⊢d-app⇒ (⊢d-strengthen ⊢f sd n≤l) (⊢d-strengthen ⊢e sd₁ n≤l)
⊢d-strengthen (⊢d-ann ⊢e) (sd-ann sd) n≤l = ⊢d-ann (⊢d-strengthen ⊢e sd n≤l)
⊢d-strengthen (⊢d-sub ⊢e A≤B neq) sd n≤l = ⊢d-sub (⊢d-strengthen ⊢e sd n≤l) A≤B neq
⊢d-strengthen (⊢d-rcd ⊢e) (sd-rcd x) n≤l = ⊢d-rcd (⊢r-strengthen ⊢e x n≤l)
⊢d-strengthen (⊢d-prj ⊢e) (sd-prj sd) n≤l = ⊢d-prj (⊢d-strengthen ⊢e sd n≤l)

⊢r-strengthen ⊢r-nil rs~n n≤l = ⊢r-nil
⊢r-strengthen (⊢r-one x) (sdr-cons x₁ rs~n) n≤l = ⊢r-one (⊢d-strengthen x x₁ n≤l)
⊢r-strengthen (⊢r-cons x ⊢rs nnil) (sdr-cons x₁ rs~n) n≤l = ⊢r-cons (⊢d-strengthen x x₁ n≤l) (⊢r-strengthen ⊢rs rs~n n≤l) (rs≢rnil-↓r nnil)

⊢d-strengthen-0 : ∀ {Γ cc e A B}
  → Γ , A ⊢d cc # e ↑ 0 ⦂ B
  → Γ ⊢d cc # e ⦂ B
⊢d-strengthen-0 {e = e} ⊢e with ⊢d-strengthen ⊢e ↑-shifted z≤n
... | ind-e rewrite ↑-↓-id e 0 = ind-e

----------------------------------------------------------------------
--+                                                                +--
--+                           Subsumption                          +--
--+                                                                +--
----------------------------------------------------------------------
{- no longer hold
⊢d-sub' : ∀ {Γ e A B i}
  → Γ ⊢d Z # e ⦂ B
  → B ≤d A
  → Γ ⊢d i # e ⦂ A
⊢d-sub' {i = Z} ⊢e B≤A = {!!}
⊢d-sub' {i = ∞} ⊢e B≤A = ⊢d-sub ⊢e B≤A (λ ())
⊢d-sub' {i = S i} ⊢e B≤A = ⊢d-sub ⊢e B≤A (λ ())
-}
