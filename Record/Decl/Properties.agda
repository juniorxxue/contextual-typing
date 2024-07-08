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

⊢weaken : ∀ {Γ i e A B n}
  → Γ ⊢ i # e ⦂ B
  → (n≤l : n ≤ length Γ)
  → Γ ↑ n [ n≤l ] A ⊢ i # (e ↑ n) ⦂ B

⊢r-weaken : ∀ {Γ rs A B n}
  → Γ ⊢r ♭ Z # rs ⦂ B
  → (n≤l : n ≤ length Γ)
  → Γ ↑ n [ n≤l ] A ⊢r ♭ Z # (rs ↑r n) ⦂ B

⊢weaken ⊢c n≤l = ⊢c
⊢weaken (⊢var x∈Γ) n≤l = ⊢var (∋-weaken x∈Γ n≤l)
⊢weaken (⊢lam₁ ⊢e) n≤l = ⊢lam₁ (⊢weaken ⊢e (s≤s n≤l))
⊢weaken (⊢lam₂ ⊢e) n≤l = ⊢lam₂ (⊢weaken ⊢e (s≤s n≤l))
⊢weaken (⊢app⇐ ⊢f ⊢e) n≤l = ⊢app⇐ (⊢weaken ⊢f n≤l) (⊢weaken ⊢e n≤l)
⊢weaken (⊢app⇒ ⊢f ⊢e) n≤l = ⊢app⇒ (⊢weaken ⊢f n≤l) (⊢weaken ⊢e n≤l)
⊢weaken (⊢ann ⊢e) n≤l = ⊢ann (⊢weaken ⊢e n≤l)
⊢weaken (⊢sub ⊢e A≤B neq) n≤l = ⊢sub (⊢weaken ⊢e n≤l) A≤B neq
⊢weaken (⊢rcd ⊢e) n≤l = ⊢rcd (⊢r-weaken ⊢e n≤l)
⊢weaken (⊢prj ⊢e) n≤l = ⊢prj (⊢weaken ⊢e n≤l)

⊢r-weaken ⊢r-nil n≤l = ⊢r-nil
⊢r-weaken (⊢r-one x) n≤l = ⊢r-one (⊢weaken x n≤l)
⊢r-weaken (⊢r-cons x ⊢rs nnil) n≤l = ⊢r-cons (⊢weaken x n≤l) (⊢r-weaken ⊢rs n≤l) (rs≢rnil-↑r nnil)

⊢weaken-0 : ∀ {Γ cc e A B}
  → Γ ⊢ cc # e ⦂ B
  → Γ , A ⊢ cc # e ↑ 0 ⦂ B
⊢weaken-0 ⊢e = ⊢weaken ⊢e z≤n  

----------------------------------------------------------------------
--+                                                                +--
--+                         Strengthening                          +--
--+                                                                +--
----------------------------------------------------------------------

⊢strengthen : ∀ {Γ cc e A n}
  → Γ ⊢ cc # e ⦂ A
  → e ~↑~ n
  → (n≤l : n ≤ length Γ)
  → Γ ↓ n [ n≤l ] ⊢ cc # e ↓ n ⦂ A
  
⊢r-strengthen : ∀ {Γ rs A n}
  → Γ ⊢r ♭ Z # rs ⦂ A
  → rs ~↑r~ n
  → (n≤l : n ≤ length Γ)
  → Γ ↓ n [ n≤l ] ⊢r ♭ Z # rs ↓r n ⦂ A
  
⊢strengthen ⊢c sd n≤l = ⊢c
⊢strengthen (⊢var x∈Γ) sd n≤l = ⊢var (∋-strenghthen x∈Γ sd n≤l)
⊢strengthen (⊢lam₁ ⊢e) (sd-lam sd) n≤l = ⊢lam₁ (⊢strengthen ⊢e sd (s≤s n≤l))
⊢strengthen (⊢lam₂ ⊢e) (sd-lam sd) n≤l = ⊢lam₂ (⊢strengthen ⊢e sd (s≤s n≤l))
⊢strengthen (⊢app⇐ ⊢f ⊢e) (sd-app sd sd₁) n≤l = ⊢app⇐ (⊢strengthen ⊢f sd n≤l) (⊢strengthen ⊢e sd₁ n≤l)
⊢strengthen (⊢app⇒ ⊢f ⊢e) (sd-app sd sd₁) n≤l = ⊢app⇒ (⊢strengthen ⊢f sd n≤l) (⊢strengthen ⊢e sd₁ n≤l)
⊢strengthen (⊢ann ⊢e) (sd-ann sd) n≤l = ⊢ann (⊢strengthen ⊢e sd n≤l)
⊢strengthen (⊢sub ⊢e A≤B neq) sd n≤l = ⊢sub (⊢strengthen ⊢e sd n≤l) A≤B neq
⊢strengthen (⊢rcd ⊢e) (sd-rcd x) n≤l = ⊢rcd (⊢r-strengthen ⊢e x n≤l)
⊢strengthen (⊢prj ⊢e) (sd-prj sd) n≤l = ⊢prj (⊢strengthen ⊢e sd n≤l)

⊢r-strengthen ⊢r-nil rs~n n≤l = ⊢r-nil
⊢r-strengthen (⊢r-one x) (sdr-cons x₁ rs~n) n≤l = ⊢r-one (⊢strengthen x x₁ n≤l)
⊢r-strengthen (⊢r-cons x ⊢rs nnil) (sdr-cons x₁ rs~n) n≤l = ⊢r-cons (⊢strengthen x x₁ n≤l) (⊢r-strengthen ⊢rs rs~n n≤l) (rs≢rnil-↓r nnil)

⊢strengthen-0 : ∀ {Γ cc e A B}
  → Γ , A ⊢ cc # e ↑ 0 ⦂ B
  → Γ ⊢ cc # e ⦂ B
⊢strengthen-0 {e = e} ⊢e with ⊢strengthen ⊢e ↑-shifted z≤n
... | ind-e rewrite ↑-↓-id e 0 = ind-e


∋-determinism : ∀ {Γ x A B}
  → Γ ∋ x ⦂ A
  → Γ ∋ x ⦂ B
  → A ≡ B
∋-determinism Z Z = refl
∋-determinism (S ∋1) (S ∋2) = ∋-determinism ∋1 ∋2

data _↪_❪_,_❫ : Type → ℕ → List Type → Type → Set where

  n-none : ∀ {A}
    → A ↪ 0 ❪ [] , A ❫

  n-cons : ∀ {A B T n Bs}
    → B ↪ n ❪ Bs , T ❫
    → (A `→ B) ↪ (suc n) ❪ A ∷ Bs , T ❫

≤trans : ∀ {A B C j}
  → A ≤ j # B
  → B ≤ j # C
  → A ≤ j # C
≤trans {B = Int} ≤Z ≤Z = ≤Z
≤trans {B = Int} ≤int∞ ≤2 = ≤2
≤trans {B = Int} (≤and₁ ≤1 neq) ≤2 = ≤and₁ (≤trans ≤1 ≤2) neq
≤trans {B = Int} (≤and₂ ≤1 neq) ≤2 = ≤and₂ (≤trans ≤1 ≤2) neq
≤trans {B = Float} ≤Z ≤Z = ≤Z
≤trans {B = Float} ≤float∞ ≤2 = ≤2
≤trans {B = Float} (≤and₁ ≤1 neq) ≤2 = ≤and₁ (≤trans ≤1 ≤2) neq
≤trans {B = Float} (≤and₂ ≤1 neq) ≤2 = ≤and₂ (≤trans ≤1 ≤2) neq
≤trans {B = Top} ≤Z ≤Z = ≤Z
≤trans {B = Top} ≤top ≤top = ≤top
≤trans {B = Top} ≤top (≤and ≤2 ≤3) = ≤and (≤trans ≤top ≤2) (≤trans ≤top ≤3)
≤trans {B = Top} (≤and₁ ≤1 neq) ≤2 = ≤and₁ (≤trans ≤1 ≤2) neq
≤trans {B = Top} (≤and₂ ≤1 neq) ≤2 = ≤and₂ (≤trans ≤1 ≤2) neq

≤trans {B = B `→ B₁} ≤Z ≤2 = ≤2
≤trans {B = B `→ B₁} (≤arr-∞ ≤1 ≤3) ≤top = ≤top
≤trans {B = B `→ B₁} (≤arr-∞ ≤1 ≤3) (≤arr-∞ ≤2 ≤4) = ≤arr-∞ (≤trans ≤2 ≤1) (≤trans ≤3 ≤4)
≤trans {B = B `→ B₁} (≤arr-∞ ≤1 ≤3) (≤and ≤2 ≤4) = ≤and (≤trans (≤arr-∞ ≤1 ≤3) ≤2) (≤trans (≤arr-∞ ≤1 ≤3) ≤4)
≤trans {B = B `→ B₁} (≤arr-S⇐ ≤1 ≤3) (≤arr-S⇐ ≤2 ≤4) = ≤arr-S⇐ ≤2 (≤trans ≤3 ≤4)
≤trans {B = B `→ B₁} (≤arr-S⇒ x₁ x₂) (≤arr-S⇒ x x₃) = ≤arr-S⇒ x (≤trans x₂ x₃)

≤trans {B = B `→ B₁} (≤and₁ ≤1 neq) ≤2 = ≤and₁ (≤trans ≤1 ≤2) neq
≤trans {B = B `→ B₁} (≤and₂ ≤1 neq) ≤2 = ≤and₂ (≤trans ≤1 ≤2) neq
≤trans {B = B & B₁} ≤Z ≤2 = ≤2
≤trans {B = B & B₁} (≤and₁ ≤1 neq) ≤2 = ≤and₁ (≤trans ≤1 ≤2) neq
≤trans {B = B & B₁} (≤and₂ ≤1 neq) ≤2 = ≤and₂ (≤trans ≤1 ≤2) neq
≤trans {B = B & B₁} (≤and ≤1 ≤3) ≤top = ≤top
≤trans {B = B & B₁} (≤and ≤1 ≤3) (≤and₁ ≤2 neq) = ≤trans ≤1 ≤2
≤trans {B = B & B₁} (≤and ≤1 ≤3) (≤and₂ ≤2 neq) = ≤trans ≤3 ≤2
≤trans {B = B & B₁} (≤and ≤1 ≤3) (≤and ≤2 ≤4) = ≤and (≤trans (≤and ≤1 ≤3) ≤2) (≤trans (≤and ≤1 ≤3) ≤4)

≤trans {B = τ⟦ l ↦ B ⟧} ≤Z ≤2 = ≤2
≤trans {B = τ⟦ l ↦ B ⟧} (≤rcd∞ ≤1) ≤top = ≤top
≤trans {B = τ⟦ l ↦ B ⟧} (≤rcd∞ ≤1) (≤rcd∞ ≤2) = ≤rcd∞ (≤trans ≤1 ≤2)
≤trans {B = τ⟦ l ↦ B ⟧} (≤rcd∞ ≤1) (≤and ≤2 ≤3) = ≤and (≤trans (≤rcd∞ ≤1) ≤2) (≤trans (≤rcd∞ ≤1) ≤3)
≤trans {B = τ⟦ l ↦ B ⟧} (≤rcd-Sl ≤1) (≤rcd-Sl ≤2) = ≤rcd-Sl (≤trans ≤1 ≤2)
≤trans {B = τ⟦ l ↦ B ⟧} (≤and₁ ≤1 neq) ≤2 = ≤and₁ (≤trans ≤1 ≤2) neq
≤trans {B = τ⟦ l ↦ B ⟧} (≤and₂ ≤1 neq) ≤2 = ≤and₂ (≤trans ≤1 ≤2) neq

----------------------------------------------------------------------
--+                           Subsumption                          +--
----------------------------------------------------------------------

⊢sub' : ∀ {Γ e A B i}
  → Γ ⊢ ♭ Z # e ⦂ B
  → B ≤ i # A
  → Γ ⊢ i # e ⦂ A
⊢sub' {i = ♭ Z} ⊢e ≤Z = ⊢e
⊢sub' {i = ♭ Z} ⊢e (≤and₁ B≤A x) = ⊥-elim (x refl)
⊢sub' {i = ♭ Z} ⊢e (≤and₂ B≤A x) = ⊥-elim (x refl)
⊢sub' {i = ♭ ∞} ⊢e B≤A = ⊢sub ⊢e B≤A (λ ())
⊢sub' {i = ♭ (S⇐ x)} ⊢e B≤A = ⊢sub ⊢e B≤A (λ ())
⊢sub' {i = ♭ (Sl x)} ⊢e B≤A = ⊢sub ⊢e B≤A (λ ())
⊢sub' {i = S⇒ i} ⊢e B≤A = ⊢sub ⊢e B≤A (λ ())
