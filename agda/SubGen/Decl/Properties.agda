module SubGen.Decl.Properties where

open import SubGen.Prelude
open import SubGen.Common
open import SubGen.Decl
open import SubGen.Properties

----------------------------------------------------------------------
--+                                                                +--
--+                           Weakening                            +--
--+                                                                +--
----------------------------------------------------------------------

⊢d-weaken : ∀ {Γ cc e A B n}
  → Γ ⊢d cc # e ⦂ B
  → (n≤l : n ≤ length Γ)
  → Γ ↑ n [ n≤l ] A ⊢d cc # (e ↑ n) ⦂ B
⊢d-weaken ⊢d-int n≤l = ⊢d-int
⊢d-weaken (⊢d-var x∈Γ) n≤l = ⊢d-var (∋-weaken x∈Γ n≤l)
⊢d-weaken (⊢d-lam₁ ⊢e) n≤l = ⊢d-lam₁ (⊢d-weaken ⊢e (s≤s n≤l))
⊢d-weaken (⊢d-lam₂ ⊢e) n≤l = ⊢d-lam₂ (⊢d-weaken ⊢e (s≤s n≤l))
⊢d-weaken (⊢d-app₁ ⊢f ⊢e) n≤l = ⊢d-app₁ (⊢d-weaken ⊢f n≤l) (⊢d-weaken ⊢e n≤l)
⊢d-weaken (⊢d-app₂ ⊢f ⊢e) n≤l = ⊢d-app₂ (⊢d-weaken ⊢f n≤l) (⊢d-weaken ⊢e n≤l)
⊢d-weaken (⊢d-ann ⊢e) n≤l = ⊢d-ann (⊢d-weaken ⊢e n≤l)
⊢d-weaken (⊢d-& ⊢e₁ ⊢e₂) n≤l = ⊢d-& (⊢d-weaken ⊢e₁ n≤l) (⊢d-weaken ⊢e₂ n≤l)
⊢d-weaken (⊢d-sub ⊢e A≤B neq) n≤l = ⊢d-sub (⊢d-weaken ⊢e n≤l) A≤B neq

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
⊢d-strengthen (⊢d-lam₁ ⊢e) (sd-lam sd) n≤l = ⊢d-lam₁ (⊢d-strengthen ⊢e sd (s≤s n≤l))
⊢d-strengthen (⊢d-lam₂ ⊢e) (sd-lam sd) n≤l = ⊢d-lam₂ (⊢d-strengthen ⊢e sd (s≤s n≤l))
⊢d-strengthen (⊢d-app₁ ⊢f ⊢e) (sd-app sd sd₁) n≤l = ⊢d-app₁ (⊢d-strengthen ⊢f sd n≤l) (⊢d-strengthen ⊢e sd₁ n≤l)
⊢d-strengthen (⊢d-app₂ ⊢f ⊢e) (sd-app sd sd₁) n≤l = ⊢d-app₂ (⊢d-strengthen ⊢f sd n≤l) (⊢d-strengthen ⊢e sd₁ n≤l)
⊢d-strengthen (⊢d-ann ⊢e) (sd-ann sd) n≤l = ⊢d-ann (⊢d-strengthen ⊢e sd n≤l)
⊢d-strengthen (⊢d-& ⊢e₁ ⊢e₂) sd n≤l = ⊢d-& (⊢d-strengthen ⊢e₁ sd n≤l) (⊢d-strengthen ⊢e₂ sd n≤l)
⊢d-strengthen (⊢d-sub ⊢e A≤B neq) sd n≤l = ⊢d-sub (⊢d-strengthen ⊢e sd n≤l) A≤B neq

⊢d-strengthen-0 : ∀ {Γ cc e A B}
  → Γ , A ⊢d cc # e ↑ 0 ⦂ B
  → Γ ⊢d cc # e ⦂ B
⊢d-strengthen-0 {e = e} ⊢e with ⊢d-strengthen ⊢e ↑-shifted z≤n
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
    → (A ⇒ B) ↪ (suc n) ❪ A ∷ Bs , T ❫

{-

determinism is not intended

⊢d-determinism : ∀ {Γ e A B n As Bs T₁ T₂}
  → Γ ⊢d c n # e ⦂ A
  → A ↪ n ❪ As , T₁ ❫
  → Γ ⊢d c n # e ⦂ B
  → B ↪ n ❪ Bs , T₂ ❫
  → As ≡ Bs
  → T₁ ≡ T₂
⊢d-determinism ⊢d-int n-none ⊢d-int n-none refl = refl
⊢d-determinism ⊢d-int n-none (⊢d-sub ⊢2 x x₁) n-none refl = {!!} -- done
⊢d-determinism (⊢d-var x) ↪1 ⊢2 ↪2 eq = {!!} -- done

⊢d-determinism (⊢d-lam₂ ⊢1) (n-cons ↪1) (⊢d-lam₂ ⊢2) (n-cons ↪2) refl = ⊢d-determinism ⊢1 ↪1 ⊢2 ↪2 refl
⊢d-determinism (⊢d-lam₂ ⊢1) ↪1 (⊢d-sub ⊢2 x x₁) ↪2 eq = {!!} -- ⊢2 is absurd

⊢d-determinism (⊢d-app₁ ⊢1 ⊢3) n-none (⊢d-app₁ ⊢2 ⊢4) n-none refl = {!⊢d-determinism ⊢1 n-none ⊢2 n-none refl!} -- easy
⊢d-determinism (⊢d-app₁ ⊢1 ⊢3) n-none (⊢d-app₂ ⊢2 ⊢4) n-none refl = {!!} -- 
⊢d-determinism (⊢d-app₁ ⊢1 ⊢3) n-none (⊢d-sub ⊢2 x x₁) n-none refl = {!!} -- absurd

⊢d-determinism (⊢d-app₂ ⊢1 ⊢3) ↪1 ⊢2 ↪2 eq = {!!}
⊢d-determinism (⊢d-ann ⊢1) ↪1 ⊢2 ↪2 eq = {!!}
⊢d-determinism (⊢d-sub ⊢1 x x₁) ↪1 ⊢2 ↪2 eq = {!!}

-}

data wf-j : Type → Counter → Set where

  wf-∞ : ∀ {A}
    → wf-j A ∞

  wf-0 : ∀ {A}
    → wf-j A Z

  wf-S⇒ : ∀ {A B j}
    → wf-j B j
    → wf-j (A ⇒ B) (S⇒ j)

  wf-S⇐ : ∀ {A B j}
    → wf-j B j
    → wf-j (A ⇒ B) (S⇐ j)

≤d-refl : ∀ {A j}
  → wf-j A j
  → A ≤d j # A
≤d-refl wf-∞ = ≤d-refl∞
≤d-refl wf-0 = ≤d-Z
≤d-refl (wf-S⇒ wfj) = ≤d-arr-S⇒ (≤d-refl wf-∞) (≤d-refl wfj)
≤d-refl (wf-S⇐ wfj) = ≤d-arr-S⇐ (≤d-refl wf-∞) (≤d-refl wfj)

≤d-trans : ∀ {A B C j}
  → A ≤d j # B
  → B ≤d j # C
  → A ≤d j # C
≤d-trans {B = Int} ≤d-Z ≤d-Z = ≤d-Z
≤d-trans {B = Int} ≤d-int∞ ≤2 = ≤2
≤d-trans {B = Int} (≤d-and₁ ≤1) ≤2 = ≤d-and₁ (≤d-trans ≤1 ≤2)
≤d-trans {B = Int} (≤d-and₂ ≤1) ≤2 = ≤d-and₂ (≤d-trans ≤1 ≤2)
≤d-trans {B = * x} ≤d-Z ≤d-Z = ≤d-Z
≤d-trans {B = * x} ≤d-base∞ ≤2 = ≤2
≤d-trans {B = * x} (≤d-and₁ ≤1) ≤2 = ≤d-and₁ (≤d-trans ≤1 ≤2)
≤d-trans {B = * x} (≤d-and₂ ≤1) ≤2 = ≤d-and₂ (≤d-trans ≤1 ≤2)
≤d-trans {B = Top} ≤d-Z ≤d-Z = ≤d-Z
≤d-trans {B = Top} ≤d-top ≤d-top = ≤d-top
≤d-trans {B = Top} ≤d-top (≤d-and ≤2 ≤3) = ≤d-and (≤d-trans ≤d-top ≤2) (≤d-trans ≤d-top ≤3)
≤d-trans {B = Top} (≤d-and₁ ≤1) ≤2 = ≤d-and₁ (≤d-trans ≤1 ≤2)
≤d-trans {B = Top} (≤d-and₂ ≤1) ≤2 = ≤d-and₂ (≤d-trans ≤1 ≤2)

≤d-trans {B = B ⇒ B₁} ≤d-Z ≤2 = ≤2
≤d-trans {B = B ⇒ B₁} (≤d-arr-∞ ≤1 ≤3) ≤d-top = ≤d-top
≤d-trans {B = B ⇒ B₁} (≤d-arr-∞ ≤1 ≤3) (≤d-arr-∞ ≤2 ≤4) = ≤d-arr-∞ (≤d-trans ≤2 ≤1) (≤d-trans ≤3 ≤4)
≤d-trans {B = B ⇒ B₁} (≤d-arr-∞ ≤1 ≤3) (≤d-and ≤2 ≤4) = ≤d-and (≤d-trans (≤d-arr-∞ ≤1 ≤3) ≤2) (≤d-trans (≤d-arr-∞ ≤1 ≤3) ≤4)
≤d-trans {B = B ⇒ B₁} (≤d-arr-S⇒ ≤1 ≤3) (≤d-arr-S⇒ ≤2 ≤4) = ≤d-arr-S⇒ ≤2 (≤d-trans ≤3 ≤4)
≤d-trans {B = B ⇒ B₁} (≤d-arr-S⇐ ≤1 ≤3) (≤d-arr-S⇐ ≤2 ≤4) = ≤d-arr-S⇐ ≤2 (≤d-trans ≤3 ≤4)

≤d-trans {B = B ⇒ B₁} (≤d-and₁ ≤1) ≤2 = ≤d-and₁ (≤d-trans ≤1 ≤2)
≤d-trans {B = B ⇒ B₁} (≤d-and₂ ≤1) ≤2 = ≤d-and₂ (≤d-trans ≤1 ≤2)
≤d-trans {B = B & B₁} ≤d-Z ≤2 = ≤2
≤d-trans {B = B & B₁} (≤d-and₁ ≤1) ≤2 = ≤d-and₁ (≤d-trans ≤1 ≤2)
≤d-trans {B = B & B₁} (≤d-and₂ ≤1) ≤2 = ≤d-and₂ (≤d-trans ≤1 ≤2)
≤d-trans {B = B & B₁} (≤d-and ≤1 ≤3) ≤d-top = ≤d-top
≤d-trans {B = B & B₁} (≤d-and ≤1 ≤3) (≤d-and₁ ≤2) = ≤d-trans ≤1 ≤2
≤d-trans {B = B & B₁} (≤d-and ≤1 ≤3) (≤d-and₂ ≤2) = ≤d-trans ≤3 ≤2
≤d-trans {B = B & B₁} (≤d-and ≤1 ≤3) (≤d-and ≤2 ≤4) = ≤d-and (≤d-trans (≤d-and ≤1 ≤3) ≤2) (≤d-trans (≤d-and ≤1 ≤3) ≤4)
