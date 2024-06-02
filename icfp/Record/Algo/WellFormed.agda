module Record.Algo.WellFormed where

open import Record.Prelude hiding (_≤?_) renaming (_≤_ to _≤n_)
open import Record.Common
open import Record.Properties
open import Record.Algo
open import Record.Algo.Properties

data _#_ : Type → Type → Set where

  #-and-l : ∀ {A B C}
    → A # C
    → B # C
    → (A & B) # C

  #-and-r : ∀ {A B C}
    → A # B
    → A # C
    → A # (B & C)

  #-base-1 : ∀ {A B}
    → (Int `→ A) # (Float `→ B)

  #-base-2 : ∀ {A B}
    → (Float `→ A) # (Int `→ B)

  #-rcd : ∀ {x y A B}
    → x ≢ y
    → τ⟦ x ↦ A ⟧ # τ⟦ y ↦ B ⟧

#-inv-l : ∀ {A B C}
  → (A & B) # C
  → A # C
#-inv-l (#-and-l AB#C AB#C₁) = AB#C
#-inv-l (#-and-r AB#C AB#C₁) = #-and-r (#-inv-l AB#C) (#-inv-l AB#C₁)

#-inv-r : ∀ {A B C}
  → (A & B) # C
  → B # C
#-inv-r (#-and-l AB#C AB#C₁) = AB#C₁
#-inv-r (#-and-r AB#C AB#C₁) = #-and-r (#-inv-r AB#C) (#-inv-r AB#C₁)
    
data WF : Type → Set where
  wf-int : WF Int
  wf-float : WF Float
  wf-top : WF Top
  wf-arr : ∀ {A B} → WF A → WF B → WF (A `→ B)
  wf-and : ∀ {A B} → WF A → WF B → (A#B : A # B) → WF (A & B)
  wf-rcd : ∀ {l A} → WF A → WF (τ⟦ l ↦ A ⟧)

data WFG : Env → Set where
  wfg-∅ : WFG ∅
  wfg-, : ∀ {Γ A} → WFG Γ → WF A → WFG (Γ , A)

infix 3 _∉_

data _∉_ : Label → Record → Set where
  notin-empty : ∀ {l}
    → l ∉ rnil

  notin-cons : ∀ {l₁ l₂ rs e}
    → l₁ ≢ l₂
    → l₁ ∉ rs
    → l₁ ∉ r⟦ l₂ ↦ e ⟧ rs

data Value : Term → Set where

  V-n : ∀ {c}
    → Value (𝕔 c)

  V-ƛ : ∀ {e}
    → Value (ƛ e)

data WFE : Term → Set 
data WFR : Record → Set

data WFE where
  wfe-c : ∀ {n} → WFE (𝕔 n)
  wfe-var : ∀ {x} → WFE (` x)
  wfe-lam : ∀ {e} → WFE e → WFE (ƛ e)
  wfe-app : ∀ {e₁ e₂} → WFE e₁ → WFE e₂ → Value e₂ → WFE (e₁ · e₂)
  wfe-ann : ∀ {e A} → WFE e → WF A → WFE (e ⦂ A)
  wfe-rcd : ∀ {rs} → WFR rs → WFE (𝕣 rs)
  wfe-prj : ∀ {e l} → WFE e → WFE (e 𝕡 l)

data WFR where
  wfr-nil : WFR rnil
  wfr-cons : ∀ {e l rs}
    → WFE e
    → WFR rs
    → l ∉ rs
    → WFR (r⟦ l ↦ e ⟧ rs)

data WFΣ : Context → Set where
  wfh-□ : WFΣ □
  wfh-τ : ∀ {A} → WF A → WFΣ (τ A)
  wfh-e : ∀ {e Σ} → WFΣ Σ → WFE e → Value e → WFΣ (⟦ e ⟧⇒ Σ)
  wfh-l : ∀ {l Σ} → WFΣ Σ → WFΣ (⌊ l ⌋⇒ Σ)


∉-↑r : ∀ {rs l n}
  → l ∉ rs
  → l ∉ rs ↑r n
∉-↑r notin-empty = notin-empty
∉-↑r (notin-cons x ni) = notin-cons x (∉-↑r ni)

wf-↑ : ∀ {e n}
  → WFE e
  → WFE (e ↑ n)
  
wfr-↑r : ∀ {rs n}
  → WFR rs
  → WFR (rs ↑r n)

wfr-↑r wfr-nil = wfr-nil
wfr-↑r (wfr-cons x wfr wfl) = wfr-cons (wf-↑ x) (wfr-↑r wfr) (∉-↑r wfl)

v-↑ : ∀ {e n}
  → Value e
  → Value (e ↑ n)
v-↑ V-n = V-n
v-↑ V-ƛ = V-ƛ

wf-↑ wfe-c = wfe-c
wf-↑ wfe-var = wfe-var
wf-↑ (wfe-lam wfe) = wfe-lam (wf-↑ wfe)
wf-↑ (wfe-app wfe wfe₁ ve) = wfe-app (wf-↑ wfe) (wf-↑ wfe₁) (v-↑ ve)
wf-↑ (wfe-ann wfe x) = wfe-ann (wf-↑ wfe) x
wf-↑ (wfe-rcd x) = wfe-rcd (wfr-↑r x)
wf-↑ (wfe-prj wfe) = wfe-prj (wf-↑ wfe)

wf-⇧ : ∀ {Σ n}
  → WFΣ Σ
  → WFΣ (Σ ⇧ n)
wf-⇧ wfh-□ = wfh-□
wf-⇧ (wfh-τ x) = wfh-τ x
wf-⇧ (wfh-e wfh x ve) = wfh-e (wf-⇧ wfh) (wf-↑ x) (v-↑ ve)
wf-⇧ (wfh-l wfh) = wfh-l (wf-⇧ wfh)


x∈Γ-wf : ∀ {Γ x A}
  → WFG Γ
  → Γ ∋ x ⦂ A
  → WF A
x∈Γ-wf (wfg-, wfg x) Z = x
x∈Γ-wf (wfg-, wfg x) (S x∈Γ) = x∈Γ-wf wfg x∈Γ

⊢wf : ∀ {Γ Σ e A}
  → WFG Γ
  → WFΣ Σ
  → WFE e
  → Γ ⊢ Σ ⇒ e ⇒ A
  → WF A
  
≤wf : ∀ {Γ Σ A B}
  → WFG Γ
  → WFΣ Σ
  → WF A
  → Γ ⊢ A ≤ Σ ⇝ B
  → WF B

⊢r-wf : ∀ {Γ Σ rs A}
  → WFG Γ
  → WFΣ Σ
  → WFR rs
  → Γ ⊢r Σ ⇒ rs ⇒ A
  → WF A

⊢r-# : ∀ {Γ A Bs rs l}
  → rs ≢ rnil
  → Γ ⊢r □ ⇒ rs ⇒ Bs
  → l ∉ rs
  → τ⟦ l ↦ A ⟧ # Bs
⊢r-# ne ⊢nil notin = ⊥-elim (ne refl)
⊢r-# ne (⊢one x) (notin-cons x₁ notin) = #-rcd x₁
⊢r-# ne (⊢cons x ⊢rs x₁) (notin-cons x₂ notin) = #-and-r (#-rcd x₂) (⊢r-# x₁ ⊢rs notin)

⊢r-wf wfg wfh wfr ⊢nil = wf-top
⊢r-wf wfg wfh (wfr-cons x₁ wfr wfl) (⊢one x) = wf-rcd (⊢wf wfg wfh x₁ x)
⊢r-wf wfg wfh (wfr-cons x₂ wfr wfl) (⊢cons x ⊢r x₁) = wf-and (wf-rcd (⊢wf wfg wfh x₂ x)) (⊢r-wf wfg wfh wfr ⊢r) (⊢r-# x₁ ⊢r wfl)

≤wf wfg wfh wfA ≤int = wfA
≤wf wfg wfh wfA ≤float = wfA
≤wf wfg wfh wfA ≤top = wf-top
≤wf wfg wfh wfA ≤□ = wfA
≤wf wfg (wfh-τ (wf-arr x x₁)) (wf-arr wfA wfA₁) (≤arr s s₁) = wf-arr x x₁
≤wf wfg (wfh-τ (wf-rcd x)) (wf-rcd wfA) (≤rcd s) = wf-rcd (≤wf wfg (wfh-τ x) wfA s)
≤wf wfg (wfh-e wfh x₁ ve) (wf-arr wfA wfA₁) (≤hint x s) = wf-arr wfA (≤wf wfg wfh wfA₁ s)
≤wf wfg (wfh-l wfh) (wf-rcd wfA) (≤hint-l s) = wf-rcd (≤wf wfg wfh wfA s)
≤wf wfg wfh (wf-and wfA wfA₁ A#B) (≤and-l s x) = ≤wf wfg wfh wfA s
≤wf wfg wfh (wf-and wfA wfA₁ A#B) (≤and-r s x) = ≤wf wfg wfh wfA₁ s
≤wf wfg (wfh-τ (wf-and x x₁ A#B)) wfA (≤and s s₁) with ≤id-0 s | ≤id-0 s₁
... | refl | refl = wf-and x x₁ A#B

⊢wf wfg wfh wfe (⊢c {c = lit x}) = wf-int
⊢wf wfg wfh wfe (⊢c {c = flt x}) = wf-float
⊢wf wfg wfh wfe (⊢c {c = +s}) = wf-and (wf-arr wf-int (wf-arr wf-int wf-int)) (wf-arr wf-float (wf-arr wf-float wf-float)) #-base-1
⊢wf wfg wfh wfe (⊢c {c = +i x}) = wf-arr wf-int wf-int
⊢wf wfg wfh wfe (⊢c {c = +f x}) = wf-arr wf-float wf-float
⊢wf wfg wfh wfe (⊢var x∈Γ) = x∈Γ-wf wfg x∈Γ
⊢wf wfg wfh (wfe-ann wfe x) (⊢ann ⊢e) = x
⊢wf wfg wfh (wfe-app wfe wfe₁ ve) (⊢app ⊢e) with ⊢wf wfg (wfh-e wfh wfe₁ ve) wfe ⊢e
... | wf-arr r r₁ = r₁
⊢wf wfg (wfh-τ (wf-arr x x₁)) (wfe-lam wfe) (⊢lam₁ ⊢e) = wf-arr x (⊢wf (wfg-, wfg x) (wfh-τ x₁) wfe ⊢e)
⊢wf wfg (wfh-e wfh x ve) (wfe-lam wfe) (⊢lam₂ ⊢e ⊢e₁) =
  wf-arr (⊢wf wfg wfh-□ x ⊢e) (⊢wf (wfg-, wfg (⊢wf wfg wfh-□ x ⊢e)) (wf-⇧ wfh) wfe ⊢e₁)
⊢wf wfg wfh wfe (⊢sub p-e ⊢e A≤Σ Σ≢□) = ≤wf wfg wfh (⊢wf wfg wfh-□ wfe ⊢e) A≤Σ
⊢wf wfg wfh (wfe-rcd x₁) (⊢rcd x) = ⊢r-wf wfg wfh x₁ x
⊢wf wfg wfh (wfe-prj wfe) (⊢prj ⊢e) with ⊢wf wfg (wfh-l wfh) wfe ⊢e
... | wf-rcd r = r

#-comm : ∀ {A B}
  → A # B
  → B # A
#-comm (#-and-l A#B A#B₁) = #-and-r (#-comm A#B) (#-comm A#B₁)
#-comm (#-and-r A#B A#B₁) = #-and-l (#-comm A#B) (#-comm A#B₁)
#-comm #-base-1 = #-base-2
#-comm #-base-2 = #-base-1
#-comm (#-rcd x) = #-rcd (λ x₂ → x (sym x₂))


wf-c : ∀ c
  → WF (c-τ c)
wf-c (lit x) = wf-int
wf-c (flt x) = wf-float
wf-c +s = wf-and (wf-arr wf-int (wf-arr wf-int wf-int))
           (wf-arr wf-float (wf-arr wf-float wf-float)) #-base-1
wf-c (+i x) = wf-arr wf-int wf-int
wf-c (+f x) = wf-arr wf-float wf-float
