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

  #-base-1 :
     (Int ⇒ Int ⇒ Int) # (Float ⇒ Float ⇒ Float)

  #-base-2 :
     (Float ⇒ Float ⇒ Float) # (Int ⇒ Int ⇒ Int)

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
  wf-arr : ∀ {A B} → WF A → WF B → WF (A ⇒ B)
  wf-and : ∀ {A B} → WF A → WF B → (A#B : A # B) → WF (A & B)
  wf-rcd : ∀ {l A} → WF A → WF (τ⟦ l ↦ A ⟧)

data WFG : Context → Set where
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

data WFE : Term → Set 
data WFR : Record → Set

data WFE where
  wfe-c : ∀ {n} → WFE (𝕔 n)
  wfe-var : ∀ {x} → WFE (` x)
  wfe-lam : ∀ {e} → WFE e → WFE (ƛ e)
  wfe-app : ∀ {e₁ e₂} → WFE e₁ → WFE e₂ → WFE (e₁ · e₂)
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

data WFH : Hint → Set where
  wfh-□ : WFH □
  wfh-τ : ∀ {A} → WF A → WFH (τ A)
  wfh-e : ∀ {e H} → WFH H → WFE e → WFH (⟦ e ⟧⇒ H)
  wfh-l : ∀ {l H} → WFH H → WFH (⌊ l ⌋⇒ H)


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

wf-↑ wfe-c = wfe-c
wf-↑ wfe-var = wfe-var
wf-↑ (wfe-lam wfe) = wfe-lam (wf-↑ wfe)
wf-↑ (wfe-app wfe wfe₁) = wfe-app (wf-↑ wfe) (wf-↑ wfe₁)
wf-↑ (wfe-ann wfe x) = wfe-ann (wf-↑ wfe) x
wf-↑ (wfe-rcd x) = wfe-rcd (wfr-↑r x)
wf-↑ (wfe-prj wfe) = wfe-prj (wf-↑ wfe)

wf-⇧ : ∀ {H n}
  → WFH H
  → WFH (H ⇧ n)
wf-⇧ wfh-□ = wfh-□
wf-⇧ (wfh-τ x) = wfh-τ x
wf-⇧ (wfh-e wfh x) = wfh-e (wf-⇧ wfh) (wf-↑ x)
wf-⇧ (wfh-l wfh) = wfh-l (wf-⇧ wfh)


x∈Γ-wf : ∀ {Γ x A}
  → WFG Γ
  → Γ ∋ x ⦂ A
  → WF A
x∈Γ-wf (wfg-, wfg x) Z = x
x∈Γ-wf (wfg-, wfg x) (S x∈Γ) = x∈Γ-wf wfg x∈Γ

⊢a-wf : ∀ {Γ H e A}
  → WFG Γ
  → WFH H
  → WFE e
  → Γ ⊢a H ⇛ e ⇛ A
  → WF A
  
≤a-wf : ∀ {Γ H A B}
  → WFG Γ
  → WFH H
  → WF A
  → Γ ⊢a A ≤ H ⇝ B
  → WF B

⊢r-wf : ∀ {Γ H rs A}
  → WFG Γ
  → WFH H
  → WFR rs
  → Γ ⊢r H ⇛ rs ⇛ A
  → WF A

⊢r-# : ∀ {Γ A Bs rs l}
  → rs ≢ rnil
  → Γ ⊢r □ ⇛ rs ⇛ Bs
  → l ∉ rs
  → τ⟦ l ↦ A ⟧ # Bs
⊢r-# ne ⊢a-nil notin = ⊥-elim (ne refl)
⊢r-# ne (⊢a-one x) (notin-cons x₁ notin) = #-rcd x₁
⊢r-# ne (⊢a-cons x ⊢rs x₁) (notin-cons x₂ notin) = #-and-r (#-rcd x₂) (⊢r-# x₁ ⊢rs notin)

⊢r-wf wfg wfh wfr ⊢a-nil = wf-top
⊢r-wf wfg wfh (wfr-cons x₁ wfr wfl) (⊢a-one x) = wf-rcd (⊢a-wf wfg wfh x₁ x)
⊢r-wf wfg wfh (wfr-cons x₂ wfr wfl) (⊢a-cons x ⊢r x₁) = wf-and (wf-rcd (⊢a-wf wfg wfh x₂ x)) (⊢r-wf wfg wfh wfr ⊢r) (⊢r-# x₁ ⊢r wfl)

≤a-wf wfg wfh wfA ≤a-int = wfA
≤a-wf wfg wfh wfA ≤a-float = wfA
≤a-wf wfg wfh wfA ≤a-top = wf-top
≤a-wf wfg wfh wfA ≤a-□ = wfA
≤a-wf wfg (wfh-τ (wf-arr x x₁)) (wf-arr wfA wfA₁) (≤a-arr s s₁) = wf-arr x x₁
≤a-wf wfg (wfh-τ (wf-rcd x)) (wf-rcd wfA) (≤a-rcd s) = wf-rcd (≤a-wf wfg (wfh-τ x) wfA s)
≤a-wf wfg (wfh-e wfh x₁) (wf-arr wfA wfA₁) (≤a-hint x s) = wf-arr wfA (≤a-wf wfg wfh wfA₁ s)
≤a-wf wfg (wfh-l wfh) (wf-rcd wfA) (≤a-hint-l s) = wf-rcd (≤a-wf wfg wfh wfA s)
≤a-wf wfg wfh (wf-and wfA wfA₁ A#B) (≤a-and-l s x) = ≤a-wf wfg wfh wfA s
≤a-wf wfg wfh (wf-and wfA wfA₁ A#B) (≤a-and-r s x) = ≤a-wf wfg wfh wfA₁ s
≤a-wf wfg (wfh-τ (wf-and x x₁ A#B)) wfA (≤a-and s s₁) with ≤a-id-0 s | ≤a-id-0 s₁
... | refl | refl = wf-and x x₁ A#B

⊢a-wf wfg wfh wfe (⊢a-c {c = lit x}) = wf-int
⊢a-wf wfg wfh wfe (⊢a-c {c = flt x}) = wf-float
⊢a-wf wfg wfh wfe (⊢a-c {c = +s}) = wf-and (wf-arr wf-int (wf-arr wf-int wf-int)) (wf-arr wf-float (wf-arr wf-float wf-float)) #-base-1
⊢a-wf wfg wfh wfe (⊢a-c {c = +i x}) = wf-arr wf-int wf-int
⊢a-wf wfg wfh wfe (⊢a-c {c = +f x}) = wf-arr wf-float wf-float
⊢a-wf wfg wfh wfe (⊢a-var x∈Γ) = x∈Γ-wf wfg x∈Γ
⊢a-wf wfg wfh (wfe-ann wfe x) (⊢a-ann ⊢e) = x
⊢a-wf wfg wfh (wfe-app wfe wfe₁) (⊢a-app ⊢e) with ⊢a-wf wfg (wfh-e wfh wfe₁) wfe ⊢e
... | wf-arr r r₁ = r₁
⊢a-wf wfg (wfh-τ (wf-arr x x₁)) (wfe-lam wfe) (⊢a-lam₁ ⊢e) = wf-arr x (⊢a-wf (wfg-, wfg x) (wfh-τ x₁) wfe ⊢e)
⊢a-wf wfg (wfh-e wfh x) (wfe-lam wfe) (⊢a-lam₂ ⊢e ⊢e₁) =
  wf-arr (⊢a-wf wfg wfh-□ x ⊢e) (⊢a-wf (wfg-, wfg (⊢a-wf wfg wfh-□ x ⊢e)) (wf-⇧ wfh) wfe ⊢e₁)
⊢a-wf wfg wfh wfe (⊢a-sub p-e ⊢e A≤H H≢□) = ≤a-wf wfg wfh (⊢a-wf wfg wfh-□ wfe ⊢e) A≤H
⊢a-wf wfg wfh (wfe-rcd x₁) (⊢a-rcd x) = ⊢r-wf wfg wfh x₁ x
⊢a-wf wfg wfh (wfe-prj wfe) (⊢a-prj ⊢e) with ⊢a-wf wfg (wfh-l wfh) wfe ⊢e
... | wf-rcd r = r

#-comm : ∀ {A B}
  → A # B
  → B # A
#-comm (#-and-l A#B A#B₁) = #-and-r (#-comm A#B) (#-comm A#B₁)
#-comm (#-and-r A#B A#B₁) = #-and-l (#-comm A#B) (#-comm A#B₁)
#-comm #-base-1 = #-base-2
#-comm #-base-2 = #-base-1
#-comm (#-rcd x) = #-rcd (λ x₂ → x (sym x₂))


data _~_ : Hint → Hint → Set where

  ~H : ∀ {H₁ H₂ e}
    → H₁ ~ H₂
    → (⟦ e ⟧⇒ H₁) ~ (⟦ e ⟧⇒ H₂)

  ~B : τ Int ~ τ Float


data endInt : Hint → Set where

  endInt-Z : endInt (τ Int)
  
  endInt-S : ∀ {e H}
    → endInt H
    → endInt (⟦ e ⟧⇒ H)

data endFloat : Hint → Set where

  endFloat-Z : endFloat (τ Float)
  
  endFloat-S : ∀ {e H}
    → endFloat H
    → endFloat (⟦ e ⟧⇒ H)
  
out-to-in-int : ∀ {Γ A A' B e H}
  → WFG Γ
  → WF A
  → WF B
  → A # B
  → Γ ⊢a A & B ≤ ⟦ e ⟧⇒ H ⇝ A'
  → endInt H
  → Γ ⊢a τ Int ⇛ e ⇛ Int
out-to-in-int wfg (wf-and wfA wfA₁ A#B₂) wfB (#-and-l A#B A#B₁) (≤a-and-l s x) eh = out-to-in-int wfg wfA wfA₁ A#B₂ s eh
out-to-in-int wfg wfA (wf-and wfB wfB₁ A#B₂) (#-and-r A#B A#B₁) (≤a-and-l s x) eh = out-to-in-int wfg wfA wfB₁ A#B₁ (≤a-and-l s x) eh
out-to-in-int wfg (wf-and wfA wfA₁ A#B₂) wfB (#-and-l A#B A#B₁) (≤a-and-r s x) eh = out-to-in-int wfg wfA₁ wfB A#B₁ (≤a-and-r s x) eh
out-to-in-int wfg wfA (wf-and wfB wfB₁ A#B₂) (#-and-r A#B A#B₁) (≤a-and-r s x) eh = out-to-in-int wfg wfB wfB₁ A#B₂ s eh
out-to-in-int wfg wfA wfB #-base-1 (≤a-and-l (≤a-hint x₁ s) x) eh with ⊢a-id-0 x₁
... | refl = x₁
out-to-in-int wfg wfA wfB #-base-2 (≤a-and-l (≤a-hint x₁ (≤a-hint x₂ ≤a-float)) x) (endInt-S ())
out-to-in-int wfg wfA wfB #-base-2 (≤a-and-l (≤a-hint x₁ (≤a-hint x₂ ≤a-top)) x) (endInt-S ())
out-to-in-int wfg wfA wfB #-base-2 (≤a-and-l (≤a-hint x₁ (≤a-hint x₂ ≤a-□)) x) (endInt-S ())
out-to-in-int wfg wfA wfB #-base-2 (≤a-and-l (≤a-hint x₁ (≤a-hint x₂ (≤a-and s s₁))) x) (endInt-S ())
out-to-in-int wfg wfA wfB #-base-1 (≤a-and-r (≤a-hint x₁ (≤a-hint x₂ ≤a-float)) x) (endInt-S ())
out-to-in-int wfg wfA wfB #-base-1 (≤a-and-r (≤a-hint x₁ (≤a-hint x₂ ≤a-top)) x) (endInt-S ())
out-to-in-int wfg wfA wfB #-base-1 (≤a-and-r (≤a-hint x₁ (≤a-hint x₂ ≤a-□)) x)  (endInt-S ())
out-to-in-int wfg wfA wfB #-base-1 (≤a-and-r (≤a-hint x₁ (≤a-hint x₂ (≤a-and s s₁))) x) (endInt-S ())
out-to-in-int wfg wfA wfB #-base-2 (≤a-and-r (≤a-hint x₁ s) x) eh with ⊢a-id-0 x₁
... | refl = x₁

out-to-in-flt : ∀ {Γ A A' B e H}
  → WFG Γ
  → WF A
  → WF B
  → A # B
  → Γ ⊢a A & B ≤ ⟦ e ⟧⇒ H ⇝ A'
  → endFloat H
  → Γ ⊢a τ Float ⇛ e ⇛ Float
out-to-in-flt wfg (wf-and wfA wfA₁ A#B₂) wfB (#-and-l A#B A#B₁) (≤a-and-l s x) eh = out-to-in-flt wfg wfA wfA₁ A#B₂ s eh
out-to-in-flt wfg wfA (wf-and wfB wfB₁ A#B₂) (#-and-r A#B A#B₁) (≤a-and-l s x) eh = out-to-in-flt wfg wfA wfB₁ A#B₁ (≤a-and-l s x) eh
out-to-in-flt wfg (wf-and wfA wfA₁ A#B₂) wfB (#-and-l A#B A#B₁) (≤a-and-r s x) eh = out-to-in-flt wfg wfA₁ wfB A#B₁ (≤a-and-r s x) eh
out-to-in-flt wfg wfA (wf-and wfB wfB₁ A#B₂) (#-and-r A#B A#B₁) (≤a-and-r s x) eh = out-to-in-flt wfg wfB wfB₁ A#B₂ s eh
out-to-in-flt wfg wfA wfB #-base-1 (≤a-and-l (≤a-hint x₁ (≤a-hint x₂ ≤a-int)) x) (endFloat-S ())
out-to-in-flt wfg wfA wfB #-base-1 (≤a-and-l (≤a-hint x₁ (≤a-hint x₂ ≤a-top)) x) (endFloat-S ())
out-to-in-flt wfg wfA wfB #-base-1 (≤a-and-l (≤a-hint x₁ (≤a-hint x₂ ≤a-□)) x) (endFloat-S ())
out-to-in-flt wfg wfA wfB #-base-1 (≤a-and-l (≤a-hint x₁ (≤a-hint x₂ (≤a-and s s₁))) x) (endFloat-S ())
out-to-in-flt wfg wfA wfB #-base-1 (≤a-and-r (≤a-hint x₁ s) x) eh with ⊢a-id-0 x₁
... | refl = x₁
out-to-in-flt wfg wfA wfB #-base-2 (≤a-and-l (≤a-hint x₁ s) x) eh with ⊢a-id-0 x₁
... | refl = x₁
out-to-in-flt wfg wfA wfB #-base-2 (≤a-and-r (≤a-hint x₁ (≤a-hint x₂ ≤a-int)) x) (endFloat-S ())
out-to-in-flt wfg wfA wfB #-base-2 (≤a-and-r (≤a-hint x₁ (≤a-hint x₂ ≤a-top)) x) (endFloat-S ())
out-to-in-flt wfg wfA wfB #-base-2 (≤a-and-r (≤a-hint x₁ (≤a-hint x₂ ≤a-□)) x) (endFloat-S ())
out-to-in-flt wfg wfA wfB #-base-2 (≤a-and-r (≤a-hint x₁ (≤a-hint x₂ (≤a-and s s₁))) x) (endFloat-S ())

out-to-in-flt' : ∀ {Γ A A' B e H}
  → WFG Γ
  → WF A
  → WF B
  → A # B
  → Γ ⊢a A ≤ ⟦ e ⟧⇒ H ⇝ A'
  → endFloat H
  → Γ ⊢a τ Float ⇛ e ⇛ Float
out-to-in-flt' wfg (wf-and wfA wfA₁ A#B₂) wfB (#-and-l A#B A#B₁) s eh = out-to-in-flt wfg wfA wfA₁ A#B₂ s eh
out-to-in-flt' wfg wfA (wf-and wfB wfB₁ A#B₂) (#-and-r A#B A#B₁) s eh = out-to-in-flt' wfg wfA wfB₁ A#B₁ s eh
out-to-in-flt' wfg wfA wfB #-base-1 (≤a-hint x (≤a-hint x₁ ≤a-int)) (endFloat-S ())
out-to-in-flt' wfg wfA wfB #-base-1 (≤a-hint x (≤a-hint x₁ ≤a-top)) (endFloat-S ())
out-to-in-flt' wfg wfA wfB #-base-1 (≤a-hint x (≤a-hint x₁ ≤a-□)) (endFloat-S ())
out-to-in-flt' wfg wfA wfB #-base-1 (≤a-hint x (≤a-hint x₁ (≤a-and s s₁))) (endFloat-S ())
out-to-in-flt' wfg wfA wfB #-base-2 (≤a-hint x s) eh with ⊢a-id-0 x
... | refl = x

out-to-in-int' : ∀ {Γ A A' B e H}
  → WFG Γ
  → WF A
  → WF B
  → A # B
  → Γ ⊢a A ≤ ⟦ e ⟧⇒ H ⇝ A'
  → endInt H
  → Γ ⊢a τ Int ⇛ e ⇛ Int
out-to-in-int' wfg (wf-and wfA wfA₁ A#B₂) wfB (#-and-l A#B A#B₁) s eh = out-to-in-int wfg wfA wfA₁ A#B₂ s eh
out-to-in-int' wfg wfA (wf-and wfB wfB₁ A#B₂) (#-and-r A#B A#B₁) s eh = out-to-in-int' wfg wfA wfB₁ A#B₁ s eh
out-to-in-int' wfg wfA wfB #-base-1 (≤a-hint x s) eh with ⊢a-id-0 x
... | refl = x
out-to-in-int' wfg wfA wfB #-base-2 (≤a-hint x (≤a-hint x₁ ≤a-float)) (endInt-S ())
out-to-in-int' wfg wfA wfB #-base-2 (≤a-hint x (≤a-hint x₁ ≤a-top)) (endInt-S ())
out-to-in-int' wfg wfA wfB #-base-2 (≤a-hint x (≤a-hint x₁ ≤a-□)) (endInt-S ())
out-to-in-int' wfg wfA wfB #-base-2 (≤a-hint x (≤a-hint x₁ (≤a-and s s₁)))  (endInt-S ())

#-float-false : ∀ {A}
  → Float # A
  → ⊥
#-float-false (#-and-r f#A f#A₁) = #-float-false f#A

inv-flt : ∀ {Γ A B}
  → WFG Γ
  → WF A
  → WF B
  → A # B
  → Γ ⊢a A ≤ τ Float ⇝ Float
  → ⊥
inv-flt wfg (wf-and wfA wfA₁ A#B₂) wfB (#-and-l A#B A#B₁) (≤a-and-l s x) = inv-flt wfg wfA wfB A#B s
inv-flt wfg (wf-and wfA wfA₁ A#B₂) wfB (#-and-l A#B A#B₁) (≤a-and-r s x) = inv-flt wfg wfA₁ wfB A#B₁ s
inv-flt wfg wfA (wf-and wfB wfB₁ A#B₂) (#-and-r A#B A#B₁) ≤a-float = #-float-false A#B
inv-flt wfg (wf-and wfA wfA₁ A#B₃) (wf-and wfB wfB₁ A#B₂) (#-and-r A#B A#B₁) (≤a-and-l s x) = inv-flt wfg wfA wfB (#-inv-l A#B) s
inv-flt wfg (wf-and wfA wfA₁ A#B₃) (wf-and wfB wfB₁ A#B₂) (#-and-r A#B A#B₁) (≤a-and-r s x) = inv-flt wfg wfA₁ wfB₁ (#-inv-r A#B₁) s

~End : ∀ {H₁ H₂}
  → H₁ ~ H₂
  → endInt H₁ × endFloat H₂
~End (~H h~h) = ⟨ (endInt-S (proj₁ (~End h~h))) , (endFloat-S (proj₂ (~End h~h))) ⟩
~End ~B = ⟨ endInt-Z , endFloat-Z ⟩



