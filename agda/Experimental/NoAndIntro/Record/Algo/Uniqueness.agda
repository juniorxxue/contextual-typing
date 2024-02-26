module Record.Algo.Uniqueness where

open import Record.Prelude hiding (_≤?_) renaming (_≤_ to _≤n_)
open import Record.Common
open import Record.Properties
open import Record.Algo
open import Record.Algo.Properties
open import Record.Algo.WellFormed

data toplike : Hint → Set where
  tl-base1 : toplike (τ Top)
  tl-base2 : toplike □
  tl-cons1 : ∀ {A B}
    → toplike (τ B)
    → toplike (τ (A ⇒ B))
  tl-cons2 : ∀ {e H}
    → toplike H
    → toplike (⟦ e ⟧⇒ H)

toplike-spec : ∀ {Γ A B H C₁ C₂}
  → WFG Γ → WF A → WF B → WFH H
  → A # B
  → Γ ⊢a A ≤ H ⇝ C₁
  → Γ ⊢a B ≤ H ⇝ C₂
  → toplike H
toplike-spec wfg (wf-and wfA wfA₁ A#B₂) wfB wfh (#-and-l A#B A#B₁) ≤a-top s2 = tl-base1
toplike-spec wfg (wf-and wfA wfA₁ A#B₂) wfB wfh (#-and-l A#B A#B₁) ≤a-□ s2 = tl-base2
toplike-spec wfg (wf-and wfA wfA₁ A#B₂) wfB wfh (#-and-l A#B A#B₁) (≤a-and-l s1 x) s2 = toplike-spec wfg wfA wfB wfh A#B s1 s2
toplike-spec wfg (wf-and wfA wfA₁ A#B₂) wfB wfh (#-and-l A#B A#B₁) (≤a-and-r s1 x) s2 = toplike-spec wfg wfA₁ wfB wfh A#B₁ s1 s2
toplike-spec wfg (wf-and wfA wfA₁ A#B₂) wfB wfh (#-and-l A#B A#B₁) (≤a-and s1 s3) s2 = {!!}
toplike-spec wfg wfA wfB wfh (#-and-r A#B A#B₁) s1 ≤a-top = tl-base1
toplike-spec wfg wfA wfB wfh (#-and-r A#B A#B₁) s1 ≤a-□ = tl-base2
toplike-spec wfg wfA (wf-and wfB wfB₁ A#B₂) wfh (#-and-r A#B A#B₁) s1 (≤a-and-l s2 x) = toplike-spec wfg wfA wfB wfh A#B s1 s2
toplike-spec wfg wfA (wf-and wfB wfB₁ A#B₂) wfh (#-and-r A#B A#B₁) s1 (≤a-and-r s2 x) = toplike-spec wfg wfA wfB₁ wfh A#B₁ s1 s2
toplike-spec wfg wfA wfB wfh (#-and-r A#B A#B₁) s1 (≤a-and s2 s3) = {!!}
toplike-spec wfg wfA wfB wfh (#-arr A#B) ≤a-top ≤a-top = tl-base1
toplike-spec wfg wfA wfB wfh (#-arr A#B) ≤a-□ ≤a-□ = tl-base2
toplike-spec wfg (wf-arr wfA wfA₁) (wf-arr wfB wfB₁) (wfh-τ (wf-arr x x₁)) (#-arr A#B) (≤a-arr s1 s3) (≤a-arr s2 s4) =
  tl-cons1 (toplike-spec wfg wfA₁ wfB₁ (wfh-τ x₁) A#B s3 s4)
toplike-spec wfg (wf-arr wfA wfA₁) (wf-arr wfB wfB₁) (wfh-e wfh x₂) (#-arr A#B) (≤a-hint x s1) (≤a-hint x₁ s2) =
  tl-cons2 ( toplike-spec wfg wfA₁ wfB₁ wfh A#B s1 s2)
toplike-spec wfg wfA wfB wfh (#-arr A#B) (≤a-and s1 s3) (≤a-and s2 s4) = {!!}
toplike-spec wfg wfA wfB wfh #-base-1 ≤a-top s2 = tl-base1
toplike-spec wfg wfA wfB wfh #-base-1 ≤a-□ s2 = tl-base2
toplike-spec wfg wfA wfB wfh #-base-1 (≤a-arr s1 ≤a-int) (≤a-arr s2 ())
toplike-spec wfg wfA wfB wfh #-base-1 (≤a-arr s1 ≤a-top) s2 = tl-cons1 tl-base1
toplike-spec wfg wfA wfB wfh #-base-1 (≤a-arr s1 (≤a-and s3 s4)) (≤a-arr s2 (≤a-and s5 s6)) = {!!}
toplike-spec wfg (wf-arr wfA wfA₁) (wf-arr wfB wfB₁) (wfh-e wfh x₂) #-base-1 (≤a-hint x s1) (≤a-hint x₁ s2) = tl-cons2 {!!}
toplike-spec wfg wfA wfB wfh #-base-1 (≤a-and s1 s3) s2 = {!!}
toplike-spec wfg wfA wfB wfh #-base-2 s1 s2 = {!!}
toplike-spec wfg wfA wfB wfh (#-rcd x) s1 s2 = {!!}

sub-unique : ∀ {Γ A B H C₁ C₂ C₃}
  → WFG Γ → WF A → WF B → WFH H
  → A # B
  → Γ ⊢a (A & B) ≤ H ⇝ C₁
  → ¬ (toplike H)
  → ¬ (Γ ⊢a A ≤ H ⇝ C₂ × Γ ⊢a B ≤ H ⇝ C₃)
sub-unique wfg wfA wfB wfh A#B s notl = {!!}

⊢a-unique : ∀ {Γ H e A B}
  → WFG Γ → WFH H → WFE e
  → Γ ⊢a H ⇛ e ⇛ A
  → Γ ⊢a H ⇛ e ⇛ B
  → A ≡ B
  
≤a-unique : ∀ {Γ A H B C}
  → WFG Γ → WF A → WFH H
  → Γ ⊢a A ≤ H ⇝ B
  → Γ ⊢a A ≤ H ⇝ C
  → B ≡ C

⊢r-unique : ∀ {Γ H rs A B}
  → WFG Γ → WFH H → WFR rs
  → Γ ⊢r H ⇛ rs ⇛ A
  → Γ ⊢r H ⇛ rs ⇛ B
  → A ≡ B

⊢r-unique wfg wfh wfr ⊢a-nil ⊢a-nil = refl
⊢r-unique wfg wfh-□ (wfr-cons x₂ wfr wfl) (⊢a-one x) (⊢a-one x₁) with ⊢a-unique wfg wfh-□ x₂ x x₁
... | refl = refl
⊢r-unique wfg wfh wfr (⊢a-one x) (⊢a-cons x₁ ⊢2 x₂) = ⊥-elim (x₂ refl)
⊢r-unique wfg wfh wfr (⊢a-cons x ⊢1 x₁) (⊢a-one x₂) = ⊥-elim (x₁ refl)
⊢r-unique wfg wfh-□ (wfr-cons x₄ wfr wfl) (⊢a-cons x ⊢1 x₁) (⊢a-cons x₂ ⊢2 x₃) with ⊢a-unique wfg wfh-□ x₄ x x₂ | ⊢r-unique wfg wfh-□ wfr ⊢1 ⊢2
... | refl | refl = refl

⊢a-unique wfg wfh wfe ⊢a-c ⊢a-c = refl
⊢a-unique wfg wfh wfe ⊢a-c (⊢a-sub p-e ⊢2 A≤H H≢□) = ⊥-elim (H≢□ refl)
⊢a-unique wfg wfh wfe (⊢a-var x∈Γ) (⊢a-var x∈Γ₁) = x∈Γ-unique x∈Γ x∈Γ₁
⊢a-unique wfg wfh wfe (⊢a-var x∈Γ) (⊢a-sub p-e ⊢2 A≤H H≢□) = ⊥-elim (H≢□ refl)
⊢a-unique wfg wfh wfe (⊢a-ann ⊢1) (⊢a-ann ⊢2) = refl
⊢a-unique wfg wfh wfe (⊢a-ann ⊢1) (⊢a-sub p-e ⊢2 A≤H H≢□) = ⊥-elim (H≢□ refl)
⊢a-unique wfg wfh (wfe-app wfe wfe₁) (⊢a-app ⊢1) (⊢a-app ⊢2) with ⊢a-unique wfg (wfh-e wfh wfe₁) wfe ⊢1 ⊢2
... | refl = refl
⊢a-unique wfg (wfh-τ (wf-arr x x₁)) (wfe-lam wfe) (⊢a-lam₁ ⊢1) (⊢a-lam₁ ⊢2) with ⊢a-unique (wfg-, wfg x) (wfh-τ x₁) wfe ⊢1 ⊢2
... | refl = refl
⊢a-unique wfg (wfh-e wfh x) (wfe-lam wfe) (⊢a-lam₂ ⊢1 ⊢3) (⊢a-lam₂ ⊢2 ⊢4) with ⊢a-unique wfg wfh-□ x ⊢1 ⊢2 
... | refl with ⊢a-unique (wfg-, wfg (⊢a-wf wfg wfh-□ x ⊢1)) (wf-⇧ wfh) wfe ⊢3 ⊢4
... | refl = refl
⊢a-unique wfg wfh wfe (⊢a-sub p-e ⊢1 A≤H H≢□) ⊢a-c = ⊥-elim (H≢□ refl)
⊢a-unique wfg wfh wfe (⊢a-sub p-e ⊢1 A≤H H≢□) (⊢a-var x∈Γ) = ⊥-elim (H≢□ refl)
⊢a-unique wfg wfh wfe (⊢a-sub p-e ⊢1 A≤H H≢□) (⊢a-ann ⊢2) = ⊥-elim (H≢□ refl)
⊢a-unique wfg wfh wfe (⊢a-sub p-e ⊢1 A≤H H≢□) (⊢a-sub p-e₁ ⊢2 A≤H₁ H≢□₁) with ⊢a-unique wfg wfh-□ wfe ⊢1 ⊢2
... | refl = ≤a-unique wfg (⊢a-wf wfg wfh-□ wfe ⊢1) wfh A≤H A≤H₁
⊢a-unique wfg wfh wfe (⊢a-sub p-e ⊢1 A≤H H≢□) (⊢a-rcd x) = ⊥-elim (H≢□ refl)
⊢a-unique wfg wfh wfe (⊢a-rcd x) (⊢a-sub p-e ⊢2 A≤H H≢□) = ⊥-elim (H≢□ refl)
⊢a-unique wfg wfh (wfe-rcd x₂) (⊢a-rcd x) (⊢a-rcd x₁) = ⊢r-unique wfg wfh x₂ x x₁
⊢a-unique wfg wfh (wfe-prj wfe) (⊢a-prj ⊢1) (⊢a-prj ⊢2) with ⊢a-unique wfg (wfh-l wfh) wfe ⊢1 ⊢2
... | refl = refl

≤a-unique wfg wf wfh ≤a-int ≤a-int = refl
≤a-unique wfg wf wfh ≤a-float ≤a-float = refl
≤a-unique wfg wf wfh ≤a-top ≤a-top = refl
≤a-unique wfg (wf-and wf wf₁ A#B) wfh ≤a-top (≤a-and-l s2 x) = ≤a-unique wfg wf wfh ≤a-top s2
≤a-unique wfg (wf-and wf wf₁ A#B) wfh ≤a-top (≤a-and-r s2 x) = ≤a-unique wfg wf₁ wfh ≤a-top s2
≤a-unique wfg wf wfh ≤a-□ ≤a-□ = refl
≤a-unique wfg (wf-and wf wf₁ A#B) wfh ≤a-□ (≤a-and-l s2 x) = ⊥-elim (x refl)
≤a-unique wfg (wf-and wf wf₁ A#B) wfh ≤a-□ (≤a-and-r s2 x) = ⊥-elim (x refl)
≤a-unique wfg wf wfh (≤a-arr s1 s3) (≤a-arr s2 s4) = refl
≤a-unique wfg (wf-rcd wf) (wfh-τ (wf-rcd x)) (≤a-rcd s1) (≤a-rcd s2) rewrite ≤a-unique wfg wf (wfh-τ x) s1 s2 = refl
≤a-unique wfg (wf-arr wf wf₁) (wfh-e wfh x₂) (≤a-hint x s1) (≤a-hint x₁ s2) rewrite ≤a-unique wfg wf₁ wfh s1 s2 = refl
-- andl case
≤a-unique wfg wf wfh (≤a-and-l s1 x) ≤a-top = ≤a-id-0 s1
≤a-unique wfg wf wfh (≤a-and-l s1 x) ≤a-□ = ⊥-elim (x refl)
≤a-unique wfg (wf-and wf wf₁ A#B) wfh (≤a-and-l s1 x) (≤a-and-l s2 x₁) = ≤a-unique wfg wf wfh s1 s2
≤a-unique wfg (wf-and wf wf₁ A#B) wfh (≤a-and-l s1 x) (≤a-and-r s2 x₁) = {!!}
-- #-eq x wfg wfh wf wf₁ A#B s1 s2
≤a-unique wfg (wf-and wf wf₁ A#B) (wfh-τ (wf-and x₁ x₂ A#B₁)) (≤a-and-l s1 x) (≤a-and s2 s3)
  rewrite ≤a-id-0 s2 | ≤a-id-0 s3 = ≤a-id-0 s1
-- andr case
≤a-unique wfg wf wfh (≤a-and-r s1 x) ≤a-top = ≤a-id-0 s1
≤a-unique wfg wf wfh (≤a-and-r s1 x) ≤a-□ = ⊥-elim (x refl)
≤a-unique wfg (wf-and wf wf₁ A#B) wfh (≤a-and-r s1 x) (≤a-and-l s2 x₁) = {!!}
-- #-eq x wfg wfh wf₁ wf (#-comm A#B) s1 s2
≤a-unique wfg (wf-and wf wf₁ A#B) wfh (≤a-and-r s1 x) (≤a-and-r s2 x₁) = ≤a-unique wfg wf₁ wfh s1 s2
≤a-unique wfg (wf-and wf wf₁ A#B) (wfh-τ (wf-and x₁ x₂ A#B₁)) (≤a-and-r s1 x) (≤a-and s2 s3)
  rewrite ≤a-id-0 s2 | ≤a-id-0 s3 = ≤a-id-0 s1
≤a-unique wfg (wf-and wf wf₁ A#B) (wfh-τ (wf-and x₁ x₂ A#B₁)) (≤a-and s1 s3) (≤a-and-l s2 x)
  rewrite ≤a-id-0 s1 | ≤a-id-0 s3 = sym (≤a-id-0 s2)
≤a-unique wfg (wf-and wf wf₁ A#B) (wfh-τ (wf-and x₁ x₂ A#B₁)) (≤a-and s1 s3) (≤a-and-r s2 x)
  rewrite ≤a-id-0 s1 | ≤a-id-0 s3 = sym (≤a-id-0 s2)
≤a-unique wfg wf wfh (≤a-and s1 s3) (≤a-and s2 s4)
  rewrite ≤a-id-0 s1 | ≤a-id-0 s2 | ≤a-id-0 s3 | ≤a-id-0 s4 = refl
≤a-unique wfg (wf-rcd wf) (wfh-l wfh) (≤a-hint-l s1) (≤a-hint-l s2) with ≤a-unique wfg wf wfh s1 s2
... | refl = refl

