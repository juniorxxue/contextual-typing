module Record.Algo.Uniqueness where

open import Record.Prelude hiding (_≤?_) renaming (_≤_ to _≤n_)
open import Record.Common
open import Record.Properties
open import Record.Algo
open import Record.Algo.Properties
open import Record.Algo.WellFormed


⊢unique : ∀ {Γ Σ e A B}
  → WFG Γ → WFΣ Σ → WFE e
  → Γ ⊢ Σ ⇒ e ⇒ A
  → Γ ⊢ Σ ⇒ e ⇒ B
  → A ≡ B

#-false' : ∀ {Γ e}
  → WFG Γ
  → WFE e
  → Value e
  → Γ ⊢ τ Int ⇒ e ⇒ Int
  → Γ ⊢ τ Float ⇒ e ⇒ Float
  → ⊥
#-false' wfg wfe (V-n {+s}) (⊢sub p-e ⊢c (≤and-l () x) Σ≢□) (⊢sub p-e₁ ⊢c A≤Σ₁ Σ≢□₁)
#-false' wfg wfe (V-n {+s}) (⊢sub p-e ⊢c (≤and-r () x) Σ≢□) (⊢sub p-e₁ ⊢c A≤Σ₁ Σ≢□₁)
#-false' wfg wfe (V-n {c}) (⊢sub p-e ⊢c A≤Σ Σ≢□) (⊢sub p-e₁ (⊢sub p-e₂ ⊢2 A≤Σ₂ Σ≢□₂) A≤Σ₁ Σ≢□₁) = ⊥-elim (Σ≢□₂ refl)
#-false' wfg wfe V-n (⊢sub p-e (⊢sub p-e₁ ⊢1 A≤Σ₁ Σ≢□₁) A≤Σ Σ≢□) ⊢2 = ⊥-elim (Σ≢□₁ refl)
#-false' wfg wfe V-ƛ (⊢sub p-e (⊢sub p-e₁ ⊢1 A≤Σ₁ Σ≢□₁) A≤Σ Σ≢□) ⊢2 = ⊥-elim (Σ≢□₁ refl)

#-eq : ∀ {Γ A B C D Σ}
  → Σ ≢ □
  → WFG Γ
  → WFΣ Σ
  → WF A
  → WF B
  → A # B
  → Γ ⊢ A ≤ Σ ⇝ C
  → Γ ⊢ B ≤ Σ ⇝ D
  → C ≡ D
#-eq Σ≢□ wfg wfh wfA wfB (#-and-l A#B A#B₁) ≤top s2 = sym (≤id-0 s2)
#-eq Σ≢□ wfg wfh wfA wfB (#-and-l A#B A#B₁) ≤□ s2 = ⊥-elim (Σ≢□ refl)
#-eq Σ≢□ wfg wfh (wf-and wfA wfA₁ A#B₂) wfB (#-and-l A#B A#B₁) (≤and-l s1 x) s2 = #-eq Σ≢□ wfg wfh wfA wfB A#B s1 s2
#-eq Σ≢□ wfg wfh (wf-and wfA wfA₁ A#B₂) wfB (#-and-l A#B A#B₁) (≤and-r s1 x) s2 = #-eq Σ≢□ wfg wfh wfA₁ wfB A#B₁ s1 s2
#-eq Σ≢□ wfg wfh wfA wfB (#-and-l A#B A#B₁) (≤and s1 s3) s2 with ≤id-0 s1 | ≤id-0 s3 | ≤id-0 s2
... | refl | refl | refl = refl
#-eq Σ≢□ wfg wfh wfA wfB (#-and-r A#B A#B₁) s1 ≤top = ≤id-0 s1
#-eq Σ≢□ wfg wfh wfA wfB (#-and-r A#B A#B₁) s1 ≤□ = ⊥-elim (Σ≢□ refl)
#-eq Σ≢□ wfg wfh wfA (wf-and wfB wfB₁ A#B₂) (#-and-r A#B A#B₁) s1 (≤and-l s2 x) = #-eq Σ≢□ wfg wfh wfA wfB A#B s1 s2
#-eq Σ≢□ wfg wfh wfA (wf-and wfB wfB₁ A#B₂) (#-and-r A#B A#B₁) s1 (≤and-r s2 x) = #-eq Σ≢□ wfg wfh wfA wfB₁ A#B₁ s1 s2
#-eq Σ≢□ wfg wfh wfA wfB (#-and-r A#B A#B₁) s1 (≤and s2 s3) with ≤id-0 s1 | ≤id-0 s2 | ≤id-0 s3
... | refl | refl | refl = refl
#-eq Σ≢□ wfg wfh wfA wfB #-base-1 ≤top s2 = sym (≤id-0 s2)
#-eq Σ≢□ wfg wfh wfA wfB #-base-1 ≤□ s2 = ⊥-elim (Σ≢□ refl)
#-eq Σ≢□ wfg wfh wfA wfB #-base-1 (≤arr s1 s3) s2 = sym (≤id-0 s2)
#-eq Σ≢□ wfg (wfh-e wfh wfe ve) wfA wfB #-base-1 (≤hint x s1) (≤hint x₁ s2) with ⊢id-0 x₁ | ⊢id-0 x 
... | refl | refl = ⊥-elim (#-false' wfg wfe ve x x₁)
#-eq Σ≢□ wfg wfh wfA wfB #-base-1 (≤and s1 s3) s2 with ≤id-0 s1 | ≤id-0 s2 | ≤id-0 s3
... | refl | refl | refl = refl
#-eq Σ≢□ wfg wfh wfA wfB #-base-2 ≤top s2 = sym (≤id-0 s2)
#-eq Σ≢□ wfg wfh wfA wfB #-base-2 ≤□ s2 = ⊥-elim (Σ≢□ refl)
#-eq Σ≢□ wfg wfh wfA wfB #-base-2 (≤arr s1 s3) s2 = sym (≤id-0 s2)
#-eq Σ≢□ wfg (wfh-e wfh wfe ve) wfA wfB #-base-2 (≤hint x s1) (≤hint x₁ s2) with ⊢id-0 x₁ | ⊢id-0 x 
... | refl | refl = ⊥-elim (#-false' wfg wfe ve x₁ x)
#-eq Σ≢□ wfg wfh wfA wfB #-base-2 (≤and s1 s3) s2 with ≤id-0 s1 | ≤id-0 s2 | ≤id-0 s3
... | refl | refl | refl = refl
#-eq Σ≢□ wfg wfh wfA wfB (#-rcd x) ≤top s2 = sym (≤id-0 s2)
#-eq Σ≢□ wfg wfh wfA wfB (#-rcd x) ≤□ s2 = ⊥-elim (Σ≢□ refl)
#-eq Σ≢□ wfg wfh wfA wfB (#-rcd x) (≤rcd s1) s2 with ≤id-0 s1 | ≤id-0 s2
... | refl | refl = refl
#-eq Σ≢□ wfg (wfh-l wfh) wfA wfB (#-rcd x) (≤hint-l s1) (≤hint-l s2) = ⊥-elim (x refl)
#-eq Σ≢□ wfg wfh wfA wfB (#-rcd x) (≤and s1 s3) s2 with ≤id-0 s1 | ≤id-0 s2 | ≤id-0 s3
... | refl | refl | refl = refl


≤unique : ∀ {Γ A Σ B C}
  → WFG Γ → WF A → WFΣ Σ
  → Γ ⊢ A ≤ Σ ⇝ B
  → Γ ⊢ A ≤ Σ ⇝ C
  → B ≡ C

⊢r-unique : ∀ {Γ Σ rs A B}
  → WFG Γ → WFΣ Σ → WFR rs
  → Γ ⊢r Σ ⇒ rs ⇒ A
  → Γ ⊢r Σ ⇒ rs ⇒ B
  → A ≡ B

⊢r-unique wfg wfh wfr ⊢nil ⊢nil = refl
⊢r-unique wfg wfh-□ (wfr-cons x₂ wfr wfl) (⊢one x) (⊢one x₁) with ⊢unique wfg wfh-□ x₂ x x₁
... | refl = refl
⊢r-unique wfg wfh wfr (⊢one x) (⊢cons x₁ ⊢2 x₂) = ⊥-elim (x₂ refl)
⊢r-unique wfg wfh wfr (⊢cons x ⊢1 x₁) (⊢one x₂) = ⊥-elim (x₁ refl)
⊢r-unique wfg wfh-□ (wfr-cons x₄ wfr wfl) (⊢cons x ⊢1 x₁) (⊢cons x₂ ⊢2 x₃) with ⊢unique wfg wfh-□ x₄ x x₂ | ⊢r-unique wfg wfh-□ wfr ⊢1 ⊢2
... | refl | refl = refl

⊢unique wfg wfh wfe ⊢c ⊢c = refl
⊢unique wfg wfh wfe ⊢c (⊢sub p-e ⊢2 A≤Σ Σ≢□) = ⊥-elim (Σ≢□ refl)
⊢unique wfg wfh wfe (⊢var x∈Γ) (⊢var x∈Γ₁) = x∈Γ-unique x∈Γ x∈Γ₁
⊢unique wfg wfh wfe (⊢var x∈Γ) (⊢sub p-e ⊢2 A≤Σ Σ≢□) = ⊥-elim (Σ≢□ refl)
⊢unique wfg wfh wfe (⊢ann ⊢1) (⊢ann ⊢2) = refl
⊢unique wfg wfh wfe (⊢ann ⊢1) (⊢sub p-e ⊢2 A≤Σ Σ≢□) = ⊥-elim (Σ≢□ refl)
⊢unique wfg wfh (wfe-app wfe wfe₁ ve) (⊢app ⊢1) (⊢app ⊢2) with ⊢unique wfg (wfh-e wfh wfe₁ ve) wfe ⊢1 ⊢2
... | refl = refl
⊢unique wfg (wfh-τ (wf-arr x x₁)) (wfe-lam wfe) (⊢lam₁ ⊢1) (⊢lam₁ ⊢2) with ⊢unique (wfg-, wfg x) (wfh-τ x₁) wfe ⊢1 ⊢2
... | refl = refl
⊢unique wfg (wfh-e wfh x ve) (wfe-lam wfe) (⊢lam₂ ⊢1 ⊢3) (⊢lam₂ ⊢2 ⊢4) with ⊢unique wfg wfh-□ x ⊢1 ⊢2 
... | refl with ⊢unique (wfg-, wfg (⊢wf wfg wfh-□ x ⊢1)) (wf-⇧ wfh) wfe ⊢3 ⊢4
... | refl = refl
⊢unique wfg wfh wfe (⊢sub p-e ⊢1 A≤Σ Σ≢□) ⊢c = ⊥-elim (Σ≢□ refl)
⊢unique wfg wfh wfe (⊢sub p-e ⊢1 A≤Σ Σ≢□) (⊢var x∈Γ) = ⊥-elim (Σ≢□ refl)
⊢unique wfg wfh wfe (⊢sub p-e ⊢1 A≤Σ Σ≢□) (⊢ann ⊢2) = ⊥-elim (Σ≢□ refl)
⊢unique wfg wfh wfe (⊢sub p-e ⊢1 A≤Σ Σ≢□) (⊢sub p-e₁ ⊢2 A≤Σ₁ Σ≢□₁) with ⊢unique wfg wfh-□ wfe ⊢1 ⊢2
... | refl = ≤unique wfg (⊢wf wfg wfh-□ wfe ⊢1) wfh A≤Σ A≤Σ₁
⊢unique wfg wfh wfe (⊢sub p-e ⊢1 A≤Σ Σ≢□) (⊢rcd x) = ⊥-elim (Σ≢□ refl)
⊢unique wfg wfh wfe (⊢rcd x) (⊢sub p-e ⊢2 A≤Σ Σ≢□) = ⊥-elim (Σ≢□ refl)
⊢unique wfg wfh (wfe-rcd x₂) (⊢rcd x) (⊢rcd x₁) = ⊢r-unique wfg wfh x₂ x x₁
⊢unique wfg wfh (wfe-prj wfe) (⊢prj ⊢1) (⊢prj ⊢2) with ⊢unique wfg (wfh-l wfh) wfe ⊢1 ⊢2
... | refl = refl

≤unique wfg wf wfh ≤int ≤int = refl
≤unique wfg wf wfh ≤float ≤float = refl
≤unique wfg wf wfh ≤top ≤top = refl
≤unique wfg (wf-and wf wf₁ A#B) wfh ≤top (≤and-l s2 x) = ≤unique wfg wf wfh ≤top s2
≤unique wfg (wf-and wf wf₁ A#B) wfh ≤top (≤and-r s2 x) = ≤unique wfg wf₁ wfh ≤top s2
≤unique wfg wf wfh ≤□ ≤□ = refl
≤unique wfg (wf-and wf wf₁ A#B) wfh ≤□ (≤and-l s2 x) = ⊥-elim (x refl)
≤unique wfg (wf-and wf wf₁ A#B) wfh ≤□ (≤and-r s2 x) = ⊥-elim (x refl)
≤unique wfg wf wfh (≤arr s1 s3) (≤arr s2 s4) = refl
≤unique wfg (wf-rcd wf) (wfh-τ (wf-rcd x)) (≤rcd s1) (≤rcd s2) rewrite ≤unique wfg wf (wfh-τ x) s1 s2 = refl
≤unique wfg (wf-arr wf wf₁) (wfh-e wfh x₂ ve) (≤hint x s1) (≤hint x₁ s2) rewrite ≤unique wfg wf₁ wfh s1 s2 = refl
-- andl case
≤unique wfg wf wfh (≤and-l s1 x) ≤top = ≤id-0 s1
≤unique wfg wf wfh (≤and-l s1 x) ≤□ = ⊥-elim (x refl)
≤unique wfg (wf-and wf wf₁ A#B) wfh (≤and-l s1 x) (≤and-l s2 x₁) = ≤unique wfg wf wfh s1 s2
≤unique wfg (wf-and wf wf₁ A#B) wfh (≤and-l s1 x) (≤and-r s2 x₁) = #-eq x wfg wfh wf wf₁ A#B s1 s2
≤unique wfg (wf-and wf wf₁ A#B) (wfh-τ (wf-and x₁ x₂ A#B₁)) (≤and-l s1 x) (≤and s2 s3)
  rewrite ≤id-0 s2 | ≤id-0 s3 = ≤id-0 s1
-- andr case
≤unique wfg wf wfh (≤and-r s1 x) ≤top = ≤id-0 s1
≤unique wfg wf wfh (≤and-r s1 x) ≤□ = ⊥-elim (x refl)
≤unique wfg (wf-and wf wf₁ A#B) wfh (≤and-r s1 x) (≤and-l s2 x₁) = #-eq x wfg wfh wf₁ wf (#-comm A#B) s1 s2
≤unique wfg (wf-and wf wf₁ A#B) wfh (≤and-r s1 x) (≤and-r s2 x₁) = ≤unique wfg wf₁ wfh s1 s2
≤unique wfg (wf-and wf wf₁ A#B) (wfh-τ (wf-and x₁ x₂ A#B₁)) (≤and-r s1 x) (≤and s2 s3)
  rewrite ≤id-0 s2 | ≤id-0 s3 = ≤id-0 s1
≤unique wfg (wf-and wf wf₁ A#B) (wfh-τ (wf-and x₁ x₂ A#B₁)) (≤and s1 s3) (≤and-l s2 x)
  rewrite ≤id-0 s1 | ≤id-0 s3 = sym (≤id-0 s2)
≤unique wfg (wf-and wf wf₁ A#B) (wfh-τ (wf-and x₁ x₂ A#B₁)) (≤and s1 s3) (≤and-r s2 x)
  rewrite ≤id-0 s1 | ≤id-0 s3 = sym (≤id-0 s2)
≤unique wfg wf wfh (≤and s1 s3) (≤and s2 s4)
  rewrite ≤id-0 s1 | ≤id-0 s2 | ≤id-0 s3 | ≤id-0 s4 = refl
≤unique wfg (wf-rcd wf) (wfh-l wfh) (≤hint-l s1) (≤hint-l s2) with ≤unique wfg wf wfh s1 s2
... | refl = refl

⊢unique-0 : ∀ {Γ e A B}
  → WFG Γ → WFE e
  → Γ ⊢ □ ⇒ e ⇒ A
  → Γ ⊢ □ ⇒ e ⇒ B
  → A ≡ B
⊢unique-0 wfg wfe ⊢1 ⊢2 = ⊢unique wfg wfh-□ wfe ⊢1 ⊢2  

⊢r-unique-0 : ∀ {Γ rs A B}
  → WFG Γ → WFR rs
  → Γ ⊢r □ ⇒ rs ⇒ A
  → Γ ⊢r □ ⇒ rs ⇒ B
  → A ≡ B
⊢r-unique-0 wfg wfr ⊢1 ⊢2 = ⊢r-unique wfg wfh-□ wfr ⊢1 ⊢2  
