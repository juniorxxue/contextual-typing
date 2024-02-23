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
    → (Int ⇒ A) # (Float ⇒ B)

  #-base-2 : ∀ {A B}
    → (Float ⇒ A) # (Int ⇒ B)

  #-rcd : ∀ {x y A B}
    → x ≢ y
    → τ⟦ x ↦ A ⟧ # τ⟦ y ↦ B ⟧
    
data WF : Type → Set where
  wf-int : WF Int
  wf-float : WF Float
  wf-arr : ∀ {A B} → WF A → WF B → WF (A ⇒ B)
  wf-and : ∀ {A B} → WF A → WF B → A # B → WF (A & B)

data WFG : Context → Set where
  wfg-∅ : WFG ∅
  wfg-, : ∀ {Γ A} → WFG Γ → WF A → WFG (Γ , A)

data WFE : Term → Set where
  wfe-c : ∀ {n} → WFE (𝕔 n)
  wfe-var : ∀ {x} → WFE (` x)
  wfe-lam : ∀ {e} → WFE e → WFE (ƛ e)
  wfe-app : ∀ {e₁ e₂} → WFE e₁ → WFE e₂ → WFE (e₁ · e₂)
  wfe-ann : ∀ {e A} → WFE e → WF A → WFE (e ⦂ A)

data WFH : Hint → Set where
  wfh-□ : WFH □
  wfh-τ : ∀ {A} → WF A → WFH (τ A)
  wfh-e : ∀ {e H} → WFH H → WFE e → WFH (⟦ e ⟧⇒ H)

{-

Γ ⊢ A₁ & A₂ < H ⇝ B
  Γ ⊢ A₁ < H ⇝ B
  
Γ ⊢ A₁ & A₂ < H ⇝ C
  Γ ⊢ A₂ < H ⇝ C

we have
A₁ # A₂

does it contribute to B = C

-}

{-

#-false : ∀ {Γ A B C D H}
  → H ≢ □
  → WFH H
  → WF A
  → WF B
  → A # B
  → Γ ⊢a A ≤ H ⇝ C
  → Γ ⊢a B ≤ H ⇝ D
  → ⊥

#-false H≢□ (wfh-τ ()) wfA wfB (#-and-l A#B A#B₁) ≤a-top s2
#-false H≢□ wfh wfA wfB (#-and-l A#B A#B₁) ≤a-□ s2 = ⊥-elim (H≢□ refl)
#-false H≢□ wfh (wf-and wfA wfA₁ x₁) wfB (#-and-l A#B A#B₁) (≤a-and-l s1 x) s2 = #-false x wfh wfA wfB A#B s1 s2
#-false H≢□ wfh (wf-and wfA wfA₁ x₁) wfB (#-and-l A#B A#B₁) (≤a-and-r s1 x) s2 = #-false x wfh wfA₁ wfB A#B₁ s1 s2
#-false H≢□ wfh wfA'@(wf-and wfA wfA₁ x) (wf-and wfB wfB₁ x₂) (#-and-l A#B A#B₁) s1'@(≤a-and s1 s3) (≤a-and-l s2 x₁) =
  #-false x₁ wfh wfA' wfB (#-and-l {!!} {!!}) s1' s2
#-false H≢□ wfh wfA'@(wf-and wfA wfA₁ x) wfB (#-and-l A#B A#B₁) s1'@(≤a-and s1 s3) (≤a-and-r s2 x₁) = {!!}
#-false H≢□ (wfh-τ (wf-and x₁ x₂ x₃)) (wf-and wfA wfA₁ x) wfB (#-and-l A#B A#B₁) (≤a-and s1 s3) (≤a-and s2 s4) =
  #-false (λ ()) (wfh-τ x₁) (wf-and wfA wfA₁ x) wfB (#-and-l A#B A#B₁) s1 s2
#-false H≢□ wfh wfA wfB (#-and-r A#B A#B₁) s1 s2 = {!!}

#-false H≢□ (wfh-τ ()) wfA wfB (#-base-1 A#B) ≤a-top s2
#-false H≢□ wfh wfA wfB (#-base-1 A#B) ≤a-□ s2 = ⊥-elim (H≢□ refl)
#-false H≢□ wfh wfA wfB (#-base-1 A#B) (≤a-arr s1 s3) (≤a-arr s2 s4) = #-false (λ ()) {!!} {!!} {!!} A#B s3 s4 -- proved
#-false H≢□ wfh wfA wfB (#-base-1 A#B) (≤a-hint x s1) (≤a-hint x₁ s2) = {!!}
#-false H≢□ (wfh-τ (wf-and x x₁ x₂)) wfA wfB (#-base-1 A#B) (≤a-and s1 s3) (≤a-and s2 s4) = {!!}
#-false H≢□ wfh wfA wfB (#-base-2 A#B) s1 s2 = {!!} -- duplicated
-}



{-
⊢a-unique = {!!}  

≤a-unique wfg wf wfh ≤a-int ≤a-int = refl
≤a-unique wfg wf wfh ≤a-float ≤a-float = refl
≤a-unique wfg wf (wfh-τ ()) ≤a-top s2
≤a-unique wfg wf wfh ≤a-□ ≤a-□ = refl
≤a-unique wfg wf wfh ≤a-□ (≤a-and-l s2 x) = ⊥-elim (x refl)
≤a-unique wfg wf wfh ≤a-□ (≤a-and-r s2 x) = ⊥-elim (x refl)
≤a-unique wfg wf wfh (≤a-arr s1 s3) (≤a-arr s2 s4) = refl
≤a-unique wfg (wf-arr wfA wfB) (wfh-e wfh x) (≤a-hint ⊢1 s1) (≤a-hint ⊢2 s2) rewrite ≤a-unique wfg wfB wfh s1 s2 = refl
≤a-unique wfg (wf-and wf wf₁ A#B) wfh (≤a-and-l s1 x) ≤a-top = {!!} -- tri
≤a-unique wfg (wf-and wf wf₁ A#B) wfh (≤a-and-l s1 x) ≤a-□ = {!!} -- tri
≤a-unique wfg (wf-and wf wf₁ A#B) wfh (≤a-and-l s1 x) (≤a-and-l s2 x₁) = ≤a-unique wfg wf wfh s1 s2
≤a-unique wfg (wf-and wf wf₁ A#B) wfh (≤a-and-l s1 x) (≤a-and-r s2 x₁) = {!!}
≤a-unique wfg (wf-and wf wf₁ A#B) wfh (≤a-and-l s1 x) (≤a-and s2 s3) = {!!}
≤a-unique wfg wf wfh (≤a-and-r s1 x) s2 = {!!}
≤a-unique wfg wf wfh (≤a-and s1 s3) s2 = {!!}
-}

