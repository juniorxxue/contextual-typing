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


≤a-unique : ∀ {Γ A H B C}
  → WFG Γ → WF A → WFH H
  → Γ ⊢a A ≤ H ⇝ B
  → Γ ⊢a A ≤ H ⇝ C
  → B ≡ C

⊢a-unique : ∀ {Γ H e A B}
  → WFG Γ → WFH H → WFE e
  → Γ ⊢a H ⇛ e ⇛ A
  → Γ ⊢a H ⇛ e ⇛ B
  → A ≡ B

⊢r-unique : ∀ {Γ H rs A B}
  → WFG Γ → WFH H → WFR rs
  → Γ ⊢r H ⇛ rs ⇛ A
  → Γ ⊢r H ⇛ rs ⇛ B
  → A ≡ B


#-s-false : ∀ {Γ H₁ A es As₁ H₂ As₂ A₁ A₂}
  → WFG Γ
  → WFH H₁ → WFH H₂
  → WF A
  → Γ ⊢a A ≤ H₁ ⇝ A₁
  → ⟦ H₁ , A₁ ⟧→⟦ es , τ Int , As₁ , Int ⟧
  → Γ ⊢a A ≤ H₂ ⇝ A₂
  → ⟦ H₂ , A₂ ⟧→⟦ es , τ Float , As₂ , Float ⟧
  → ⊥
#-s-false wfg wfh1 wfh2 wfA ≤a-int none-τ () none-τ
#-s-false wfg (wfh-e wfh1 x₂) (wfh-e wfh2 x₃) (wf-arr wfA wfA₁) (≤a-hint x s1) (have-a spl1) (≤a-hint x₁ s2) (have-a spl2) =
  #-s-false wfg wfh1 wfh2 wfA₁ s1 spl1 s2 spl2
#-s-false wfg (wfh-l wfh1) (wfh-l wfh2) (wf-rcd wfA) (≤a-hint-l s1) (have-l spl1) (≤a-hint-l s2) (have-l spl2) =
  #-s-false wfg wfh1 wfh2 wfA s1 spl1 s2 spl2
#-s-false wfg wfh1 wfh2 wfA (≤a-and-l s1 x) spl1 (≤a-and-l s2 x₁) spl2 = {!!} -- can do by IH
#-s-false wfg wfh1 wfh2 wfA (≤a-and-l s1 x) spl1 (≤a-and-r s2 x₁) spl2 = {!!} -- cannot do by IH, since A and B is different
#-s-false wfg wfh1 wfh2 wfA (≤a-and-r s1 x) spl1 s2 spl2 = {!!}

#-false : ∀ {Γ H₁ A₁ es As₁ e H₂ A₂ As₂}
  → WFG Γ
  → WFH H₁ → WFH H₂
  → WFE e
  → Γ ⊢a H₁ ⇛ e ⇛ A₁
  → ⟦ H₁ , A₁ ⟧→⟦ es , τ Int , As₁ , Int ⟧
  → Γ ⊢a H₂ ⇛ e ⇛ A₂
  → ⟦ H₂ , A₂ ⟧→⟦ es , τ Float , As₂ , Float ⟧
  → ⊥

#-false wfg wfh1 wfh2 (wfe-app wfe wfe₁) (⊢a-app ⊢1) spl1 (⊢a-app ⊢2) spl2 =
  #-false wfg (wfh-e wfh1 wfe₁) (wfh-e wfh2 wfe₁) wfe ⊢1 (have-a spl1) ⊢2 (have-a spl2)
#-false wfg (wfh-e wfh1 x) (wfh-e wfh2 x₁) (wfe-lam wfe) (⊢a-lam₂ ⊢1 ⊢3) (have-a spl1) (⊢a-lam₂ ⊢2 ⊢4) (have-a spl2)
  with ⊢a-unique wfg wfh-□ x₁ ⊢1 ⊢2
... | refl = #-false (wfg-, wfg (⊢a-wf wfg wfh-□ x ⊢1)) (wf-⇧ wfh1) (wf-⇧ wfh2) wfe ⊢3 (spl-weaken spl1) ⊢4 (spl-weaken spl2)
#-false x (wfh-e x₄ x₅) (wfh-τ x₆) (wfe-lam x₇) (⊢a-lam₂ x₈ x₉) (have-a x₁) (⊢a-lam₁ x₂) ()
#-false x (wfh-e x₄ x₅) (wfh-τ x₆) (wfe-lam x₇) (⊢a-lam₂ x₈ x₉) (have-a x₁) (⊢a-sub () x₂ A≤H H≢□) x₃
#-false x (wfh-e x₄ x₅) (wfh-l x₆) (wfe-lam x₇) (⊢a-lam₂ x₈ x₉) x₁ (⊢a-sub p-e (⊢a-sub () x₂ A≤H₁ H≢□₁) A≤H H≢□) x₃
#-false wfg wfh1 wfh2 wfe (⊢a-sub p-e ⊢1 A≤H H≢□) spl1 (⊢a-sub p-e₁ ⊢2 A≤H₁ H≢□₁) spl2
  with ⊢a-unique wfg wfh-□ wfe ⊢1 ⊢2
... | refl = {!!}
-- #-s-false wfg wfh1 wfh2 (⊢a-wf wfg wfh-□ wfe ⊢1) A≤H spl1 A≤H₁ spl2
#-false wfg wfh1 wfh2 (wfe-prj wfe) (⊢a-prj ⊢1) spl1 (⊢a-prj ⊢2) spl2 =
  #-false wfg (wfh-l wfh1) (wfh-l wfh2) wfe ⊢1 (have-l spl1) ⊢2 (have-l spl2)

{-
#-false (⊢a-app ⊢1) spl1 (⊢a-app ⊢2) spl2 = #-false ⊢1 (have-a spl1) ⊢2 (have-a spl2)
#-false (⊢a-lam₂ ⊢1 ⊢3) (have-a spl1) (⊢a-lam₂ ⊢2 ⊢4) (have-a spl2) = {!!}
#-false (⊢a-sub p-e ⊢1 A≤H H≢□) spl1 ⊢2 spl2 = {!!}
#-false (⊢a-prj ⊢1) spl1 ⊢2 spl2 = {!!}
-}

#-false' : ∀ {Γ e}
  → WFG Γ
  → WFE e
  → Γ ⊢a τ Int ⇛ e ⇛ Int
  → Γ ⊢a τ Float ⇛ e ⇛ Float
  → ⊥
#-false' wfg wfe ⊢1 ⊢2 = #-false wfg (wfh-τ wf-int) (wfh-τ wf-float) wfe ⊢1 none-τ ⊢2 none-τ


#-eq : ∀ {Γ A B C D H}
  → H ≢ □
  → WFG Γ
  → WFH H
  → WF A
  → WF B
  → A # B
  → Γ ⊢a A ≤ H ⇝ C
  → Γ ⊢a B ≤ H ⇝ D
  → C ≡ D
#-eq H≢□ wfg wfh wfA wfB (#-and-l A#B A#B₁) ≤a-top s2 = sym (≤a-id-0 s2)
#-eq H≢□ wfg wfh wfA wfB (#-and-l A#B A#B₁) ≤a-□ s2 = ⊥-elim (H≢□ refl)
#-eq H≢□ wfg wfh (wf-and wfA wfA₁ A#B₂) wfB (#-and-l A#B A#B₁) (≤a-and-l s1 x) s2 = #-eq H≢□ wfg wfh wfA wfB A#B s1 s2
#-eq H≢□ wfg wfh (wf-and wfA wfA₁ A#B₂) wfB (#-and-l A#B A#B₁) (≤a-and-r s1 x) s2 = #-eq H≢□ wfg wfh wfA₁ wfB A#B₁ s1 s2
#-eq H≢□ wfg wfh wfA wfB (#-and-l A#B A#B₁) (≤a-and s1 s3) s2 with ≤a-id-0 s1 | ≤a-id-0 s3 | ≤a-id-0 s2
... | refl | refl | refl = refl
#-eq H≢□ wfg wfh wfA wfB (#-and-r A#B A#B₁) s1 ≤a-top = ≤a-id-0 s1
#-eq H≢□ wfg wfh wfA wfB (#-and-r A#B A#B₁) s1 ≤a-□ = ⊥-elim (H≢□ refl)
#-eq H≢□ wfg wfh wfA (wf-and wfB wfB₁ A#B₂) (#-and-r A#B A#B₁) s1 (≤a-and-l s2 x) = #-eq H≢□ wfg wfh wfA wfB A#B s1 s2
#-eq H≢□ wfg wfh wfA (wf-and wfB wfB₁ A#B₂) (#-and-r A#B A#B₁) s1 (≤a-and-r s2 x) = #-eq H≢□ wfg wfh wfA wfB₁ A#B₁ s1 s2
#-eq H≢□ wfg wfh wfA wfB (#-and-r A#B A#B₁) s1 (≤a-and s2 s3) with ≤a-id-0 s1 | ≤a-id-0 s2 | ≤a-id-0 s3
... | refl | refl | refl = refl
#-eq H≢□ wfg wfh wfA wfB #-base-1 ≤a-top s2 = sym (≤a-id-0 s2)
#-eq H≢□ wfg wfh wfA wfB #-base-1 ≤a-□ s2 = ⊥-elim (H≢□ refl)
#-eq H≢□ wfg wfh wfA wfB #-base-1 (≤a-arr s1 s3) s2 = sym (≤a-id-0 s2)
#-eq H≢□ wfg (wfh-e wfh wfe) wfA wfB #-base-1 (≤a-hint x s1) (≤a-hint x₁ s2) with ⊢a-id-0 x₁ | ⊢a-id-0 x
... | refl | refl = ⊥-elim (#-false' wfg wfe x x₁)
#-eq H≢□ wfg wfh wfA wfB #-base-1 (≤a-and s1 s3) s2 with ≤a-id-0 s1 | ≤a-id-0 s2 | ≤a-id-0 s3
... | refl | refl | refl = refl
#-eq H≢□ wfg wfh wfA wfB #-base-2 s1 s2 = {!!} -- dual
#-eq H≢□ wfg wfh wfA wfB (#-rcd x) ≤a-top s2 = sym (≤a-id-0 s2)
#-eq H≢□ wfg wfh wfA wfB (#-rcd x) ≤a-□ s2 = ⊥-elim (H≢□ refl)
#-eq H≢□ wfg wfh wfA wfB (#-rcd x) (≤a-rcd s1) s2 with ≤a-id-0 s1 | ≤a-id-0 s2
... | refl | refl = refl
#-eq H≢□ wfg (wfh-l wfh) wfA wfB (#-rcd x) (≤a-hint-l s1) (≤a-hint-l s2) = ⊥-elim (x refl)
#-eq H≢□ wfg wfh wfA wfB (#-rcd x) (≤a-and s1 s3) s2 with ≤a-id-0 s1 | ≤a-id-0 s2 | ≤a-id-0 s3
... | refl | refl | refl = refl

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
≤a-unique wfg (wf-and wf wf₁ A#B) wfh (≤a-and-l s1 x) (≤a-and-r s2 x₁) = #-eq x wfg wfh wf wf₁ A#B s1 s2
≤a-unique wfg (wf-and wf wf₁ A#B) (wfh-τ (wf-and x₁ x₂ A#B₁)) (≤a-and-l s1 x) (≤a-and s2 s3)
  rewrite ≤a-id-0 s2 | ≤a-id-0 s3 = ≤a-id-0 s1
-- andr case
≤a-unique wfg wf wfh (≤a-and-r s1 x) ≤a-top = ≤a-id-0 s1
≤a-unique wfg wf wfh (≤a-and-r s1 x) ≤a-□ = ⊥-elim (x refl)
≤a-unique wfg (wf-and wf wf₁ A#B) wfh (≤a-and-r s1 x) (≤a-and-l s2 x₁) = #-eq x wfg wfh wf₁ wf (#-comm A#B) s1 s2
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
