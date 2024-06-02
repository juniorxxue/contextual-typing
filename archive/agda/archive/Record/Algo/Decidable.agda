module Record.Algo.Decidable where

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
--    → A # B
    → (Int ⇒ A) # (Float ⇒ B)

  #-base-2 : ∀ {A B}
--    → A # B
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

postulate
  ≤a-unique : ∀ {Γ A H B C}
    → WFG Γ → WF A → WFH H
    → Γ ⊢a A ≤ H ⇝ B
    → Γ ⊢a A ≤ H ⇝ C
    → B ≡ C

  ⊢a-unique : ∀ {Γ A B H e}
    → WFG Γ → WFH H → WFE e
    → Γ ⊢a H ⇛ e ⇛ A
    → Γ ⊢a H ⇛ e ⇛ B
    → A ≡ B

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

n<o⇒n+0<o : ∀ {n o}
  → n < o
  → n + 0 < o
n<o⇒n+0<o {n} {o} n<o rewrite +-comm n 0 = n<o


size-e : Term → ℕ
size-r : Record → ℕ

size-e (𝕔 x) = 1
size-e (` x) = 1
size-e (ƛ e) = 1 + size-e e
size-e (e₁ · e₂) = 2 + size-e e₁ + size-e e₂
size-e (e ⦂ _) = 1 + size-e e
size-e (𝕣 rs) = size-r rs
size-e (e 𝕡 l) = 1 + size-e e

size-r rnil = 1
size-r (r⟦ l ↦ e ⟧ rs) = 1 + size-e e + size-r rs

size-H : Hint → ℕ
size-H □ = 0
size-H (τ _) = 0
size-H (⟦ e ⟧⇒ H) = 1 + size-e e + size-H H
size-H (⌊ l ⌋⇒ H) = 1 + size-H H -- unsure

x∈Γ-dec : ∀ Γ n
  → Dec (∃[ A ] (Γ ∋ n ⦂ A))
x∈Γ-dec ∅ n = no λ ()
x∈Γ-dec (Γ , A) zero = yes ⟨ A , Z ⟩
x∈Γ-dec (Γ , A) (suc n) with x∈Γ-dec Γ n
... | yes ⟨ A' , x∈Γ ⟩ = yes ⟨ A' , S x∈Γ ⟩
... | no ¬p = no λ where
  ⟨ A' , S x∈Γ ⟩ → ¬p ⟨ A' , x∈Γ ⟩

x∈Γ-unique : ∀ {Γ x A B}
  → Γ ∋ x ⦂ A
  → Γ ∋ x ⦂ B
  → A ≡ B
x∈Γ-unique {x = zero} Z Z = refl
x∈Γ-unique {x = suc x} (S A∈Γ) (S B∈Γ) rewrite x∈Γ-unique A∈Γ B∈Γ = refl

sub-inv : ∀ {Γ H e A A'}
  → Γ ⊢a H ⇛ e ⇛ A'
  → Γ ⊢a □ ⇛ e ⇛ A
  → Γ ⊢a A ≤ H ⇝ A'
sub-inv ⊢a-c ⊢nif = {!!}
sub-inv (⊢a-var x) ⊢nif = {!!}
sub-inv (⊢a-ann ⊢e) ⊢nif = {!!}
sub-inv (⊢a-app ⊢e) ⊢nif = {!!}
sub-inv (⊢a-lam₁ ⊢e) ⊢nif = {!!}
sub-inv (⊢a-lam₂ ⊢e ⊢e₁) ⊢nif = {!!}
sub-inv (⊢a-sub x ⊢e x₁ H≢□) ⊢nif = {!!}
sub-inv (⊢a-& ⊢e ⊢e₁) ⊢nif = ≤a-and (sub-inv ⊢e ⊢nif) (sub-inv ⊢e₁ ⊢nif)
sub-inv (⊢a-rcd x) ⊢nif = {!!}
sub-inv (⊢a-prj ⊢e) ⊢nif = {!!}
{-
sub-inv ⊢a-c ⊢a-c = ≤a-□
sub-inv (⊢a-sub x ⊢a-c x₁ H≢□) ⊢a-c = x₁
sub-inv (⊢a-sub x (⊢a-sub x₂ ⊢e x₃ H≢□₁) x₁ H≢□) ⊢a-c = ⊥-elim (H≢□₁ refl)
sub-inv (⊢a-& ⊢e ⊢e₁) ⊢a-c = ≤a-and (sub-inv ⊢e ⊢a-c) (sub-inv ⊢e₁ ⊢a-c)
sub-inv (⊢a-var x₁) (⊢a-var x) rewrite x∈Γ-unique x x₁ = ≤a-□
sub-inv (⊢a-sub x₁ (⊢a-var x₃) x₂ H≢□) (⊢a-var x) rewrite x∈Γ-unique x₃ x = x₂
sub-inv (⊢a-sub x₁ (⊢a-sub x₃ ⊢e x₄ H≢□₁) x₂ H≢□) (⊢a-var x) = ⊥-elim (H≢□₁ refl)
sub-inv (⊢a-& ⊢e ⊢e₁) (⊢a-var x) = ≤a-and (sub-inv ⊢e (⊢a-var x)) (sub-inv ⊢e₁ (⊢a-var x))

sub-inv (⊢a-ann ⊢e) (⊢a-ann ⊢e-inf) = ≤a-□
sub-inv (⊢a-sub x ⊢e x₁ H≢□) (⊢a-ann ⊢e-inf) = {!!}
sub-inv (⊢a-& ⊢e ⊢e₁) (⊢a-ann ⊢e-inf) = ≤a-and (sub-inv ⊢e (⊢a-ann ⊢e-inf)) (sub-inv ⊢e₁ (⊢a-ann ⊢e-inf))

sub-inv ⊢e (⊢a-app ⊢e-inf) = {!!}
sub-inv ⊢e (⊢a-sub x ⊢e-inf x₁ H≢□) = {!!}
sub-inv ⊢e (⊢a-rcd x) = {!!}
sub-inv ⊢e (⊢a-prj ⊢e-inf) = {!!}
-}

≤a-dec : ∀ k Γ H A
  → size-H H < k
  → Dec (∃[ B ](Γ ⊢a A ≤ H ⇝ B))

⊢a-dec : ∀ k Γ H e
  → size-e e + size-H H < k
  → Dec (∃[ A ](Γ ⊢a H ⇛ e ⇛ A))

private
  inv-case-const : ∀ {Γ H c A}
    → ¬ (∃[ A' ](Γ ⊢a (c-τ c) ≤ H ⇝ A'))
    → Γ ⊢a H ⇛ 𝕔 c ⇛ A
    → ⊥
  inv-case-const {c = c} ¬p ⊢a-c = ¬p ⟨ c-τ c , ≤a-□ ⟩
  inv-case-const {A = A} ¬p (⊢a-sub x ⊢a-c x₁ H≢□) = ¬p ⟨ A , x₁ ⟩
  inv-case-const ¬p (⊢a-sub x (⊢a-sub x₂ ⊢e x₃ H≢□₁) x₁ H≢□) = ⊥-elim (H≢□₁ refl)
  inv-case-const ¬p (⊢a-& {A = A} {B = B} ⊢e ⊢e₁) = ¬p ⟨ A & B , sub-inv (⊢a-& ⊢e ⊢e₁) ⊢a-c ⟩

  inv-case-var : ∀ {Γ H x A A₁}
    → ¬ (∃[ A' ](Γ ⊢a A₁ ≤ H ⇝ A'))
    → Γ ∋ x ⦂ A₁
    → Γ ⊢a H ⇛ ` x ⇛ A
    → ⊥
  inv-case-var {A₁ = A₁} ¬p x∈Γ (⊢a-var x∈Γ') rewrite sym (x∈Γ-unique x∈Γ x∈Γ') = ¬p ⟨ A₁ , ≤a-□ ⟩
  inv-case-var {A = A} ¬p x∈Γ (⊢a-sub x (⊢a-var x∈Γ') x₁ H≢□) rewrite sym (x∈Γ-unique x∈Γ x∈Γ') = ¬p ⟨ A , x₁ ⟩
  inv-case-var ¬p x∈Γ (⊢a-sub x (⊢a-sub x₂ ⊢e x₃ H≢□₁) x₁ H≢□) = ⊥-elim (H≢□₁ refl)
  inv-case-var ¬p x∈Γ (⊢a-& {A = A} {B = B} ⊢e ⊢e₁) = ¬p ⟨ (A & B) , sub-inv (⊢a-& ⊢e ⊢e₁) (⊢a-var x∈Γ) ⟩

  inv-case-var' : ∀ {Γ H x A}
    → Γ ⊢a H ⇛ ` x ⇛ A
    → ¬ (∃[ B ](Γ ∋ x ⦂ B))
    → ⊥
  inv-case-var' {A = A} (⊢a-var x∈Γ) ¬p = ¬p ⟨ A , x∈Γ ⟩
  inv-case-var' (⊢a-sub p-e (⊢a-var {A = A₁} x∈Γ) A≤H H≢□) ¬p = ¬p ⟨ A₁ , x∈Γ ⟩
  inv-case-var' {A = A} (⊢a-sub p-e (⊢a-sub p-e₁ ⊢e A≤H₁ H≢□₁) A≤H H≢□) ¬p = ⊥-elim (H≢□₁ refl)
  inv-case-var' (⊢a-& {A = A} {B = B} ⊢e ⊢e₁) ¬p = inv-case-var' ⊢e ¬p
  

≤a-dec k Γ H A sz = {!!}
-- const
⊢a-dec (suc k) Γ H (𝕔 c) (s≤s sz) with ≤a-dec k Γ H (c-τ c) sz
... | yes ⟨ A' , s ⟩ = yes ⟨ A' , (subsumption-0 ⊢a-c s) ⟩
... | no ¬p = no λ where
  ⟨ A , ⊢e' ⟩ → inv-case-const ¬p ⊢e'
-- var
⊢a-dec (suc k) Γ H (` x) (s≤s sz) with x∈Γ-dec Γ x
⊢a-dec (suc k) Γ H (` x) (s≤s sz) | yes ⟨ A , x∈Γ ⟩ with ≤a-dec k Γ H A sz
... | yes ⟨ A' , s ⟩ = yes ⟨ A' , subsumption-0 (⊢a-var x∈Γ) s ⟩
... | no ¬p = no λ where
  ⟨ A , ⊢e' ⟩ → inv-case-var ¬p x∈Γ ⊢e'
⊢a-dec (suc k) Γ H (` x) (s≤s sz) | no ¬p = no λ where
  ⟨ A , ⊢e ⟩ → inv-case-var' ⊢e ¬p
-- lam
⊢a-dec k Γ □ (ƛ e) sz = no λ where
  ⟨ A , ⊢a-sub p-e ⊢e' A≤H H≢□ ⟩ → ⊥-elim (H≢□ refl)
-- lam1  
⊢a-dec (suc k) Γ (τ A) (ƛ e) (s≤s sz) = {!!}
-- lam2
⊢a-dec (suc k) Γ (⟦ x ⟧⇒ H) (ƛ e) (s≤s sz) = {!!}
-- lam-false
⊢a-dec k Γ (⌊ x ⌋⇒ H) (ƛ e) sz = no λ where
  ⟨ A , ⊢a-sub p-e (⊢a-sub p-e₁ ⊢e' A≤H₁ H≢□₁) A≤H H≢□ ⟩ → ⊥-elim (H≢□₁ refl)
-- app
⊢a-dec k Γ H (e₁ · e₂) sz = {!!}
-- ann
⊢a-dec k Γ H (e ⦂ A) sz = {!!}
-- record
⊢a-dec k Γ H (𝕣 rs) sz = {!!}
-- proj
⊢a-dec k Γ H (e 𝕡 l) sz = {!!}
