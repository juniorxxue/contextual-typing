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
{-
  ≤a-unique : ∀ {Γ A H B C}
    → WFG Γ → WF A → WFH H
    → Γ ⊢a A ≤ H ⇝ B
    → Γ ⊢a A ≤ H ⇝ C
    → B ≡ C
-}
  ⊢a-unique : ∀ {Γ A B H e}
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


size-t : Type → ℕ
size-t Int = 0
size-t Float = 0
size-t Top = 0
size-t (A ⇒ B) = 1 + size-t A + size-t B
size-t (A & B) = 1 + size-t A + size-t B
size-t τ⟦ l ↦ A ⟧ = 2 + size-t A


size-e : Term → ℕ
size-r : Record → ℕ

size-e (𝕔 x) = 1
size-e (` x) = 1
size-e (ƛ e) = 1 + size-e e
size-e (e₁ · e₂) = 2 + size-e e₁ + size-e e₂
size-e (e ⦂ A) = 1 + size-t A + size-e e
size-e (𝕣 rs) = size-r rs
size-e (e 𝕡 l) = 2 + size-e e

size-r rnil = 1
size-r (r⟦ l ↦ e ⟧ rs) = 1 + size-e e + size-r rs

size-H : Hint → ℕ
size-H □ = 0
size-H (τ A) = size-t A
size-H (⟦ e ⟧⇒ H) = 1 + size-e e + size-H H
size-H (⌊ l ⌋⇒ H) = 1 + size-H H -- unsure


size-↑ : ∀ e {n}
  → size-e e ≡ size-e (e ↑ n)

size-↑r : ∀ rs {n}
  → size-r rs ≡ size-r (rs ↑r n)

size-↑ (𝕔 x) {n} = refl
size-↑ (` x) {n} = refl
size-↑ (ƛ e) {n} rewrite size-↑ e {suc n} = refl
size-↑ (e₁ · e₂) {n} rewrite size-↑ e₁ {n} | size-↑ e₂ {n}  = refl
size-↑ (e ⦂ A) {n} rewrite size-↑ e {n} = refl
size-↑ (𝕣 rs) {n} = size-↑r rs {n}
size-↑ (e 𝕡 l) {n} rewrite size-↑ e {n} = refl

size-↑r rnil {n} = refl
size-↑r (r⟦ l ↦ e ⟧ rs) {n} rewrite size-↑ e {n} | size-↑r rs {n} = refl

size-⇧ : ∀ H {n}
  → size-H H ≡ size-H (H ⇧ n)
size-⇧ □ = refl
size-⇧ (τ _) = refl
size-⇧ (⟦ e ⟧⇒ H) {n} rewrite size-⇧ H {n} | size-↑ e {n} = refl
size-⇧ (⌊ x ⌋⇒ H) {n} rewrite size-⇧ H {n} = refl

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

≤a-dec : ∀ k Γ H A
  → size-H H < k
  → Dec (∃[ B ](Γ ⊢a A ≤ H ⇝ B))

≤a-dec' : ∀ k₁ k₂ Γ H A
  → size-H H < k₁
  → size-t A < k₂
  → Dec (∃[ B ](Γ ⊢a A ≤ H ⇝ B))

⊢a-dec : ∀ k Γ H e
  → size-e e + size-H H < k
  → Dec (∃[ A ](Γ ⊢a H ⇛ e ⇛ A))

⊢r-dec : ∀ k Γ rs
  → size-r rs < k
  → Dec (∃[ A ](Γ ⊢r □ ⇛ rs ⇛ A))


private
  inv-case-const : ∀ {Γ H c A}
    → ¬ (∃[ A' ](Γ ⊢a (c-τ c) ≤ H ⇝ A'))
    → Γ ⊢a H ⇛ 𝕔 c ⇛ A
    → ⊥
  inv-case-const {c = c} ¬p ⊢a-c = ¬p ⟨ c-τ c , ≤a-□ ⟩
  inv-case-const {A = A} ¬p (⊢a-sub x ⊢a-c x₁ H≢□) = ¬p ⟨ A , x₁ ⟩
  inv-case-const ¬p (⊢a-sub x (⊢a-sub x₂ ⊢e x₃ H≢□₁) x₁ H≢□) = ⊥-elim (H≢□₁ refl)
  
  inv-case-var : ∀ {Γ H x A A₁}
    → ¬ (∃[ A' ](Γ ⊢a A₁ ≤ H ⇝ A'))
    → Γ ∋ x ⦂ A₁
    → Γ ⊢a H ⇛ ` x ⇛ A
    → ⊥
  inv-case-var {A₁ = A₁} ¬p x∈Γ (⊢a-var x∈Γ') rewrite sym (x∈Γ-unique x∈Γ x∈Γ') = ¬p ⟨ A₁ , ≤a-□ ⟩
  inv-case-var {A = A} ¬p x∈Γ (⊢a-sub x (⊢a-var x∈Γ') x₁ H≢□) rewrite sym (x∈Γ-unique x∈Γ x∈Γ') = ¬p ⟨ A , x₁ ⟩
  inv-case-var ¬p x∈Γ (⊢a-sub x (⊢a-sub x₂ ⊢e x₃ H≢□₁) x₁ H≢□) = ⊥-elim (H≢□₁ refl)
  
  inv-case-var' : ∀ {Γ H x A}
    → Γ ⊢a H ⇛ ` x ⇛ A
    → ¬ (∃[ B ](Γ ∋ x ⦂ B))
    → ⊥
  inv-case-var' {A = A} (⊢a-var x∈Γ) ¬p = ¬p ⟨ A , x∈Γ ⟩
  inv-case-var' (⊢a-sub p-e (⊢a-var {A = A₁} x∈Γ) A≤H H≢□) ¬p = ¬p ⟨ A₁ , x∈Γ ⟩
  inv-case-var' {A = A} (⊢a-sub p-e (⊢a-sub p-e₁ ⊢e A≤H₁ H≢□₁) A≤H H≢□) ¬p = ⊥-elim (H≢□₁ refl)

  sz-case-1 : ∀ {m n o k}
    → m + suc (n + o) < k
    → n + 0 < k
  sz-case-1 {m} {n} {o} {k} m+1+n+o<k rewrite +-comm n 0
                                            | +-comm n o
                                            | sym (+-assoc m (1 + o) n)
                                            | +-comm m (1 + o)
                                            = <-trans (m<n+m n (s≤s z≤n)) m+1+n+o<k
  sz-case-2 : ∀ {m n o k}
    → suc (m + n + o) < k
    → m + suc (n + o) < k
  sz-case-2 {m} {n} {o} {k} sz rewrite +-comm m (1 + n + o) | +-comm (n + o) m | +-assoc m n o = sz

  sz-case-3' : ∀ {m n o k}
    → m + (1 + n + o) < k
    → m + o < k
  sz-case-3' {m} {n} {o} {k} sz rewrite +-comm (1 + n) o | sym (+-assoc m o (suc n)) = <-trans (m<m+n (m + o) (s≤s z≤n)) sz

  sz-case-3 : ∀ {e H e' k}
    → suc (size-e e + suc (size-e e' + size-H H)) ≤n k
    → size-e e + size-H (H ⇧ 0) < k
  sz-case-3 {H = H} sz rewrite sym (size-⇧ H {0}) = sz-case-3' sz

  inv-case-lam' : ∀ {Γ e e' H A}
    → Γ ⊢a □ ⇛ e' ⇛ A
    → ¬ (∃[ C ](Γ , A ⊢a H ⇧ 0 ⇛ e ⇛ C))
    → ¬ (∃[ D ](Γ ⊢a (⟦ e' ⟧⇒ H) ⇛ ƛ e ⇛ D))
  inv-case-lam' ⊢e ¬p ⟨ D ⇒ E , ⊢a-lam₂ ⊢e' ⊢e'' ⟩ rewrite ⊢a-unique ⊢e ⊢e' = ¬p ⟨ E , ⊢e'' ⟩

  inv-case-lam'' : ∀ {Γ e' e H}
    → ¬ (∃[ C ](Γ ⊢a □ ⇛ e' ⇛ C))
    → ∃[ D ](Γ ⊢a ⟦ e' ⟧⇒ H ⇛ ƛ e ⇛ D)
    → ⊥
  inv-case-lam'' ¬p ⟨ A ⇒ B , ⊢a-lam₂ ⊢e ⊢e₁ ⟩ = ¬p ⟨ A , ⊢e ⟩

  data HoType : Type → Set where
    ht-int : HoType Int
    ht-flt : HoType Float
    ht-top : HoType Top
    ht-and : ∀ {A B} → HoType (A & B)
    ht-rcd : ∀ {l A} → HoType τ⟦ l ↦ A ⟧

  inv-case-sub-hole : ∀ {Γ A H A' e H' B C}
    → Γ ⊢a A ≤ H ⇝ A'
    → H ≡ ⟦ e ⟧⇒ H'
    → A' ≡ B & C
    → ⊥
  inv-case-sub-hole (≤a-and-l A≤H x) refl refl = inv-case-sub-hole A≤H refl refl
  inv-case-sub-hole (≤a-and-r A≤H x) refl refl = inv-case-sub-hole A≤H refl refl

  inv-case-app : ∀ {Γ H e₁ e₂ A}
    → Γ ⊢a ⟦ e₂ ⟧⇒ H ⇛ e₁ ⇛ A
    → HoType A
    → ⊥
  inv-case-app {A = Int} ⊢e neq with ⊢a-to-≤a ⊢e
  ... | ()
  inv-case-app {A = Float} ⊢e neq with ⊢a-to-≤a ⊢e
  ... | ()
  inv-case-app {A = Top} ⊢e neq with ⊢a-to-≤a ⊢e
  ... | ()
  inv-case-app {A = A & B} ⊢e neq with ⊢a-to-≤a ⊢e
  ... | r = inv-case-sub-hole r refl refl
  inv-case-app {A = τ⟦ x ↦ A ⟧} ⊢e neq  with ⊢a-to-≤a ⊢e
  ... | ()

  data HoTypeRcd : Type → Set where
    htr-int : HoTypeRcd Int
    htr-flt : HoTypeRcd Float
    htr-top : HoTypeRcd Top
    htr-and : ∀ {A B} → HoTypeRcd (A & B)
    htr-arr : ∀ {A B} → HoTypeRcd (A ⇒ B)

  inv-case-sub-hole-prj : ∀ {Γ A H A' e H' B C}
    → Γ ⊢a A ≤ H ⇝ A'
    → H ≡ ⌊ e ⌋⇒ H'
    → A' ≡ B & C
    → ⊥
  inv-case-sub-hole-prj (≤a-and-l A≤H x) refl refl = inv-case-sub-hole-prj A≤H refl refl
  inv-case-sub-hole-prj (≤a-and-r A≤H x) refl refl = inv-case-sub-hole-prj A≤H refl refl

  inv-case-prj : ∀ {Γ H e l A}
    → Γ ⊢a ⌊ l ⌋⇒ H ⇛ e ⇛ A
    → HoTypeRcd A
    → ⊥
  inv-case-prj {A = Int} ⊢e neq with ⊢a-to-≤a ⊢e
  ... | ()
  inv-case-prj {A = Float} ⊢e neq with ⊢a-to-≤a ⊢e
  ... | ()
  inv-case-prj {A = Top} ⊢e neq with ⊢a-to-≤a ⊢e
  ... | ()
  inv-case-prj {A = A & B} ⊢e neq with ⊢a-to-≤a ⊢e
  ... | r = inv-case-sub-hole-prj r refl refl
  inv-case-prj {A = A ⇒ B⟧} ⊢e neq  with ⊢a-to-≤a ⊢e
  ... | ()

{-
  inv-and : ∀ {Γ A B C}
    → Γ ⊢a A & B ≤ τ C ⇝ C
    → (Γ ⊢a A ≤ τ C ⇝ C) ⊎ (Γ ⊢a B ≤ τ C ⇝ C) -- wrong inversion lemmas
  inv-and ≤a-top = inj₁ ≤a-top
  inv-and (≤a-and-l s x) = inj₁ s
  inv-and (≤a-and-r s x) = inj₂ s
  inv-and (≤a-and s s₁) with inv-and s | inv-and s₁
  ... | inj₁ x | inj₁ y = inj₁ (≤a-and x y)
  ... | inj₁ x | inj₂ y = {!!}
  ... | inj₂ y | r2 = {!!}

  inv-sub-and : ∀ {Γ H A B C}
    → H ≢ □
    → ¬ (∃[ A' ](Γ ⊢a A ≤ H ⇝ A'))
    → ¬ (∃[ B' ](Γ ⊢a B ≤ H ⇝ B'))
    → ¬ (Γ ⊢a A & B ≤ H ⇝ C)
  inv-sub-and H≢□ ¬p1 ¬p2 ≤a-top = ¬p1 ⟨ Top , ≤a-top ⟩
  inv-sub-and H≢□ ¬p1 ¬p2 ≤a-□ = ⊥-elim (H≢□ refl)
  inv-sub-and H≢□ ¬p1 ¬p2 (≤a-and-l s x) = {!!}
  inv-sub-and H≢□ ¬p1 ¬p2 (≤a-and-r s x) = {!!}
  inv-sub-and H≢□ ¬p1 ¬p2 (≤a-and s s₁) = {!!}
-}  

  sub-inv-and-r : ∀ {Γ A B C D}
    → Γ ⊢a C ≤ τ (A & B) ⇝ D
    → (Γ ⊢a C ≤ τ A ⇝ A) × (Γ ⊢a C ≤ τ B ⇝ B)
  sub-inv-and-r (≤a-and-l s x) with sub-inv-and-r s
  ... | ⟨ s1 , s2 ⟩ = ⟨ (≤a-and-l s1 (λ ())) , (≤a-and-l s2 (λ ())) ⟩
  sub-inv-and-r (≤a-and-r s x) with sub-inv-and-r s
  ... | ⟨ s1 , s2 ⟩ = ⟨ (≤a-and-r s1 (λ ())) , (≤a-and-r s2 (λ ())) ⟩
  sub-inv-and-r (≤a-and s s₁) = ⟨ ≤a-rigid s , ≤a-rigid s₁ ⟩

  inv-case-and-r : ∀ {Γ A B C A'}
    → Γ ⊢a C ≤ τ (A & B) ⇝ A'
    → ¬ (∃[ B' ](Γ ⊢a C ≤ τ B ⇝ B'))
    → ⊥
  inv-case-and-r {B = B} ⊢e ¬p with sub-inv-and-r ⊢e
  ... | ⟨ l , r ⟩ = ¬p ⟨ B , r ⟩

  inv-case-and-l : ∀ {Γ A B C A'}
    → Γ ⊢a C ≤ τ (A & B) ⇝ A'
    → ¬ (∃[ A' ](Γ ⊢a C ≤ τ A ⇝ A'))
    → ⊥
  inv-case-and-l {A = A} ⊢e ¬p with sub-inv-and-r ⊢e
  ... | ⟨ l , r ⟩ = ¬p ⟨ A , l ⟩
    
≤a-dec k Γ H A sz = {!!}
-- H is and case, we exclude this case out
≤a-dec' (suc k₁) (suc k₂) Γ (τ (A & B)) C (s≤s sz₁) (s≤s sz₂) with ≤a-dec' k₁ (suc k₂) Γ (τ A) C {!!} (s≤s sz₂)
                                                                 | ≤a-dec' k₁ (suc k₂) Γ (τ B) C {!!} (s≤s sz₂)
... | yes ⟨ A' , s1 ⟩ | yes ⟨ B' , s2 ⟩ = yes ⟨ (A' & B') , ≤a-and s1 s2 ⟩
... | yes p | no ¬p = no λ where
  ⟨ A' , s ⟩ → inv-case-and-r s ¬p
... | no ¬p | _ = no λ where
  ⟨ A' , s ⟩ → inv-case-and-l s ¬p
-- int
≤a-dec' (suc k₁) (suc k₂) Γ □ Int (s≤s sz₁) (s≤s sz₂) = yes ⟨ Int , ≤a-□ ⟩
≤a-dec' (suc k₁) (suc k₂) Γ (τ Int) Int (s≤s sz₁) (s≤s sz₂) = yes ⟨ Int , ≤a-int ⟩
≤a-dec' (suc k₁) (suc k₂) Γ (τ Float) Int (s≤s sz₁) (s≤s sz₂) = no λ where
  ⟨ A' , () ⟩
≤a-dec' (suc k₁) (suc k₂) Γ (τ Top) Int (s≤s sz₁) (s≤s sz₂) = yes ⟨ Top , ≤a-top ⟩
≤a-dec' (suc k₁) (suc k₂) Γ (τ (A ⇒ B)) Int (s≤s sz₁) (s≤s sz₂) = no λ where
  ⟨ A' , () ⟩
≤a-dec' (suc k₁) (suc k₂) Γ (τ τ⟦ l ↦ A ⟧) Int (s≤s sz₁) (s≤s sz₂) = no λ where
  ⟨ A' , () ⟩
≤a-dec' (suc k₁) (suc k₂) Γ (⟦ e ⟧⇒ H) Int (s≤s sz₁) (s≤s sz₂) = no λ where
  ⟨ A' , () ⟩
≤a-dec' (suc k₁) (suc k₂) Γ (⌊ l ⌋⇒ H) Int (s≤s sz₁) (s≤s sz₂) = no λ where
  ⟨ A' , () ⟩
-- float
≤a-dec' (suc k₁) (suc k₂) Γ □ Float (s≤s sz₁) (s≤s sz₂) = yes ⟨ Float , ≤a-□ ⟩
≤a-dec' (suc k₁) (suc k₂) Γ (τ Int) Float (s≤s sz₁) (s≤s sz₂) = no λ where
  ⟨ A' , () ⟩
≤a-dec' (suc k₁) (suc k₂) Γ (τ Float) Float (s≤s sz₁) (s≤s sz₂) = yes ⟨ Float , ≤a-float ⟩
≤a-dec' (suc k₁) (suc k₂) Γ (τ Top) Float (s≤s sz₁) (s≤s sz₂) = yes ⟨ Top , ≤a-top ⟩
≤a-dec' (suc k₁) (suc k₂) Γ (τ (A ⇒ B)) Float (s≤s sz₁) (s≤s sz₂) = no λ where
  ⟨ A' , () ⟩
≤a-dec' (suc k₁) (suc k₂) Γ (τ τ⟦ l ↦ A ⟧) Float (s≤s sz₁) (s≤s sz₂) = no λ where
  ⟨ A' , () ⟩
≤a-dec' (suc k₁) (suc k₂) Γ (⟦ e ⟧⇒ H) Float (s≤s sz₁) (s≤s sz₂) = no λ where
  ⟨ A' , () ⟩
≤a-dec' (suc k₁) (suc k₂) Γ (⌊ l ⌋⇒ H) Float (s≤s sz₁) (s≤s sz₂) = no λ where
  ⟨ A' , () ⟩
-- top
≤a-dec' (suc k₁) (suc k₂) Γ □ Top (s≤s sz₁) (s≤s sz₂) = yes ⟨ Top , ≤a-□ ⟩
≤a-dec' (suc k₁) (suc k₂) Γ (τ Int) Top (s≤s sz₁) (s≤s sz₂) = no λ where
  ⟨ A' , () ⟩
≤a-dec' (suc k₁) (suc k₂) Γ (τ Float) Top (s≤s sz₁) (s≤s sz₂) = no λ where
  ⟨ A' , () ⟩
≤a-dec' (suc k₁) (suc k₂) Γ (τ Top) Top (s≤s sz₁) (s≤s sz₂) = yes ⟨ Top , ≤a-top ⟩
≤a-dec' (suc k₁) (suc k₂) Γ (τ (x ⇒ x₁)) Top (s≤s sz₁) (s≤s sz₂) = no λ where
  ⟨ A' , () ⟩
≤a-dec' (suc k₁) (suc k₂) Γ (τ τ⟦ l ↦ A ⟧) Top (s≤s sz₁) (s≤s sz₂) = no λ where
  ⟨ A' , () ⟩
≤a-dec' (suc k₁) (suc k₂) Γ (⟦ x ⟧⇒ H) Top (s≤s sz₁) (s≤s sz₂) = no λ where
  ⟨ A' , () ⟩
≤a-dec' (suc k₁) (suc k₂) Γ (⌊ x ⌋⇒ H) Top (s≤s sz₁) (s≤s sz₂) = no λ where
  ⟨ A' , () ⟩
-- arrow
≤a-dec' (suc k₁) (suc k₂) Γ □ (A ⇒ B) (s≤s sz₁) (s≤s sz₂) = yes ⟨ A ⇒ B , ≤a-□ ⟩
≤a-dec' (suc k₁) (suc k₂) Γ (τ Int) (A ⇒ B) (s≤s sz₁) (s≤s sz₂) = no λ where
  ⟨ A' , () ⟩
≤a-dec' (suc k₁) (suc k₂) Γ (τ Float) (A ⇒ B) (s≤s sz₁) (s≤s sz₂) = no λ where
  ⟨ A' , () ⟩
≤a-dec' (suc k₁) (suc k₂) Γ (τ Top) (A ⇒ B) (s≤s sz₁) (s≤s sz₂) = yes ⟨ Top , ≤a-top ⟩
≤a-dec' (suc k₁) (suc k₂) Γ (τ (A' ⇒ B')) (A ⇒ B) (s≤s sz₁) (s≤s sz₂) with ≤a-dec' k₁ (suc k₂) Γ (τ A) A' {!!} {!!}
                                                                         | ≤a-dec' k₁ (suc k₂) Γ (τ B') B {!!} {!!}
... | r | r' = {!!} -- problem due to contra-variance
≤a-dec' (suc k₁) (suc k₂) Γ (τ τ⟦ l ↦ A' ⟧) (A ⇒ B) (s≤s sz₁) (s≤s sz₂) = no λ where
  ⟨ A' , () ⟩
≤a-dec' (suc k₁) (suc k₂) Γ (⟦ e ⟧⇒ H) (A ⇒ B) (s≤s sz₁) (s≤s sz₂) = {!!}
≤a-dec' (suc k₁) (suc k₂) Γ (⌊ l ⌋⇒ H) (A ⇒ B) (s≤s sz₁) (s≤s sz₂) = no λ where
  ⟨ A' , () ⟩
-- and
≤a-dec' (suc k₁) (suc k₂) Γ H (A & B) (s≤s sz₁) (s≤s sz₂) with □-dec H
                                                             | ≤a-dec' (suc k₁) k₂ Γ H A (s≤s sz₁) {!!}
                                                             | ≤a-dec' (suc k₁) k₂ Γ H B (s≤s sz₁) {!!}
... | yes p  | _ | _ rewrite p = yes ⟨ A & B , ≤a-□ ⟩
... | no H≢□ | yes ⟨ A' , s ⟩ | _ = yes ⟨ A' , (≤a-and-l s H≢□) ⟩
... | no H≢□ | no ¬p | yes ⟨ A' , s ⟩ = yes ⟨ A' , (≤a-and-r s H≢□) ⟩
... | no H≢□ | no ¬p1 | no ¬p2 = {!!} -- it's doable
≤a-dec' (suc k₁) (suc k₂) Γ H τ⟦ l ↦ A ⟧ (s≤s sz₁) (s≤s sz₂) = {!!}

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
-- lam false
⊢a-dec (suc k) Γ (τ Int) (ƛ e) (s≤s sz) = no λ where
  ⟨ A , ⊢a-sub p-e (⊢a-sub p-e₁ ⊢e' A≤H₁ H≢□₁) A≤H H≢□ ⟩ → ⊥-elim (H≢□₁ refl)
⊢a-dec (suc k) Γ (τ Float) (ƛ e) (s≤s sz) = no λ where
  ⟨ A , ⊢a-sub p-e (⊢a-sub p-e₁ ⊢e' A≤H₁ H≢□₁) A≤H H≢□ ⟩ → ⊥-elim (H≢□₁ refl)
⊢a-dec (suc k) Γ (τ Top) (ƛ e) (s≤s sz) = no λ where
  ⟨ A , ⊢a-sub p-e (⊢a-sub p-e₁ ⊢e' A≤H₁ H≢□₁) A≤H H≢□ ⟩ → ⊥-elim (H≢□₁ refl)
-- lam 1
⊢a-dec (suc k) Γ (τ (A ⇒ B)) (ƛ e) (s≤s sz) with ⊢a-dec k (Γ , A) (τ B) e {!!}
... | yes ⟨ C , ⊢e ⟩ = yes ⟨ A ⇒ C , ⊢a-lam₁ ⊢e ⟩
... | no ¬p = no λ where
  ⟨ A ⇒ C , ⊢a-lam₁ ⊢e' ⟩ → ¬p ⟨ C , ⊢e' ⟩
-- lam false
⊢a-dec (suc k) Γ (τ (A & A₁)) (ƛ e) (s≤s sz) = no λ where
  ⟨ A , ⊢a-sub p-e (⊢a-sub p-e₁ ⊢e' A≤H₁ H≢□₁) A≤H H≢□ ⟩ → ⊥-elim (H≢□₁ refl)
⊢a-dec (suc k) Γ (τ τ⟦ x ↦ A ⟧) (ƛ e) (s≤s sz) = no λ where
  ⟨ A , ⊢a-sub p-e (⊢a-sub p-e₁ ⊢e' A≤H₁ H≢□₁) A≤H H≢□ ⟩ → ⊥-elim (H≢□₁ refl)
-- lam2
⊢a-dec (suc k) Γ (⟦ e' ⟧⇒ H) (ƛ e) (s≤s sz) with ⊢a-dec k Γ □ e' (sz-case-1 sz)
⊢a-dec (suc k) Γ (⟦ e' ⟧⇒ H) (ƛ e) (s≤s sz) | yes ⟨ A , ⊢e' ⟩ with ⊢a-dec k (Γ , A) (H ⇧ 0) e (sz-case-3 {e = e} {H = H} {e' = e'} sz)
... | yes ⟨ B , ⊢e'' ⟩ = yes ⟨ (A ⇒ B) , (⊢a-lam₂ ⊢e' ⊢e'') ⟩
... | no ¬p = no (inv-case-lam' ⊢e' ¬p)
⊢a-dec (suc k) Γ (⟦ e' ⟧⇒ H) (ƛ e) (s≤s sz) | no ¬p = no λ ih → inv-case-lam'' ¬p ih
-- lam-false
⊢a-dec k Γ (⌊ x ⌋⇒ H) (ƛ e) sz = no λ where
  ⟨ A , ⊢a-sub p-e (⊢a-sub p-e₁ ⊢e' A≤H₁ H≢□₁) A≤H H≢□ ⟩ → ⊥-elim (H≢□₁ refl)
-- app
⊢a-dec (suc k) Γ H (e₁ · e₂) (s≤s sz) with ⊢a-dec k Γ (⟦ e₂ ⟧⇒ H) e₁ (sz-case-2 sz)
... | yes ⟨ Int , ⊢e ⟩ = ⊥-elim (inv-case-app ⊢e ht-int)
... | yes ⟨ Float , ⊢e ⟩ = ⊥-elim (inv-case-app ⊢e ht-flt)
... | yes ⟨ Top , ⊢e ⟩ = ⊥-elim (inv-case-app ⊢e ht-top)
... | yes ⟨ A ⇒ B , ⊢e ⟩ = yes ⟨ B , (⊢a-app ⊢e) ⟩
... | yes ⟨ A & B , ⊢e ⟩ = ⊥-elim (inv-case-app ⊢e ht-and)
... | yes ⟨ τ⟦ x ↦ A ⟧ , ⊢e ⟩ = ⊥-elim (inv-case-app ⊢e ht-rcd)
... | no ¬p = no λ where
  ⟨ A' , ⊢a-app {A = A''} ⊢e' ⟩ → ¬p ⟨ A'' ⇒ A' , ⊢e' ⟩
-- ann
⊢a-dec (suc k) Γ H (e ⦂ A) (s≤s sz) with ⊢a-dec k Γ (τ A) e {!!} | ≤a-dec k Γ H A (m+n<o⇒n<o sz)
... | yes ⟨ A' , ⊢e' ⟩ | yes ⟨ B' , s ⟩ = yes ⟨ B' , subsumption-0 (⊢a-ann ⊢e') s ⟩
... | yes p | no ¬p  = no λ where
  ⟨ A' , ⊢a-ann ⊢e' ⟩ → ¬p ⟨ A , ≤a-□ ⟩
  ⟨ A' , ⊢a-sub p-e (⊢a-ann ⊢e') A≤H H≢□ ⟩ → ¬p ⟨ A' , A≤H ⟩
  ⟨ A' , ⊢a-sub p-e (⊢a-sub p-e₁ ⊢e' A≤H₁ H≢□₁) A≤H H≢□ ⟩ → ⊥-elim (H≢□₁ refl)
... | no ¬p | _      = no λ where
  ⟨ A' , ⊢a-ann {B = B} ⊢e' ⟩ → ¬p ⟨ B , ⊢e' ⟩
  ⟨ A' , ⊢a-sub p-e (⊢a-ann {B = B} ⊢e') A≤H H≢□ ⟩ → ¬p ⟨ B , ⊢e' ⟩
  ⟨ A' , ⊢a-sub p-e (⊢a-sub p-e₁ ⊢e' A≤H₁ H≢□₁) A≤H H≢□ ⟩ → ⊥-elim (H≢□₁ refl)
-- record
⊢a-dec k Γ H (𝕣 rs) sz = {!!}
-- proj
⊢a-dec (suc k) Γ H (e 𝕡 l) (s≤s sz) with ⊢a-dec k Γ (⌊ l ⌋⇒ H) e {!!}
... | yes ⟨ Int , ⊢e' ⟩ = ⊥-elim (inv-case-prj ⊢e' htr-int)
... | yes ⟨ Float , ⊢e' ⟩ = ⊥-elim (inv-case-prj ⊢e' htr-flt)
... | yes ⟨ Top , ⊢e' ⟩ = ⊥-elim (inv-case-prj ⊢e' htr-top)
... | yes ⟨ A' ⇒ A'' , ⊢e' ⟩ = ⊥-elim (inv-case-prj ⊢e' htr-arr)
... | yes ⟨ A' & A'' , ⊢e' ⟩ = ⊥-elim (inv-case-prj ⊢e' htr-and)
... | yes ⟨ τ⟦ x ↦ A' ⟧ , ⊢e' ⟩ = yes ⟨ A' , ⊢a-prj ⊢e' ⟩
... | no ¬p = no λ where
  ⟨ A'' , ⊢a-prj {l₂ = l'} ⊢e'' ⟩ → ¬p ⟨ τ⟦ l' ↦ A'' ⟧ , ⊢e'' ⟩

⊢r-dec k Γ rnil sz = yes ⟨ Top , ⊢a-nil ⟩
⊢r-dec (suc k) Γ (r⟦ l ↦ e ⟧ rs) (s≤s sz) = {!!}
{-
with ⊢a-dec k Γ □ e {!!} | ⊢r-dec k Γ rs {!!}
... | yes ⟨ A' , ⊢e' ⟩ | yes ⟨ A'' , ⊢r' ⟩ = yes ⟨ (τ⟦ l ↦ A' ⟧ & A'') , ⊢a-cons ⊢e' ⊢r' ⟩
-}
{-
⊢r-dec (suc k) Γ (r⟦ l ↦ e ⟧ rnil) (s≤s sz) with ⊢a-dec k Γ □ e {!!}
... | yes ⟨ A' , ⊢e' ⟩ = yes ⟨ τ⟦ l ↦ A' ⟧ , ⊢a-one ⊢e' ⟩
... | no ¬p = no λ where
  ⟨ (τ⟦ l ↦ A' ⟧) , ⊢a-one x ⟩ → ¬p ⟨ A' , x ⟩
  ⟨ (τ⟦ l ↦ A' ⟧ & _) , ⊢a-cons x ⊢e' ⟩ → ¬p ⟨ A' , x ⟩
⊢r-dec (suc k) Γ (r⟦ l₁ ↦ e₁ ⟧ r⟦ l₂ ↦ e₂ ⟧ rs) (s≤s sz) = {!!}
-}
