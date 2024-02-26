module Record.Algo.Decidable where

open import Record.Prelude hiding (_≤?_) renaming (_≤_ to _≤n_)
open import Record.Common
open import Record.Properties
open import Record.Algo
open import Record.Algo.Properties
open import Record.Algo.Sizes
open import Record.Algo.WellFormed
open import Record.Algo.Uniqueness
  
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
size-e (e ⦂ A) = 1 + size-e e
size-e (𝕣 rs) = 1 + size-r rs
size-e (e 𝕡 l) = 2 + size-e e

size-r rnil = 1
size-r (r⟦ l ↦ e ⟧ rs) = 1 + size-e e + size-r rs

size-H : Hint → ℕ
size-H □ = 0
size-H (τ A) = 0
size-H (⟦ e ⟧⇒ H) = 1 + size-e e + size-H H
size-H (⌊ l ⌋⇒ H) = 1 + size-H H -- unsure

-- have a extra def of size that tracks the size of type

size-H' : Hint → ℕ
size-H' □ = 0
size-H' (τ A) = size-t A
size-H' (⟦ e ⟧⇒ H) = 1 + size-e e + size-H' H
size-H' (⌊ l ⌋⇒ H) = 1 + size-H' H


size-↑ : ∀ e {n}
  → size-e e ≡ size-e (e ↑ n)

size-↑r : ∀ rs {n}
  → size-r rs ≡ size-r (rs ↑r n)

size-↑ (𝕔 x) {n} = refl
size-↑ (` x) {n} = refl
size-↑ (ƛ e) {n} rewrite size-↑ e {suc n} = refl
size-↑ (e₁ · e₂) {n} rewrite size-↑ e₁ {n} | size-↑ e₂ {n}  = refl
size-↑ (e ⦂ A) {n} rewrite size-↑ e {n} = refl
size-↑ (𝕣 rs) {n} rewrite size-↑r rs {n} = refl
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


≤a-dec : ∀ k Γ H A
  → WFG Γ → WFH H → WF A
  → size-H H < k
  → Dec (∃[ B ](Γ ⊢a A ≤ H ⇝ B))

≤a-dec' : ∀ k₁ k₂ Γ H A
  → WFG Γ → WFH H → WF A
  → size-H H < k₁
  → size-t A + size-H' H < k₂
  → Dec (∃[ B ](Γ ⊢a A ≤ H ⇝ B))

⊢a-dec : ∀ k Γ H e
  → WFG Γ → WFH H → WFE e
  → size-e e + size-H H < k
  → Dec (∃[ A ](Γ ⊢a H ⇛ e ⇛ A))

⊢r-dec : ∀ k Γ rs
  → WFG Γ → WFR rs
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

  sz-case-3 : ∀ {e H e' k}
    → suc (size-e e + suc (size-e e' + size-H H)) ≤n k
    → size-e e + size-H (H ⇧ 0) < k
  sz-case-3 {H = H} sz rewrite sym (size-⇧ H {0}) = sz-case-3' sz

  inv-case-lam' : ∀ {Γ e e' H A}
    → WFG Γ → WFE e → WFE e' → WFH H → WF A
    → Γ ⊢a □ ⇛ e' ⇛ A
    → ¬ (∃[ C ](Γ , A ⊢a H ⇧ 0 ⇛ e ⇛ C))
    → ¬ (∃[ D ](Γ ⊢a (⟦ e' ⟧⇒ H) ⇛ ƛ e ⇛ D))
  inv-case-lam' wfg wfe wfe' wfh wfA ⊢e ¬p ⟨ D ⇒ E , ⊢a-lam₂ ⊢e' ⊢e'' ⟩ with ⊢a-unique-0 wfg wfe' ⊢e ⊢e'
  ... | refl = ¬p ⟨ E , ⊢e'' ⟩

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

  data ¬& : Type → Set where
    ¬&-int : ¬& Int
    ¬&-flt : ¬& Float
    ¬&-top : ¬& Top
    ¬&-arr : ∀ {A B} → ¬& (A ⇒ B)
    ¬&-rcd : ∀ {l A} → ¬& (τ⟦ l ↦ A ⟧)

  data ¬&τ : Hint → Set where
--    ¬&τ-none : ¬&τ □
    ¬&τ-tau : ∀ {A} → ¬& A → ¬&τ (τ A)
    ¬&τ-hole : ∀ {e H} → ¬&τ (⟦ e ⟧⇒ H)
    ¬&τ-hole-l : ∀ {l H} → ¬&τ (⌊ l ⌋⇒ H)

  inv-and : ∀ {Γ A B C}
    → ¬& C
    → Γ ⊢a A & B ≤ τ C ⇝ C
    → (Γ ⊢a A ≤ τ C ⇝ C) ⊎ (Γ ⊢a B ≤ τ C ⇝ C)
  inv-and neq ≤a-top = inj₁ ≤a-top
  inv-and neq (≤a-and-l s x) = inj₁ s
  inv-and neq (≤a-and-r s x) = inj₂ s
  inv-and () (≤a-and s s₁)

  inv-sub-and : ∀ {Γ H A B C}
    → ¬&τ H
    → ¬ (∃[ A' ](Γ ⊢a A ≤ H ⇝ A'))
    → ¬ (∃[ B' ](Γ ⊢a B ≤ H ⇝ B'))
    → ¬ (Γ ⊢a A & B ≤ H ⇝ C)
  inv-sub-and H≢□ ¬p1 ¬p2 ≤a-top = ¬p1 ⟨ Top , ≤a-top ⟩
  inv-sub-and () ¬p1 ¬p2 ≤a-□
  inv-sub-and H≢□ ¬p1 ¬p2 (≤a-and-l {C = C} s x) = ¬p1 ⟨ C , s ⟩
  inv-sub-and H≢□ ¬p1 ¬p2 (≤a-and-r {C = C} s x) = ¬p2 ⟨ C , s ⟩
  inv-sub-and (¬&τ-tau ()) ¬p1 ¬p2 (≤a-and s s₁)

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

  inv-case-rcd : ∀ {A A' H rs Γ B'}
    → WFG Γ → WFR rs
    → Γ ⊢r □ ⇛ rs ⇛ A
    → Γ ⊢r □ ⇛ rs ⇛ A'
    → Γ ⊢a A ≤ H ⇝ B'
    → ¬ (∃[ C ](Γ ⊢a A' ≤ H ⇝ C))
    → ⊥
  inv-case-rcd {B' = B'} wfg wfr ⊢1 ⊢2 s ¬p with ⊢r-unique wfg wfh-□ wfr ⊢1 ⊢2
  ... | refl = ¬p ⟨ B' , s ⟩

    
≤a-dec k Γ H A wfg wfh wfA sz = ≤a-dec' k (suc (size-t A + size-H' H)) Γ H A wfg wfh wfA sz (s≤s m≤m)
-- H is and case, we exclude this case out
≤a-dec' (suc k₁) (suc k₂) Γ (τ (A & B)) C wfg (wfh-τ (wf-and wfA' wfB' A#B)) wfA (s≤s sz₁) (s≤s sz₂) with ≤a-dec' (suc k₁) k₂ Γ (τ A) C wfg (wfh-τ wfA') wfA (s≤s sz₁) (sz-case-6 sz₂)
                                                                 | ≤a-dec' (suc k₁) k₂ Γ (τ B) C wfg (wfh-τ wfB') wfA (s≤s sz₁) (sz-case-7 sz₂)
... | yes ⟨ A' , s1 ⟩ | yes ⟨ B' , s2 ⟩ = yes ⟨ (A' & B') , ≤a-and s1 s2 ⟩
... | yes p | no ¬p = no λ where
  ⟨ A' , s ⟩ → inv-case-and-r s ¬p
... | no ¬p | _ = no λ where
  ⟨ A' , s ⟩ → inv-case-and-l s ¬p
-- int
≤a-dec' (suc k₁) (suc k₂) Γ □ Int wfg wfh wfA (s≤s sz₁) (s≤s sz₂) = yes ⟨ Int , ≤a-□ ⟩
≤a-dec' (suc k₁) (suc k₂) Γ (τ Int) Int wfg wfh wfA (s≤s sz₁) (s≤s sz₂) = yes ⟨ Int , ≤a-int ⟩
≤a-dec' (suc k₁) (suc k₂) Γ (τ Float) Int wfg wfh wfA (s≤s sz₁) (s≤s sz₂) = no λ where
  ⟨ A' , () ⟩
≤a-dec' (suc k₁) (suc k₂) Γ (τ Top) Int wfg wfh wfA (s≤s sz₁) (s≤s sz₂) = yes ⟨ Top , ≤a-top ⟩
≤a-dec' (suc k₁) (suc k₂) Γ (τ (A ⇒ B)) Int wfg wfh wfA (s≤s sz₁) (s≤s sz₂) = no λ where
  ⟨ A' , () ⟩
≤a-dec' (suc k₁) (suc k₂) Γ (τ τ⟦ l ↦ A ⟧) Int wfg wfh wfA (s≤s sz₁) (s≤s sz₂) = no λ where
  ⟨ A' , () ⟩
≤a-dec' (suc k₁) (suc k₂) Γ (⟦ e ⟧⇒ H) Int wfg wfh wfA (s≤s sz₁) (s≤s sz₂) = no λ where
  ⟨ A' , () ⟩
≤a-dec' (suc k₁) (suc k₂) Γ (⌊ l ⌋⇒ H) Int wfg wfh wfA (s≤s sz₁) (s≤s sz₂) = no λ where
  ⟨ A' , () ⟩
-- float
≤a-dec' (suc k₁) (suc k₂) Γ □ Float wfg wfh wfA (s≤s sz₁) (s≤s sz₂) = yes ⟨ Float , ≤a-□ ⟩
≤a-dec' (suc k₁) (suc k₂) Γ (τ Int) Float wfg wfh wfA (s≤s sz₁) (s≤s sz₂) = no λ where
  ⟨ A' , () ⟩
≤a-dec' (suc k₁) (suc k₂) Γ (τ Float) Float wfg wfh wfA (s≤s sz₁) (s≤s sz₂) = yes ⟨ Float , ≤a-float ⟩
≤a-dec' (suc k₁) (suc k₂) Γ (τ Top) Float wfg wfh wfA (s≤s sz₁) (s≤s sz₂) = yes ⟨ Top , ≤a-top ⟩
≤a-dec' (suc k₁) (suc k₂) Γ (τ (A ⇒ B)) Float wfg wfh wfA (s≤s sz₁) (s≤s sz₂) = no λ where
  ⟨ A' , () ⟩
≤a-dec' (suc k₁) (suc k₂) Γ (τ τ⟦ l ↦ A ⟧) Float wfg wfh wfA (s≤s sz₁) (s≤s sz₂) = no λ where
  ⟨ A' , () ⟩
≤a-dec' (suc k₁) (suc k₂) Γ (⟦ e ⟧⇒ H) Float wfg wfh wfA (s≤s sz₁) (s≤s sz₂) = no λ where
  ⟨ A' , () ⟩
≤a-dec' (suc k₁) (suc k₂) Γ (⌊ l ⌋⇒ H) Float wfg wfh wfA (s≤s sz₁) (s≤s sz₂) = no λ where
  ⟨ A' , () ⟩
-- top
≤a-dec' (suc k₁) (suc k₂) Γ □ Top wfg wfh wfA (s≤s sz₁) (s≤s sz₂) = yes ⟨ Top , ≤a-□ ⟩
≤a-dec' (suc k₁) (suc k₂) Γ (τ Int) Top wfg wfh wfA (s≤s sz₁) (s≤s sz₂) = no λ where
  ⟨ A' , () ⟩
≤a-dec' (suc k₁) (suc k₂) Γ (τ Float) Top wfg wfh wfA (s≤s sz₁) (s≤s sz₂) = no λ where
  ⟨ A' , () ⟩
≤a-dec' (suc k₁) (suc k₂) Γ (τ Top) Top wfg wfh wfA (s≤s sz₁) (s≤s sz₂) = yes ⟨ Top , ≤a-top ⟩
≤a-dec' (suc k₁) (suc k₂) Γ (τ (x ⇒ x₁)) Top wfg wfh wfA (s≤s sz₁) (s≤s sz₂) = no λ where
  ⟨ A' , () ⟩
≤a-dec' (suc k₁) (suc k₂) Γ (τ τ⟦ l ↦ A ⟧) Top wfg wfh wfA (s≤s sz₁) (s≤s sz₂) = no λ where
  ⟨ A' , () ⟩
≤a-dec' (suc k₁) (suc k₂) Γ (⟦ x ⟧⇒ H) Top wfg wfh wfA (s≤s sz₁) (s≤s sz₂) = no λ where
  ⟨ A' , () ⟩
≤a-dec' (suc k₁) (suc k₂) Γ (⌊ x ⌋⇒ H) Top wfg wfh wfA (s≤s sz₁) (s≤s sz₂) = no λ where
  ⟨ A' , () ⟩
-- arrow
≤a-dec' (suc k₁) (suc k₂) Γ □ (A ⇒ B) wfg wfh wfA (s≤s sz₁) (s≤s sz₂) = yes ⟨ A ⇒ B , ≤a-□ ⟩
≤a-dec' (suc k₁) (suc k₂) Γ (τ Int) (A ⇒ B) wfg wfh wfA (s≤s sz₁) (s≤s sz₂) = no λ where
  ⟨ A' , () ⟩
≤a-dec' (suc k₁) (suc k₂) Γ (τ Float) (A ⇒ B) wfg wfh wfA (s≤s sz₁) (s≤s sz₂) = no λ where
  ⟨ A' , () ⟩
≤a-dec' (suc k₁) (suc k₂) Γ (τ Top) (A ⇒ B) wfg wfh wfA (s≤s sz₁) (s≤s sz₂) = yes ⟨ Top , ≤a-top ⟩
≤a-dec' (suc k₁) (suc k₂) Γ (τ (A' ⇒ B')) (A ⇒ B) wfg (wfh-τ (wf-arr wfA' wfB')) (wf-arr wfA wfB) (s≤s sz₁) (s≤s sz₂)
  with ≤a-dec' (suc k₁) k₂ Γ (τ A) A' wfg (wfh-τ wfA) wfA' (s≤s sz₁) (sz-case-8 (size-t A') (size-t A) sz₂)
     | ≤a-dec' (suc k₁) k₂ Γ (τ B') B wfg (wfh-τ wfB') wfB (s≤s sz₁) (sz-case-9 (size-t B) (size-t B') sz₂)
... | yes ⟨ C , s ⟩ | yes ⟨ D , s' ⟩ = yes ⟨ (A' ⇒ B') , (≤a-arr s s') ⟩
... | yes p | no ¬p = no λ where
  ⟨ C ⇒ D , ≤a-arr {D' = D'} s s₁ ⟩ → ¬p ⟨ D' , s₁ ⟩
... | no ¬p | _ =  no λ where
  ⟨ C ⇒ D , ≤a-arr {A' = A'} s s₁ ⟩ → ¬p ⟨ A' , s ⟩
≤a-dec' (suc k₁) (suc k₂) Γ (τ τ⟦ l ↦ A' ⟧) (A ⇒ B) wfg wfh wfA (s≤s sz₁) (s≤s sz₂) = no λ where
  ⟨ A' , () ⟩
≤a-dec' (suc k₁) (suc k₂) Γ (⟦ e ⟧⇒ H) (A ⇒ B) wfg (wfh-e wfh wfe ve) (wf-arr wfA wfB) (s≤s sz₁) (s≤s sz₂)
  with ≤a-dec' (suc k₁) k₂ Γ H B wfg wfh wfB (sz-case-10 sz₁) (sz-case-9 (size-t B) (size-H' H) sz₂)
     | ⊢a-dec k₁ Γ (τ A) e wfg (wfh-τ wfA) wfe (sz-case-11 sz₁)
... | yes ⟨ C , s ⟩ | yes ⟨ A' , ⊢e' ⟩ = yes ⟨ (A ⇒ C) , (≤a-hint ⊢e' s) ⟩
... | yes p | no ¬p = no λ where
  ⟨ A' ⇒ B' , ≤a-hint {C = C} x s ⟩ → ¬p ⟨ C , x ⟩
... | no ¬p | _ = no λ where
  ⟨ A' ⇒ B' , ≤a-hint x s ⟩ → ¬p ⟨ B' , s ⟩
≤a-dec' (suc k₁) (suc k₂) Γ (⌊ l ⌋⇒ H) (A ⇒ B) wfg wfh wfA (s≤s sz₁) (s≤s sz₂) = no λ where
  ⟨ A' , () ⟩
-- and, many repetitions here
≤a-dec' (suc k₁) (suc k₂) Γ □ (A & B) wfg wfh wfA (s≤s sz₁) (s≤s sz₂) = yes ⟨ A & B , ≤a-□ ⟩
≤a-dec' (suc k₁) (suc k₂) Γ H@(τ Int) (A & B) wfg wfh (wf-and wfA wfB A#B) (s≤s sz₁) (s≤s sz₂)
  with ≤a-dec' (suc k₁) k₂ Γ H A wfg (wfh-τ wf-int) wfA (s≤s sz₁) (sz-case-4 (size-t A) sz₂)
     | ≤a-dec' (suc k₁) k₂ Γ H B wfg (wfh-τ wf-int) wfB (s≤s sz₁) (sz-case-5 (size-t B) sz₂)
... | yes ⟨ A' , s ⟩ | _ = yes ⟨ A' , (≤a-and-l s λ ()) ⟩
... | no ¬p | yes ⟨ A' , s ⟩ = yes ⟨ A' , (≤a-and-r s λ ()) ⟩
... | no ¬p1 | no ¬p2 = no λ where
  ⟨ A' , s ⟩ → inv-sub-and (¬&τ-tau ¬&-int) ¬p1 ¬p2 s
≤a-dec' (suc k₁) (suc k₂) Γ H@(τ Float) (A & B) wfg wfh (wf-and wfA wfB A#B) (s≤s sz₁) (s≤s sz₂)
  with ≤a-dec' (suc k₁) k₂ Γ H A wfg (wfh-τ wf-float) wfA (s≤s sz₁) (sz-case-4 (size-t A) sz₂)
     | ≤a-dec' (suc k₁) k₂ Γ H B wfg (wfh-τ wf-float) wfB (s≤s sz₁) (sz-case-5 (size-t B) sz₂)
... | yes ⟨ A' , s ⟩ | _ = yes ⟨ A' , (≤a-and-l s λ ()) ⟩
... | no ¬p | yes ⟨ A' , s ⟩ = yes ⟨ A' , (≤a-and-r s λ ()) ⟩
... | no ¬p1 | no ¬p2 = no λ where
  ⟨ A' , s ⟩ → inv-sub-and (¬&τ-tau ¬&-flt) ¬p1 ¬p2 s
≤a-dec' (suc k₁) (suc k₂) Γ H@(τ Top) (A & B) wfg wfh (wf-and wfA wfB A#B) (s≤s sz₁) (s≤s sz₂)
  with ≤a-dec' (suc k₁) k₂ Γ H A wfg (wfh-τ wf-top) wfA (s≤s sz₁) (sz-case-4 (size-t A) sz₂)
     | ≤a-dec' (suc k₁) k₂ Γ H B wfg (wfh-τ wf-top) wfB (s≤s sz₁) (sz-case-5 (size-t B) sz₂)
... | yes ⟨ A' , s ⟩ | _ = yes ⟨ A' , (≤a-and-l s λ ()) ⟩
... | no ¬p | yes ⟨ A' , s ⟩ = yes ⟨ A' , (≤a-and-r s λ ()) ⟩
... | no ¬p1 | no ¬p2 = no λ where
  ⟨ A' , s ⟩ → inv-sub-and (¬&τ-tau ¬&-top) ¬p1 ¬p2 s
≤a-dec' (suc k₁) (suc k₂) Γ H@(τ (x ⇒ x₁)) (A & B) wfg wfh (wf-and wfA wfB A#B) (s≤s sz₁) (s≤s sz₂)
  with ≤a-dec' (suc k₁) k₂ Γ H A wfg wfh wfA (s≤s sz₁) (sz-case-4 (size-t A) sz₂)
     | ≤a-dec' (suc k₁) k₂ Γ H B wfg wfh wfB (s≤s sz₁) (sz-case-5 (size-t B) sz₂)
... | yes ⟨ A' , s ⟩ | _ = yes ⟨ A' , (≤a-and-l s λ ()) ⟩
... | no ¬p | yes ⟨ A' , s ⟩ = yes ⟨ A' , (≤a-and-r s λ ()) ⟩
... | no ¬p1 | no ¬p2 = no λ where
  ⟨ A' , s ⟩ → inv-sub-and (¬&τ-tau ¬&-arr) ¬p1 ¬p2 s
≤a-dec' (suc k₁) (suc k₂) Γ H@(τ τ⟦ x ↦ x₁ ⟧) (A & B) wfg wfh (wf-and wfA wfB A#B) (s≤s sz₁) (s≤s sz₂)
  with ≤a-dec' (suc k₁) k₂ Γ H A wfg wfh wfA (s≤s sz₁) (sz-case-4 (size-t A) sz₂)
     | ≤a-dec' (suc k₁) k₂ Γ H B wfg wfh wfB (s≤s sz₁) (sz-case-5 (size-t B) sz₂)
... | yes ⟨ A' , s ⟩ | _ = yes ⟨ A' , (≤a-and-l s λ ()) ⟩
... | no ¬p | yes ⟨ A' , s ⟩ = yes ⟨ A' , (≤a-and-r s λ ()) ⟩
... | no ¬p1 | no ¬p2 = no λ where
  ⟨ A' , s ⟩ → inv-sub-and (¬&τ-tau ¬&-rcd) ¬p1 ¬p2 s
≤a-dec' (suc k₁) (suc k₂) Γ H@(⟦ e ⟧⇒ H') (A & B) wfg wfh (wf-and wfA wfB A#B) (s≤s sz₁) (s≤s sz₂)
  with ≤a-dec' (suc k₁) k₂ Γ H A wfg wfh wfA (s≤s sz₁) (sz-case-4 (size-t A) sz₂)
     | ≤a-dec' (suc k₁) k₂ Γ H B wfg wfh wfB (s≤s sz₁) (sz-case-5 (size-t B) sz₂)
... | yes ⟨ A' , s ⟩ | _ = yes ⟨ A' , (≤a-and-l s λ ()) ⟩
... | no ¬p | yes ⟨ A' , s ⟩ = yes ⟨ A' , (≤a-and-r s λ ()) ⟩
... | no ¬p1 | no ¬p2 = no λ where
  ⟨ A' , s ⟩ → inv-sub-and ¬&τ-hole ¬p1 ¬p2 s
≤a-dec' (suc k₁) (suc k₂) Γ H@(⌊ l ⌋⇒ H') (A & B) wfg wfh (wf-and wfA wfB A#B) (s≤s sz₁) (s≤s sz₂)
  with ≤a-dec' (suc k₁) k₂ Γ H A wfg wfh wfA (s≤s sz₁) (sz-case-4 (size-t A) sz₂)
     | ≤a-dec' (suc k₁) k₂ Γ H B wfg wfh wfB (s≤s sz₁) (sz-case-5 (size-t B) sz₂)
... | yes ⟨ A' , s ⟩ | _ = yes ⟨ A' , (≤a-and-l s λ ()) ⟩
... | no ¬p | yes ⟨ A' , s ⟩ = yes ⟨ A' , (≤a-and-r s λ ()) ⟩
... | no ¬p1 | no ¬p2 = no λ where
  ⟨ A' , s ⟩ → inv-sub-and ¬&τ-hole-l ¬p1 ¬p2 s
{-
≤a-dec' (suc k₁) (suc k₂) Γ H (A & B) (s≤s sz₁) (s≤s sz₂) with □-dec H
                                                             | ≤a-dec' (suc k₁) k₂ Γ H A (s≤s sz₁) {!!}
                                                             | ≤a-dec' (suc k₁) k₂ Γ H B (s≤s sz₁) {!!}
... | yes p  | _ | _ rewrite p = yes ⟨ A & B , ≤a-□ ⟩
... | no H≢□ | yes ⟨ A' , s ⟩ | _ = yes ⟨ A' , (≤a-and-l s H≢□) ⟩
... | no H≢□ | no ¬p | yes ⟨ A' , s ⟩ = yes ⟨ A' , (≤a-and-r s H≢□) ⟩
... | no H≢□ | no ¬p1 | no ¬p2 = {!no!} -- it's doable
-}
-- rcd
≤a-dec' (suc k₁) (suc k₂) Γ □ τ⟦ l ↦ A ⟧ wfg wfh wfA (s≤s sz₁) (s≤s sz₂) = yes ⟨ τ⟦ l ↦ A ⟧ , ≤a-□ ⟩
≤a-dec' (suc k₁) (suc k₂) Γ (τ Int) τ⟦ l ↦ A ⟧ wfg wfh wfA (s≤s sz₁) (s≤s sz₂) = no λ where
  ⟨ A' , () ⟩  
≤a-dec' (suc k₁) (suc k₂) Γ (τ Float) τ⟦ l ↦ A ⟧ wfg wfh wfA (s≤s sz₁) (s≤s sz₂) = no λ where
  ⟨ A' , () ⟩  
≤a-dec' (suc k₁) (suc k₂) Γ (τ Top) τ⟦ l ↦ A ⟧ wfg wfh wfA (s≤s sz₁) (s≤s sz₂) = yes ⟨ Top , ≤a-top ⟩
≤a-dec' (suc k₁) (suc k₂) Γ (τ (x ⇒ x₁)) τ⟦ l ↦ A ⟧ wfg wfh wfA (s≤s sz₁) (s≤s sz₂) = no λ where
  ⟨ A' , () ⟩  
≤a-dec' (suc k₁) (suc k₂) Γ (τ τ⟦ l' ↦ A' ⟧) τ⟦ l ↦ A ⟧ wfg (wfh-τ (wf-rcd wfA')) (wf-rcd wfA) (s≤s sz₁) (s≤s sz₂)
  with l ≟ l' | ≤a-dec' (suc k₁) k₂ Γ (τ A') A wfg (wfh-τ wfA') wfA (s≤s sz₁) (sz-case-12 sz₂)
... | yes refl | yes ⟨ B , s ⟩ = yes ⟨ τ⟦ l ↦ B ⟧ , (≤a-rcd s) ⟩
... | yes refl | no ¬p = no λ where
  ⟨ (τ⟦ l' ↦ B ⟧) , ≤a-rcd s ⟩ → ¬p ⟨ B , s ⟩
... | no ¬p | _ = no λ where
  ⟨ (τ⟦ l' ↦ B ⟧) , ≤a-rcd s ⟩ → ¬p refl 
≤a-dec' (suc k₁) (suc k₂) Γ (⟦ e ⟧⇒ H) τ⟦ l ↦ A ⟧ wfg wfh wfA (s≤s sz₁) (s≤s sz₂) = no λ where
  ⟨ A' , () ⟩  
≤a-dec' (suc k₁) (suc k₂) Γ (⌊ l ⌋⇒ H) τ⟦ l' ↦ A ⟧ wfg (wfh-l wfh) (wf-rcd wfA) (s≤s sz₁) (s≤s sz₂)
  with l ≟ l' | ≤a-dec' (suc k₁) k₂ Γ H A wfg wfh wfA (s≤s (≤-trans (m≤n+m (size-H H) 1) sz₁)) (sz-case-13 sz₂)
... | yes refl | yes ⟨ B , s ⟩ = yes ⟨ τ⟦ l ↦ B ⟧ , (≤a-hint-l s) ⟩
... | yes refl | no ¬p = no λ where
  ⟨ (τ⟦ l' ↦ B ⟧) , ≤a-hint-l s ⟩ → ¬p ⟨ B , s ⟩
... | no ¬p | _ = no λ where
  ⟨ (τ⟦ l' ↦ B ⟧) , ≤a-hint-l s ⟩ → ¬p refl 

-- const
⊢a-dec (suc k) Γ H (𝕔 c) wfg wfh wfe (s≤s sz) with ≤a-dec k Γ H (c-τ c) wfg wfh (wf-c c) sz
... | yes ⟨ A' , s ⟩ = yes ⟨ A' , (subsumption-0 ⊢a-c s) ⟩
... | no ¬p = no λ where
  ⟨ A , ⊢e' ⟩ → inv-case-const ¬p ⊢e'
-- var
⊢a-dec (suc k) Γ H (` x) wfg wfh wfe (s≤s sz) with x∈Γ-dec Γ x
⊢a-dec (suc k) Γ H (` x) wfg wfh wfe (s≤s sz) | yes ⟨ A , x∈Γ ⟩ with ≤a-dec k Γ H A wfg wfh (x∈Γ-wf wfg x∈Γ) sz
... | yes ⟨ A' , s ⟩ = yes ⟨ A' , subsumption-0 (⊢a-var x∈Γ) s ⟩
... | no ¬p = no λ where
  ⟨ A , ⊢e' ⟩ → inv-case-var ¬p x∈Γ ⊢e'
⊢a-dec (suc k) Γ H (` x) wfg wfh wfe (s≤s sz) | no ¬p = no λ where
  ⟨ A , ⊢e ⟩ → inv-case-var' ⊢e ¬p
-- lam
⊢a-dec k Γ □ (ƛ e) wfg wfh wfe sz = no λ where
  ⟨ A , ⊢a-sub p-e ⊢e' A≤H H≢□ ⟩ → ⊥-elim (H≢□ refl)
-- lam false
⊢a-dec (suc k) Γ (τ Int) (ƛ e) wfg wfh wfe (s≤s sz) = no λ where
  ⟨ A , ⊢a-sub p-e (⊢a-sub p-e₁ ⊢e' A≤H₁ H≢□₁) A≤H H≢□ ⟩ → ⊥-elim (H≢□₁ refl)
⊢a-dec (suc k) Γ (τ Float) (ƛ e) wfg wfh wfe (s≤s sz) = no λ where
  ⟨ A , ⊢a-sub p-e (⊢a-sub p-e₁ ⊢e' A≤H₁ H≢□₁) A≤H H≢□ ⟩ → ⊥-elim (H≢□₁ refl)
⊢a-dec (suc k) Γ (τ Top) (ƛ e) wfg wfh wfe (s≤s sz) = no λ where
  ⟨ A , ⊢a-sub p-e (⊢a-sub p-e₁ ⊢e' A≤H₁ H≢□₁) A≤H H≢□ ⟩ → ⊥-elim (H≢□₁ refl)
-- lam 1
⊢a-dec (suc k) Γ (τ (A ⇒ B)) (ƛ e) wfg (wfh-τ (wf-arr wfA wfB)) (wfe-lam wfe) (s≤s sz)
  with ⊢a-dec k (Γ , A) (τ B) e (wfg-, wfg wfA) (wfh-τ wfB) wfe sz
... | yes ⟨ C , ⊢e ⟩ = yes ⟨ A ⇒ C , ⊢a-lam₁ ⊢e ⟩
... | no ¬p = no λ where
  ⟨ A ⇒ C , ⊢a-lam₁ ⊢e' ⟩ → ¬p ⟨ C , ⊢e' ⟩
-- lam false
⊢a-dec (suc k) Γ (τ (A & A₁)) (ƛ e) wfg wfh wfe (s≤s sz) = no λ where
  ⟨ A , ⊢a-sub p-e (⊢a-sub p-e₁ ⊢e' A≤H₁ H≢□₁) A≤H H≢□ ⟩ → ⊥-elim (H≢□₁ refl)
⊢a-dec (suc k) Γ (τ τ⟦ x ↦ A ⟧) (ƛ e) wfg wfh wfe (s≤s sz) = no λ where
  ⟨ A , ⊢a-sub p-e (⊢a-sub p-e₁ ⊢e' A≤H₁ H≢□₁) A≤H H≢□ ⟩ → ⊥-elim (H≢□₁ refl)
-- lam2
⊢a-dec (suc k) Γ (⟦ e' ⟧⇒ H) (ƛ e) wfg (wfh-e wfh wfe' ve) (wfe-lam wfe) (s≤s sz) with ⊢a-dec k Γ □ e' wfg wfh-□ wfe' (sz-case-1 sz)
⊢a-dec (suc k) Γ (⟦ e' ⟧⇒ H) (ƛ e) wfg (wfh-e wfh wfe' ve) (wfe-lam wfe) (s≤s sz) | yes ⟨ A , ⊢e' ⟩
  with ⊢a-dec k (Γ , A) (H ⇧ 0) e (wfg-, wfg (⊢a-wf wfg wfh-□ wfe' ⊢e')) (wf-⇧ wfh) wfe (sz-case-3 {e = e} {H = H} {e' = e'} sz)
... | yes ⟨ B , ⊢e'' ⟩ = yes ⟨ (A ⇒ B) , (⊢a-lam₂ ⊢e' ⊢e'') ⟩
... | no ¬p = no (inv-case-lam' wfg wfe wfe' wfh ((⊢a-wf wfg wfh-□ wfe' ⊢e')) ⊢e' ¬p)
⊢a-dec (suc k) Γ (⟦ e' ⟧⇒ H) (ƛ e) wfg wfh wfe (s≤s sz) | no ¬p = no λ ih → inv-case-lam'' ¬p ih
-- lam-false
⊢a-dec k Γ (⌊ x ⌋⇒ H) (ƛ e) wfg wfh wfe sz = no λ where
  ⟨ A , ⊢a-sub p-e (⊢a-sub p-e₁ ⊢e' A≤H₁ H≢□₁) A≤H H≢□ ⟩ → ⊥-elim (H≢□₁ refl)
-- app
⊢a-dec (suc k) Γ H (e₁ · e₂) wfg wfh (wfe-app wfe1 wfe2 ve) (s≤s sz) with ⊢a-dec k Γ (⟦ e₂ ⟧⇒ H) e₁ wfg (wfh-e wfh wfe2 ve) wfe1 (sz-case-2 sz)
... | yes ⟨ Int , ⊢e ⟩ = ⊥-elim (inv-case-app ⊢e ht-int)
... | yes ⟨ Float , ⊢e ⟩ = ⊥-elim (inv-case-app ⊢e ht-flt)
... | yes ⟨ Top , ⊢e ⟩ = ⊥-elim (inv-case-app ⊢e ht-top)
... | yes ⟨ A ⇒ B , ⊢e ⟩ = yes ⟨ B , (⊢a-app ⊢e) ⟩
... | yes ⟨ A & B , ⊢e ⟩ = ⊥-elim (inv-case-app ⊢e ht-and)
... | yes ⟨ τ⟦ x ↦ A ⟧ , ⊢e ⟩ = ⊥-elim (inv-case-app ⊢e ht-rcd)
... | no ¬p = no λ where
  ⟨ A' , ⊢a-app {A = A''} ⊢e' ⟩ → ¬p ⟨ A'' ⇒ A' , ⊢e' ⟩
-- ann
⊢a-dec (suc k) Γ H (e ⦂ A) wfg wfh (wfe-ann wfe wfA) (s≤s sz)
  with ⊢a-dec k Γ (τ A) e wfg (wfh-τ wfA) wfe (sz-case-11 sz)
     | ≤a-dec k Γ H A wfg wfh wfA (m+n<o⇒n<o sz)
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
⊢a-dec (suc k) Γ H (𝕣 rs) wfg wfh (wfe-rcd wfr) (s≤s sz) with ⊢r-dec k Γ rs wfg wfr (≤-trans (s≤s (m≤m+n (size-r rs) (size-H H))) sz)
⊢a-dec (suc k) Γ H (𝕣 rs) wfg wfh (wfe-rcd wfr) (s≤s sz) | yes ⟨ A' , ⊢r' ⟩
  with ≤a-dec k Γ H A' wfg wfh (⊢r-wf wfg wfh-□ wfr ⊢r') (≤-trans (s≤s (m≤n+m (size-H H) (size-r rs))) sz)
... | yes ⟨ B' , s ⟩ = yes ⟨ B' , (subsumption-0 (⊢a-rcd ⊢r') s) ⟩
... | no ¬p = no λ where
  ⟨ B' , ⊢a-sub p-e (⊢a-sub p-e₁ ⊢e A≤H₁ H≢□₁) A≤H H≢□ ⟩ → ⊥-elim (H≢□₁ refl)
  ⟨ B' , ⊢a-sub p-e (⊢a-rcd x) A≤H H≢□ ⟩ → inv-case-rcd wfg wfr x ⊢r' A≤H ¬p
  ⟨ B' , ⊢a-rcd x ⟩ → ¬p ⟨ A' , ≤a-□ ⟩
⊢a-dec (suc k) Γ H (𝕣 rs) wfg wfh wfe (s≤s sz) | no ¬p = no λ where
  ⟨ B' , ⊢a-sub p-e (⊢a-sub p-e₁ ⊢e A≤H₁ H≢□₁) A≤H H≢□ ⟩ → ⊥-elim (H≢□₁ refl)
  ⟨ B' , ⊢a-sub p-e (⊢a-rcd {A = A} x) A≤H H≢□ ⟩ → ¬p ⟨ A , x ⟩
  ⟨ B' , ⊢a-rcd x ⟩ → ¬p ⟨ B' , x ⟩
-- proj
⊢a-dec (suc k) Γ H (e 𝕡 l) wfg wfh (wfe-prj wfe) (s≤s sz) with ⊢a-dec k Γ (⌊ l ⌋⇒ H) e wfg (wfh-l wfh) wfe (sz-case-14 sz)
... | yes ⟨ Int , ⊢e' ⟩ = ⊥-elim (inv-case-prj ⊢e' htr-int)
... | yes ⟨ Float , ⊢e' ⟩ = ⊥-elim (inv-case-prj ⊢e' htr-flt)
... | yes ⟨ Top , ⊢e' ⟩ = ⊥-elim (inv-case-prj ⊢e' htr-top)
... | yes ⟨ A' ⇒ A'' , ⊢e' ⟩ = ⊥-elim (inv-case-prj ⊢e' htr-arr)
... | yes ⟨ A' & A'' , ⊢e' ⟩ = ⊥-elim (inv-case-prj ⊢e' htr-and)
... | yes ⟨ τ⟦ x ↦ A' ⟧ , ⊢e' ⟩ = yes ⟨ A' , ⊢a-prj ⊢e' ⟩
... | no ¬p = no λ where
  ⟨ A'' , ⊢a-prj {l₂ = l'} ⊢e'' ⟩ → ¬p ⟨ τ⟦ l' ↦ A'' ⟧ , ⊢e'' ⟩

⊢r-dec k Γ rnil wfg wfr sz = yes ⟨ Top , ⊢a-nil ⟩
⊢r-dec (suc k) Γ (r⟦ l ↦ e ⟧ rnil) wfg (wfr-cons wfe wfr l∉rs) (s≤s sz)
  with ⊢a-dec k Γ □ e wfg wfh-□ wfe (sz-case-15 sz)
... | yes ⟨ A' , ⊢e' ⟩ = yes ⟨ τ⟦ l ↦ A' ⟧ , ⊢a-one ⊢e' ⟩
... | no ¬p = no λ where
  ⟨ (τ⟦ l ↦ A' ⟧) , ⊢a-one x ⟩ → ¬p ⟨ A' , x ⟩
  ⟨ (τ⟦ l ↦ A' ⟧ & _) , ⊢a-cons x ⊢e' rs≢ ⟩ → ¬p ⟨ A' , x ⟩
⊢r-dec (suc k) Γ (r⟦ l₁ ↦ e₁ ⟧ rs'@(r⟦ l₂ ↦ e₂ ⟧ rs)) wfg (wfr-cons wfe1 (wfr-cons wfe2 wfr l∉rs') l∉rs) (s≤s sz)
  with ⊢a-dec k Γ □ e₁ wfg wfh-□ wfe1 (sz-case-16 (size-e e₁) (size-e e₂) sz)
     | ⊢r-dec k Γ rs' wfg ((wfr-cons wfe2 wfr l∉rs')) (sz-case-17 {n = size-e e₂} sz)
... | yes ⟨ A' , ⊢e' ⟩ | yes ⟨ B' , ⊢r' ⟩ = yes ⟨ (τ⟦ l₁ ↦ A' ⟧ & B') , (⊢a-cons ⊢e' ⊢r' (λ ())) ⟩
... | yes ⟨ A' , ⊢e' ⟩ | no ¬p = no λ where
  ⟨ τ⟦ l₁ ↦ _ ⟧ & B' , ⊢a-cons x ⊢r' x₁ ⟩ → ¬p ⟨ B' , ⊢r' ⟩
... | no ¬p | _ = no λ where
  ⟨ τ⟦ l₁ ↦ A' ⟧ & _ , ⊢a-cons x ⊢r' x₁ ⟩ → ¬p ⟨ A' , x ⟩
