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
size-t (A `→ B) = 1 + size-t A + size-t B
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

size-Σ : Context → ℕ
size-Σ □ = 0
size-Σ (τ A) = 0
size-Σ (⟦ e ⟧⇒ Σ) = 1 + size-e e + size-Σ Σ
size-Σ (⌊ l ⌋⇒ Σ) = 1 + size-Σ Σ -- unsure

-- have a extra def of size that tracks the size of type

size-Σ' : Context → ℕ
size-Σ' □ = 0
size-Σ' (τ A) = size-t A
size-Σ' (⟦ e ⟧⇒ Σ) = 1 + size-e e + size-Σ' Σ
size-Σ' (⌊ l ⌋⇒ Σ) = 1 + size-Σ' Σ


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

size-⇧ : ∀ Σ {n}
  → size-Σ Σ ≡ size-Σ (Σ ⇧ n)
size-⇧ □ = refl
size-⇧ (τ _) = refl
size-⇧ (⟦ e ⟧⇒ Σ) {n} rewrite size-⇧ Σ {n} | size-↑ e {n} = refl
size-⇧ (⌊ x ⌋⇒ Σ) {n} rewrite size-⇧ Σ {n} = refl

x∈Γ-dec : ∀ Γ n
  → Dec (∃[ A ] (Γ ∋ n ⦂ A))
x∈Γ-dec ∅ n = no λ ()
x∈Γ-dec (Γ , A) zero = yes ⟨ A , Z ⟩
x∈Γ-dec (Γ , A) (suc n) with x∈Γ-dec Γ n
... | yes ⟨ A' , x∈Γ ⟩ = yes ⟨ A' , S x∈Γ ⟩
... | no ¬p = no λ where
  ⟨ A' , S x∈Γ ⟩ → ¬p ⟨ A' , x∈Γ ⟩


≤dec : ∀ k Γ Σ A
  → WFG Γ → WFΣ Σ → WF A
  → size-Σ Σ < k
  → Dec (∃[ B ](Γ ⊢ A ≤ Σ ⇝ B))

≤dec' : ∀ k₁ k₂ Γ Σ A
  → WFG Γ → WFΣ Σ → WF A
  → size-Σ Σ < k₁
  → size-t A + size-Σ' Σ < k₂
  → Dec (∃[ B ](Γ ⊢ A ≤ Σ ⇝ B))

≤dec-0 : ∀ Γ Σ A
  → WFG Γ → WFΣ Σ → WF A
  → Dec (∃[ B ](Γ ⊢ A ≤ Σ ⇝ B))
≤dec-0 Γ Σ A wfΓ wfΣ wfA = ≤dec (suc (size-Σ Σ)) Γ Σ A wfΓ wfΣ wfA (s≤s m≤m)

⊢dec : ∀ k Γ Σ e
  → WFG Γ → WFΣ Σ → WFE e
  → size-e e + size-Σ Σ < k
  → Dec (∃[ A ](Γ ⊢ Σ ⇒ e ⇒ A))

⊢dec-0 : ∀ {Γ Σ e}
  → WFG Γ → WFΣ Σ → WFE e
  → Dec (∃[ A ](Γ ⊢ Σ ⇒ e ⇒ A))
⊢dec-0 {Γ} {Σ} {e} wfg wfh wfe = ⊢dec (suc (size-e e + size-Σ Σ)) Γ Σ e wfg wfh wfe (s≤s m≤m)

⊢r-dec : ∀ k Γ rs
  → WFG Γ → WFR rs
  → size-r rs < k
  → Dec (∃[ A ](Γ ⊢r □ ⇒ rs ⇒ A))


private
  inv-case-const : ∀ {Γ Σ c A}
    → ¬ (∃[ A' ](Γ ⊢ (c-τ c) ≤ Σ ⇝ A'))
    → Γ ⊢ Σ ⇒ 𝕔 c ⇒ A
    → ⊥
  inv-case-const {c = c} ¬p ⊢c = ¬p ⟨ c-τ c , ≤□ ⟩
  inv-case-const {A = A} ¬p (⊢sub x ⊢c x₁ Σ≢□) = ¬p ⟨ A , x₁ ⟩
  inv-case-const ¬p (⊢sub x (⊢sub x₂ ⊢e x₃ Σ≢□₁) x₁ Σ≢□) = ⊥-elim (Σ≢□₁ refl)
  
  inv-case-var : ∀ {Γ Σ x A A₁}
    → ¬ (∃[ A' ](Γ ⊢ A₁ ≤ Σ ⇝ A'))
    → Γ ∋ x ⦂ A₁
    → Γ ⊢ Σ ⇒ ` x ⇒ A
    → ⊥
  inv-case-var {A₁ = A₁} ¬p x∈Γ (⊢var x∈Γ') rewrite sym (x∈Γ-unique x∈Γ x∈Γ') = ¬p ⟨ A₁ , ≤□ ⟩
  inv-case-var {A = A} ¬p x∈Γ (⊢sub x (⊢var x∈Γ') x₁ Σ≢□) rewrite sym (x∈Γ-unique x∈Γ x∈Γ') = ¬p ⟨ A , x₁ ⟩
  inv-case-var ¬p x∈Γ (⊢sub x (⊢sub x₂ ⊢e x₃ Σ≢□₁) x₁ Σ≢□) = ⊥-elim (Σ≢□₁ refl)
  
  inv-case-var' : ∀ {Γ Σ x A}
    → Γ ⊢ Σ ⇒ ` x ⇒ A
    → ¬ (∃[ B ](Γ ∋ x ⦂ B))
    → ⊥
  inv-case-var' {A = A} (⊢var x∈Γ) ¬p = ¬p ⟨ A , x∈Γ ⟩
  inv-case-var' (⊢sub p-e (⊢var {A = A₁} x∈Γ) A≤Σ Σ≢□) ¬p = ¬p ⟨ A₁ , x∈Γ ⟩
  inv-case-var' {A = A} (⊢sub p-e (⊢sub p-e₁ ⊢e A≤Σ₁ Σ≢□₁) A≤Σ Σ≢□) ¬p = ⊥-elim (Σ≢□₁ refl)

  sz-case-3 : ∀ {e Σ e' k}
    → suc (size-e e + suc (size-e e' + size-Σ Σ)) ≤n k
    → size-e e + size-Σ (Σ ⇧ 0) < k
  sz-case-3 {Σ = Σ} sz rewrite sym (size-⇧ Σ {0}) = sz-case-3' sz

  inv-case-lam' : ∀ {Γ e e' Σ A}
    → WFG Γ → WFE e → WFE e' → WFΣ Σ → WF A
    → Γ ⊢ □ ⇒ e' ⇒ A
    → ¬ (∃[ C ](Γ , A ⊢ Σ ⇧ 0 ⇒ e ⇒ C))
    → ¬ (∃[ D ](Γ ⊢ (⟦ e' ⟧⇒ Σ) ⇒ ƛ e ⇒ D))
  inv-case-lam' wfg wfe wfe' wfh wfA ⊢e ¬p ⟨ D `→ E , ⊢lam₂ ⊢e' ⊢e'' ⟩ with ⊢unique-0 wfg wfe' ⊢e ⊢e'
  ... | refl = ¬p ⟨ E , ⊢e'' ⟩

  inv-case-lam'' : ∀ {Γ e' e Σ}
    → ¬ (∃[ C ](Γ ⊢ □ ⇒ e' ⇒ C))
    → ∃[ D ](Γ ⊢ ⟦ e' ⟧⇒ Σ ⇒ ƛ e ⇒ D)
    → ⊥
  inv-case-lam'' ¬p ⟨ A `→ B , ⊢lam₂ ⊢e ⊢e₁ ⟩ = ¬p ⟨ A , ⊢e ⟩

  data ΣoType : Type → Set where
    ht-int : ΣoType Int
    ht-flt : ΣoType Float
    ht-top : ΣoType Top
    ht-and : ∀ {A B} → ΣoType (A & B)
    ht-rcd : ∀ {l A} → ΣoType τ⟦ l ↦ A ⟧

  inv-case-sub-hole : ∀ {Γ A Σ A' e Σ' B C}
    → Γ ⊢ A ≤ Σ ⇝ A'
    → Σ ≡ ⟦ e ⟧⇒ Σ'
    → A' ≡ B & C
    → ⊥
  inv-case-sub-hole (≤and-l A≤Σ x) refl refl = inv-case-sub-hole A≤Σ refl refl
  inv-case-sub-hole (≤and-r A≤Σ x) refl refl = inv-case-sub-hole A≤Σ refl refl

  inv-case-app : ∀ {Γ Σ e₁ e₂ A}
    → Γ ⊢ ⟦ e₂ ⟧⇒ Σ ⇒ e₁ ⇒ A
    → ΣoType A
    → ⊥
  inv-case-app {A = Int} ⊢e neq with ⊢to-≤ ⊢e
  ... | ()
  inv-case-app {A = Float} ⊢e neq with ⊢to-≤ ⊢e
  ... | ()
  inv-case-app {A = Top} ⊢e neq with ⊢to-≤ ⊢e
  ... | ()
  inv-case-app {A = A & B} ⊢e neq with ⊢to-≤ ⊢e
  ... | r = inv-case-sub-hole r refl refl
  inv-case-app {A = τ⟦ x ↦ A ⟧} ⊢e neq  with ⊢to-≤ ⊢e
  ... | ()

  data ΣoTypeRcd : Type → Set where
    htr-int : ΣoTypeRcd Int
    htr-flt : ΣoTypeRcd Float
    htr-top : ΣoTypeRcd Top
    htr-and : ∀ {A B} → ΣoTypeRcd (A & B)
    htr-arr : ∀ {A B} → ΣoTypeRcd (A `→ B)

  inv-case-sub-hole-prj : ∀ {Γ A Σ A' e Σ' B C}
    → Γ ⊢ A ≤ Σ ⇝ A'
    → Σ ≡ ⌊ e ⌋⇒ Σ'
    → A' ≡ B & C
    → ⊥
  inv-case-sub-hole-prj (≤and-l A≤Σ x) refl refl = inv-case-sub-hole-prj A≤Σ refl refl
  inv-case-sub-hole-prj (≤and-r A≤Σ x) refl refl = inv-case-sub-hole-prj A≤Σ refl refl

  inv-case-prj : ∀ {Γ Σ e l A}
    → Γ ⊢ ⌊ l ⌋⇒ Σ ⇒ e ⇒ A
    → ΣoTypeRcd A
    → ⊥
  inv-case-prj {A = Int} ⊢e neq with ⊢to-≤ ⊢e
  ... | ()
  inv-case-prj {A = Float} ⊢e neq with ⊢to-≤ ⊢e
  ... | ()
  inv-case-prj {A = Top} ⊢e neq with ⊢to-≤ ⊢e
  ... | ()
  inv-case-prj {A = A & B} ⊢e neq with ⊢to-≤ ⊢e
  ... | r = inv-case-sub-hole-prj r refl refl
  inv-case-prj {A = A `→ B⟧} ⊢e neq  with ⊢to-≤ ⊢e
  ... | ()

  data ¬& : Type → Set where
    ¬&-int : ¬& Int
    ¬&-flt : ¬& Float
    ¬&-top : ¬& Top
    ¬&-arr : ∀ {A B} → ¬& (A `→ B)
    ¬&-rcd : ∀ {l A} → ¬& (τ⟦ l ↦ A ⟧)

  data ¬&τ : Context → Set where
--    ¬&τ-none : ¬&τ □
    ¬&τ-tau : ∀ {A} → ¬& A → ¬&τ (τ A)
    ¬&τ-hole : ∀ {e Σ} → ¬&τ (⟦ e ⟧⇒ Σ)
    ¬&τ-hole-l : ∀ {l Σ} → ¬&τ (⌊ l ⌋⇒ Σ)

  inv-and : ∀ {Γ A B C}
    → ¬& C
    → Γ ⊢ A & B ≤ τ C ⇝ C
    → (Γ ⊢ A ≤ τ C ⇝ C) ⊎ (Γ ⊢ B ≤ τ C ⇝ C)
  inv-and neq ≤top = inj₁ ≤top
  inv-and neq (≤and-l s x) = inj₁ s
  inv-and neq (≤and-r s x) = inj₂ s
  inv-and () (≤and s s₁)

  inv-sub-and : ∀ {Γ Σ A B C}
    → ¬&τ Σ
    → ¬ (∃[ A' ](Γ ⊢ A ≤ Σ ⇝ A'))
    → ¬ (∃[ B' ](Γ ⊢ B ≤ Σ ⇝ B'))
    → ¬ (Γ ⊢ A & B ≤ Σ ⇝ C)
  inv-sub-and Σ≢□ ¬p1 ¬p2 ≤top = ¬p1 ⟨ Top , ≤top ⟩
  inv-sub-and () ¬p1 ¬p2 ≤□
  inv-sub-and Σ≢□ ¬p1 ¬p2 (≤and-l {C = C} s x) = ¬p1 ⟨ C , s ⟩
  inv-sub-and Σ≢□ ¬p1 ¬p2 (≤and-r {C = C} s x) = ¬p2 ⟨ C , s ⟩
  inv-sub-and (¬&τ-tau ()) ¬p1 ¬p2 (≤and s s₁)

  sub-inv-and-r : ∀ {Γ A B C D}
    → Γ ⊢ C ≤ τ (A & B) ⇝ D
    → (Γ ⊢ C ≤ τ A ⇝ A) × (Γ ⊢ C ≤ τ B ⇝ B)
  sub-inv-and-r (≤and-l s x) with sub-inv-and-r s
  ... | ⟨ s1 , s2 ⟩ = ⟨ (≤and-l s1 (λ ())) , (≤and-l s2 (λ ())) ⟩
  sub-inv-and-r (≤and-r s x) with sub-inv-and-r s
  ... | ⟨ s1 , s2 ⟩ = ⟨ (≤and-r s1 (λ ())) , (≤and-r s2 (λ ())) ⟩
  sub-inv-and-r (≤and s s₁) = ⟨ ≤rigid s , ≤rigid s₁ ⟩

  inv-case-and-r : ∀ {Γ A B C A'}
    → Γ ⊢ C ≤ τ (A & B) ⇝ A'
    → ¬ (∃[ B' ](Γ ⊢ C ≤ τ B ⇝ B'))
    → ⊥
  inv-case-and-r {B = B} ⊢e ¬p with sub-inv-and-r ⊢e
  ... | ⟨ l , r ⟩ = ¬p ⟨ B , r ⟩

  inv-case-and-l : ∀ {Γ A B C A'}
    → Γ ⊢ C ≤ τ (A & B) ⇝ A'
    → ¬ (∃[ A' ](Γ ⊢ C ≤ τ A ⇝ A'))
    → ⊥
  inv-case-and-l {A = A} ⊢e ¬p with sub-inv-and-r ⊢e
  ... | ⟨ l , r ⟩ = ¬p ⟨ A , l ⟩

  inv-case-rcd : ∀ {A A' Σ rs Γ B'}
    → WFG Γ → WFR rs
    → Γ ⊢r □ ⇒ rs ⇒ A
    → Γ ⊢r □ ⇒ rs ⇒ A'
    → Γ ⊢ A ≤ Σ ⇝ B'
    → ¬ (∃[ C ](Γ ⊢ A' ≤ Σ ⇝ C))
    → ⊥
  inv-case-rcd {B' = B'} wfg wfr ⊢1 ⊢2 s ¬p with ⊢r-unique wfg wfh-□ wfr ⊢1 ⊢2
  ... | refl = ¬p ⟨ B' , s ⟩

    
≤dec k Γ Σ A wfg wfh wfA sz = ≤dec' k (suc (size-t A + size-Σ' Σ)) Γ Σ A wfg wfh wfA sz (s≤s m≤m)
-- Σ is and case, we exclude this case out
≤dec' (suc k₁) (suc k₂) Γ (τ (A & B)) C wfg (wfh-τ (wf-and wfA' wfB' A#B)) wfA (s≤s sz₁) (s≤s sz₂) with ≤dec' (suc k₁) k₂ Γ (τ A) C wfg (wfh-τ wfA') wfA (s≤s sz₁) (sz-case-6 sz₂)
                                                                 | ≤dec' (suc k₁) k₂ Γ (τ B) C wfg (wfh-τ wfB') wfA (s≤s sz₁) (sz-case-7 sz₂)
... | yes ⟨ A' , s1 ⟩ | yes ⟨ B' , s2 ⟩ = yes ⟨ (A' & B') , ≤and s1 s2 ⟩
... | yes p | no ¬p = no λ where
  ⟨ A' , s ⟩ → inv-case-and-r s ¬p
... | no ¬p | _ = no λ where
  ⟨ A' , s ⟩ → inv-case-and-l s ¬p
-- int
≤dec' (suc k₁) (suc k₂) Γ □ Int wfg wfh wfA (s≤s sz₁) (s≤s sz₂) = yes ⟨ Int , ≤□ ⟩
≤dec' (suc k₁) (suc k₂) Γ (τ Int) Int wfg wfh wfA (s≤s sz₁) (s≤s sz₂) = yes ⟨ Int , ≤int ⟩
≤dec' (suc k₁) (suc k₂) Γ (τ Float) Int wfg wfh wfA (s≤s sz₁) (s≤s sz₂) = no λ where
  ⟨ A' , () ⟩
≤dec' (suc k₁) (suc k₂) Γ (τ Top) Int wfg wfh wfA (s≤s sz₁) (s≤s sz₂) = yes ⟨ Top , ≤top ⟩
≤dec' (suc k₁) (suc k₂) Γ (τ (A `→ B)) Int wfg wfh wfA (s≤s sz₁) (s≤s sz₂) = no λ where
  ⟨ A' , () ⟩
≤dec' (suc k₁) (suc k₂) Γ (τ τ⟦ l ↦ A ⟧) Int wfg wfh wfA (s≤s sz₁) (s≤s sz₂) = no λ where
  ⟨ A' , () ⟩
≤dec' (suc k₁) (suc k₂) Γ (⟦ e ⟧⇒ Σ) Int wfg wfh wfA (s≤s sz₁) (s≤s sz₂) = no λ where
  ⟨ A' , () ⟩
≤dec' (suc k₁) (suc k₂) Γ (⌊ l ⌋⇒ Σ) Int wfg wfh wfA (s≤s sz₁) (s≤s sz₂) = no λ where
  ⟨ A' , () ⟩
-- float
≤dec' (suc k₁) (suc k₂) Γ □ Float wfg wfh wfA (s≤s sz₁) (s≤s sz₂) = yes ⟨ Float , ≤□ ⟩
≤dec' (suc k₁) (suc k₂) Γ (τ Int) Float wfg wfh wfA (s≤s sz₁) (s≤s sz₂) = no λ where
  ⟨ A' , () ⟩
≤dec' (suc k₁) (suc k₂) Γ (τ Float) Float wfg wfh wfA (s≤s sz₁) (s≤s sz₂) = yes ⟨ Float , ≤float ⟩
≤dec' (suc k₁) (suc k₂) Γ (τ Top) Float wfg wfh wfA (s≤s sz₁) (s≤s sz₂) = yes ⟨ Top , ≤top ⟩
≤dec' (suc k₁) (suc k₂) Γ (τ (A `→ B)) Float wfg wfh wfA (s≤s sz₁) (s≤s sz₂) = no λ where
  ⟨ A' , () ⟩
≤dec' (suc k₁) (suc k₂) Γ (τ τ⟦ l ↦ A ⟧) Float wfg wfh wfA (s≤s sz₁) (s≤s sz₂) = no λ where
  ⟨ A' , () ⟩
≤dec' (suc k₁) (suc k₂) Γ (⟦ e ⟧⇒ Σ) Float wfg wfh wfA (s≤s sz₁) (s≤s sz₂) = no λ where
  ⟨ A' , () ⟩
≤dec' (suc k₁) (suc k₂) Γ (⌊ l ⌋⇒ Σ) Float wfg wfh wfA (s≤s sz₁) (s≤s sz₂) = no λ where
  ⟨ A' , () ⟩
-- top
≤dec' (suc k₁) (suc k₂) Γ □ Top wfg wfh wfA (s≤s sz₁) (s≤s sz₂) = yes ⟨ Top , ≤□ ⟩
≤dec' (suc k₁) (suc k₂) Γ (τ Int) Top wfg wfh wfA (s≤s sz₁) (s≤s sz₂) = no λ where
  ⟨ A' , () ⟩
≤dec' (suc k₁) (suc k₂) Γ (τ Float) Top wfg wfh wfA (s≤s sz₁) (s≤s sz₂) = no λ where
  ⟨ A' , () ⟩
≤dec' (suc k₁) (suc k₂) Γ (τ Top) Top wfg wfh wfA (s≤s sz₁) (s≤s sz₂) = yes ⟨ Top , ≤top ⟩
≤dec' (suc k₁) (suc k₂) Γ (τ (x `→ x₁)) Top wfg wfh wfA (s≤s sz₁) (s≤s sz₂) = no λ where
  ⟨ A' , () ⟩
≤dec' (suc k₁) (suc k₂) Γ (τ τ⟦ l ↦ A ⟧) Top wfg wfh wfA (s≤s sz₁) (s≤s sz₂) = no λ where
  ⟨ A' , () ⟩
≤dec' (suc k₁) (suc k₂) Γ (⟦ x ⟧⇒ Σ) Top wfg wfh wfA (s≤s sz₁) (s≤s sz₂) = no λ where
  ⟨ A' , () ⟩
≤dec' (suc k₁) (suc k₂) Γ (⌊ x ⌋⇒ Σ) Top wfg wfh wfA (s≤s sz₁) (s≤s sz₂) = no λ where
  ⟨ A' , () ⟩
-- arrow
≤dec' (suc k₁) (suc k₂) Γ □ (A `→ B) wfg wfh wfA (s≤s sz₁) (s≤s sz₂) = yes ⟨ A `→ B , ≤□ ⟩
≤dec' (suc k₁) (suc k₂) Γ (τ Int) (A `→ B) wfg wfh wfA (s≤s sz₁) (s≤s sz₂) = no λ where
  ⟨ A' , () ⟩
≤dec' (suc k₁) (suc k₂) Γ (τ Float) (A `→ B) wfg wfh wfA (s≤s sz₁) (s≤s sz₂) = no λ where
  ⟨ A' , () ⟩
≤dec' (suc k₁) (suc k₂) Γ (τ Top) (A `→ B) wfg wfh wfA (s≤s sz₁) (s≤s sz₂) = yes ⟨ Top , ≤top ⟩
≤dec' (suc k₁) (suc k₂) Γ (τ (A' `→ B')) (A `→ B) wfg (wfh-τ (wf-arr wfA' wfB')) (wf-arr wfA wfB) (s≤s sz₁) (s≤s sz₂)
  with ≤dec' (suc k₁) k₂ Γ (τ A) A' wfg (wfh-τ wfA) wfA' (s≤s sz₁) (sz-case-8 (size-t A') (size-t A) sz₂)
     | ≤dec' (suc k₁) k₂ Γ (τ B') B wfg (wfh-τ wfB') wfB (s≤s sz₁) (sz-case-9 (size-t B) (size-t B') sz₂)
... | yes ⟨ C , s ⟩ | yes ⟨ D , s' ⟩ = yes ⟨ (A' `→ B') , (≤arr s s') ⟩
... | yes p | no ¬p = no λ where
  ⟨ C `→ D , ≤arr {D' = D'} s s₁ ⟩ → ¬p ⟨ D' , s₁ ⟩
... | no ¬p | _ =  no λ where
  ⟨ C `→ D , ≤arr {A' = A'} s s₁ ⟩ → ¬p ⟨ A' , s ⟩
≤dec' (suc k₁) (suc k₂) Γ (τ τ⟦ l ↦ A' ⟧) (A `→ B) wfg wfh wfA (s≤s sz₁) (s≤s sz₂) = no λ where
  ⟨ A' , () ⟩
≤dec' (suc k₁) (suc k₂) Γ (⟦ e ⟧⇒ Σ) (A `→ B) wfg (wfh-e wfh wfe ve) (wf-arr wfA wfB) (s≤s sz₁) (s≤s sz₂)
  with ≤dec' (suc k₁) k₂ Γ Σ B wfg wfh wfB (sz-case-10 sz₁) (sz-case-9 (size-t B) (size-Σ' Σ) sz₂)
     | ⊢dec k₁ Γ (τ A) e wfg (wfh-τ wfA) wfe (sz-case-11 sz₁)
... | yes ⟨ C , s ⟩ | yes ⟨ A' , ⊢e' ⟩ = yes ⟨ (A `→ C) , (≤hint ⊢e' s) ⟩
... | yes p | no ¬p = no λ where
  ⟨ A' `→ B' , ≤hint {C = C} x s ⟩ → ¬p ⟨ C , x ⟩
... | no ¬p | _ = no λ where
  ⟨ A' `→ B' , ≤hint x s ⟩ → ¬p ⟨ B' , s ⟩
≤dec' (suc k₁) (suc k₂) Γ (⌊ l ⌋⇒ Σ) (A `→ B) wfg wfh wfA (s≤s sz₁) (s≤s sz₂) = no λ where
  ⟨ A' , () ⟩
-- and, many repetitions here
≤dec' (suc k₁) (suc k₂) Γ □ (A & B) wfg wfh wfA (s≤s sz₁) (s≤s sz₂) = yes ⟨ A & B , ≤□ ⟩
≤dec' (suc k₁) (suc k₂) Γ Σ@(τ Int) (A & B) wfg wfh (wf-and wfA wfB A#B) (s≤s sz₁) (s≤s sz₂)
  with ≤dec' (suc k₁) k₂ Γ Σ A wfg (wfh-τ wf-int) wfA (s≤s sz₁) (sz-case-4 (size-t A) sz₂)
     | ≤dec' (suc k₁) k₂ Γ Σ B wfg (wfh-τ wf-int) wfB (s≤s sz₁) (sz-case-5 (size-t B) sz₂)
... | yes ⟨ A' , s ⟩ | _ = yes ⟨ A' , (≤and-l s λ ()) ⟩
... | no ¬p | yes ⟨ A' , s ⟩ = yes ⟨ A' , (≤and-r s λ ()) ⟩
... | no ¬p1 | no ¬p2 = no λ where
  ⟨ A' , s ⟩ → inv-sub-and (¬&τ-tau ¬&-int) ¬p1 ¬p2 s
≤dec' (suc k₁) (suc k₂) Γ Σ@(τ Float) (A & B) wfg wfh (wf-and wfA wfB A#B) (s≤s sz₁) (s≤s sz₂)
  with ≤dec' (suc k₁) k₂ Γ Σ A wfg (wfh-τ wf-float) wfA (s≤s sz₁) (sz-case-4 (size-t A) sz₂)
     | ≤dec' (suc k₁) k₂ Γ Σ B wfg (wfh-τ wf-float) wfB (s≤s sz₁) (sz-case-5 (size-t B) sz₂)
... | yes ⟨ A' , s ⟩ | _ = yes ⟨ A' , (≤and-l s λ ()) ⟩
... | no ¬p | yes ⟨ A' , s ⟩ = yes ⟨ A' , (≤and-r s λ ()) ⟩
... | no ¬p1 | no ¬p2 = no λ where
  ⟨ A' , s ⟩ → inv-sub-and (¬&τ-tau ¬&-flt) ¬p1 ¬p2 s
≤dec' (suc k₁) (suc k₂) Γ Σ@(τ Top) (A & B) wfg wfh (wf-and wfA wfB A#B) (s≤s sz₁) (s≤s sz₂)
  with ≤dec' (suc k₁) k₂ Γ Σ A wfg (wfh-τ wf-top) wfA (s≤s sz₁) (sz-case-4 (size-t A) sz₂)
     | ≤dec' (suc k₁) k₂ Γ Σ B wfg (wfh-τ wf-top) wfB (s≤s sz₁) (sz-case-5 (size-t B) sz₂)
... | yes ⟨ A' , s ⟩ | _ = yes ⟨ A' , (≤and-l s λ ()) ⟩
... | no ¬p | yes ⟨ A' , s ⟩ = yes ⟨ A' , (≤and-r s λ ()) ⟩
... | no ¬p1 | no ¬p2 = no λ where
  ⟨ A' , s ⟩ → inv-sub-and (¬&τ-tau ¬&-top) ¬p1 ¬p2 s
≤dec' (suc k₁) (suc k₂) Γ Σ@(τ (x `→ x₁)) (A & B) wfg wfh (wf-and wfA wfB A#B) (s≤s sz₁) (s≤s sz₂)
  with ≤dec' (suc k₁) k₂ Γ Σ A wfg wfh wfA (s≤s sz₁) (sz-case-4 (size-t A) sz₂)
     | ≤dec' (suc k₁) k₂ Γ Σ B wfg wfh wfB (s≤s sz₁) (sz-case-5 (size-t B) sz₂)
... | yes ⟨ A' , s ⟩ | _ = yes ⟨ A' , (≤and-l s λ ()) ⟩
... | no ¬p | yes ⟨ A' , s ⟩ = yes ⟨ A' , (≤and-r s λ ()) ⟩
... | no ¬p1 | no ¬p2 = no λ where
  ⟨ A' , s ⟩ → inv-sub-and (¬&τ-tau ¬&-arr) ¬p1 ¬p2 s
≤dec' (suc k₁) (suc k₂) Γ Σ@(τ τ⟦ x ↦ x₁ ⟧) (A & B) wfg wfh (wf-and wfA wfB A#B) (s≤s sz₁) (s≤s sz₂)
  with ≤dec' (suc k₁) k₂ Γ Σ A wfg wfh wfA (s≤s sz₁) (sz-case-4 (size-t A) sz₂)
     | ≤dec' (suc k₁) k₂ Γ Σ B wfg wfh wfB (s≤s sz₁) (sz-case-5 (size-t B) sz₂)
... | yes ⟨ A' , s ⟩ | _ = yes ⟨ A' , (≤and-l s λ ()) ⟩
... | no ¬p | yes ⟨ A' , s ⟩ = yes ⟨ A' , (≤and-r s λ ()) ⟩
... | no ¬p1 | no ¬p2 = no λ where
  ⟨ A' , s ⟩ → inv-sub-and (¬&τ-tau ¬&-rcd) ¬p1 ¬p2 s
≤dec' (suc k₁) (suc k₂) Γ Σ@(⟦ e ⟧⇒ Σ') (A & B) wfg wfh (wf-and wfA wfB A#B) (s≤s sz₁) (s≤s sz₂)
  with ≤dec' (suc k₁) k₂ Γ Σ A wfg wfh wfA (s≤s sz₁) (sz-case-4 (size-t A) sz₂)
     | ≤dec' (suc k₁) k₂ Γ Σ B wfg wfh wfB (s≤s sz₁) (sz-case-5 (size-t B) sz₂)
... | yes ⟨ A' , s ⟩ | _ = yes ⟨ A' , (≤and-l s λ ()) ⟩
... | no ¬p | yes ⟨ A' , s ⟩ = yes ⟨ A' , (≤and-r s λ ()) ⟩
... | no ¬p1 | no ¬p2 = no λ where
  ⟨ A' , s ⟩ → inv-sub-and ¬&τ-hole ¬p1 ¬p2 s
≤dec' (suc k₁) (suc k₂) Γ Σ@(⌊ l ⌋⇒ Σ') (A & B) wfg wfh (wf-and wfA wfB A#B) (s≤s sz₁) (s≤s sz₂)
  with ≤dec' (suc k₁) k₂ Γ Σ A wfg wfh wfA (s≤s sz₁) (sz-case-4 (size-t A) sz₂)
     | ≤dec' (suc k₁) k₂ Γ Σ B wfg wfh wfB (s≤s sz₁) (sz-case-5 (size-t B) sz₂)
... | yes ⟨ A' , s ⟩ | _ = yes ⟨ A' , (≤and-l s λ ()) ⟩
... | no ¬p | yes ⟨ A' , s ⟩ = yes ⟨ A' , (≤and-r s λ ()) ⟩
... | no ¬p1 | no ¬p2 = no λ where
  ⟨ A' , s ⟩ → inv-sub-and ¬&τ-hole-l ¬p1 ¬p2 s
{-
≤dec' (suc k₁) (suc k₂) Γ Σ (A & B) (s≤s sz₁) (s≤s sz₂) with □-dec Σ
                                                             | ≤dec' (suc k₁) k₂ Γ Σ A (s≤s sz₁) {!!}
                                                             | ≤dec' (suc k₁) k₂ Γ Σ B (s≤s sz₁) {!!}
... | yes p  | _ | _ rewrite p = yes ⟨ A & B , ≤□ ⟩
... | no Σ≢□ | yes ⟨ A' , s ⟩ | _ = yes ⟨ A' , (≤and-l s Σ≢□) ⟩
... | no Σ≢□ | no ¬p | yes ⟨ A' , s ⟩ = yes ⟨ A' , (≤and-r s Σ≢□) ⟩
... | no Σ≢□ | no ¬p1 | no ¬p2 = {!no!} -- it's doable
-}
-- rcd
≤dec' (suc k₁) (suc k₂) Γ □ τ⟦ l ↦ A ⟧ wfg wfh wfA (s≤s sz₁) (s≤s sz₂) = yes ⟨ τ⟦ l ↦ A ⟧ , ≤□ ⟩
≤dec' (suc k₁) (suc k₂) Γ (τ Int) τ⟦ l ↦ A ⟧ wfg wfh wfA (s≤s sz₁) (s≤s sz₂) = no λ where
  ⟨ A' , () ⟩  
≤dec' (suc k₁) (suc k₂) Γ (τ Float) τ⟦ l ↦ A ⟧ wfg wfh wfA (s≤s sz₁) (s≤s sz₂) = no λ where
  ⟨ A' , () ⟩  
≤dec' (suc k₁) (suc k₂) Γ (τ Top) τ⟦ l ↦ A ⟧ wfg wfh wfA (s≤s sz₁) (s≤s sz₂) = yes ⟨ Top , ≤top ⟩
≤dec' (suc k₁) (suc k₂) Γ (τ (x `→ x₁)) τ⟦ l ↦ A ⟧ wfg wfh wfA (s≤s sz₁) (s≤s sz₂) = no λ where
  ⟨ A' , () ⟩  
≤dec' (suc k₁) (suc k₂) Γ (τ τ⟦ l' ↦ A' ⟧) τ⟦ l ↦ A ⟧ wfg (wfh-τ (wf-rcd wfA')) (wf-rcd wfA) (s≤s sz₁) (s≤s sz₂)
  with l ≟ l' | ≤dec' (suc k₁) k₂ Γ (τ A') A wfg (wfh-τ wfA') wfA (s≤s sz₁) (sz-case-12 sz₂)
... | yes refl | yes ⟨ B , s ⟩ = yes ⟨ τ⟦ l ↦ B ⟧ , (≤rcd s) ⟩
... | yes refl | no ¬p = no λ where
  ⟨ (τ⟦ l' ↦ B ⟧) , ≤rcd s ⟩ → ¬p ⟨ B , s ⟩
... | no ¬p | _ = no λ where
  ⟨ (τ⟦ l' ↦ B ⟧) , ≤rcd s ⟩ → ¬p refl 
≤dec' (suc k₁) (suc k₂) Γ (⟦ e ⟧⇒ Σ) τ⟦ l ↦ A ⟧ wfg wfh wfA (s≤s sz₁) (s≤s sz₂) = no λ where
  ⟨ A' , () ⟩  
≤dec' (suc k₁) (suc k₂) Γ (⌊ l ⌋⇒ Σ) τ⟦ l' ↦ A ⟧ wfg (wfh-l wfh) (wf-rcd wfA) (s≤s sz₁) (s≤s sz₂)
  with l ≟ l' | ≤dec' (suc k₁) k₂ Γ Σ A wfg wfh wfA (s≤s (≤-trans (m≤n+m (size-Σ Σ) 1) sz₁)) (sz-case-13 sz₂)
... | yes refl | yes ⟨ B , s ⟩ = yes ⟨ τ⟦ l ↦ B ⟧ , (≤hint-l s) ⟩
... | yes refl | no ¬p = no λ where
  ⟨ (τ⟦ l' ↦ B ⟧) , ≤hint-l s ⟩ → ¬p ⟨ B , s ⟩
... | no ¬p | _ = no λ where
  ⟨ (τ⟦ l' ↦ B ⟧) , ≤hint-l s ⟩ → ¬p refl

-- const
⊢dec (suc k) Γ Σ (𝕔 c) wfg wfh wfe (s≤s sz) with ≤dec k Γ Σ (c-τ c) wfg wfh (wf-c c) sz
... | yes ⟨ A' , s ⟩ = yes ⟨ A' , (subsumption-0 ⊢c s) ⟩
... | no ¬p = no λ where
  ⟨ A , ⊢e' ⟩ → inv-case-const ¬p ⊢e'
-- var
⊢dec (suc k) Γ Σ (` x) wfg wfh wfe (s≤s sz) with x∈Γ-dec Γ x
⊢dec (suc k) Γ Σ (` x) wfg wfh wfe (s≤s sz) | yes ⟨ A , x∈Γ ⟩ with ≤dec k Γ Σ A wfg wfh (x∈Γ-wf wfg x∈Γ) sz
... | yes ⟨ A' , s ⟩ = yes ⟨ A' , subsumption-0 (⊢var x∈Γ) s ⟩
... | no ¬p = no λ where
  ⟨ A , ⊢e' ⟩ → inv-case-var ¬p x∈Γ ⊢e'
⊢dec (suc k) Γ Σ (` x) wfg wfh wfe (s≤s sz) | no ¬p = no λ where
  ⟨ A , ⊢e ⟩ → inv-case-var' ⊢e ¬p
-- lam
⊢dec k Γ □ (ƛ e) wfg wfh wfe sz = no λ where
  ⟨ A , ⊢sub p-e ⊢e' A≤Σ Σ≢□ ⟩ → ⊥-elim (Σ≢□ refl)
-- lam false
⊢dec (suc k) Γ (τ Int) (ƛ e) wfg wfh wfe (s≤s sz) = no λ where
  ⟨ A , ⊢sub p-e (⊢sub p-e₁ ⊢e' A≤Σ₁ Σ≢□₁) A≤Σ Σ≢□ ⟩ → ⊥-elim (Σ≢□₁ refl)
⊢dec (suc k) Γ (τ Float) (ƛ e) wfg wfh wfe (s≤s sz) = no λ where
  ⟨ A , ⊢sub p-e (⊢sub p-e₁ ⊢e' A≤Σ₁ Σ≢□₁) A≤Σ Σ≢□ ⟩ → ⊥-elim (Σ≢□₁ refl)
⊢dec (suc k) Γ (τ Top) (ƛ e) wfg wfh wfe (s≤s sz) = no λ where
  ⟨ A , ⊢sub p-e (⊢sub p-e₁ ⊢e' A≤Σ₁ Σ≢□₁) A≤Σ Σ≢□ ⟩ → ⊥-elim (Σ≢□₁ refl)
-- lam 1
⊢dec (suc k) Γ (τ (A `→ B)) (ƛ e) wfg (wfh-τ (wf-arr wfA wfB)) (wfe-lam wfe) (s≤s sz)
  with ⊢dec k (Γ , A) (τ B) e (wfg-, wfg wfA) (wfh-τ wfB) wfe sz
... | yes ⟨ C , ⊢e ⟩ = yes ⟨ A `→ C , ⊢lam₁ ⊢e ⟩
... | no ¬p = no λ where
  ⟨ A `→ C , ⊢lam₁ ⊢e' ⟩ → ¬p ⟨ C , ⊢e' ⟩
-- lam false
⊢dec (suc k) Γ (τ (A & A₁)) (ƛ e) wfg wfh wfe (s≤s sz) = no λ where
  ⟨ A , ⊢sub p-e (⊢sub p-e₁ ⊢e' A≤Σ₁ Σ≢□₁) A≤Σ Σ≢□ ⟩ → ⊥-elim (Σ≢□₁ refl)
⊢dec (suc k) Γ (τ τ⟦ x ↦ A ⟧) (ƛ e) wfg wfh wfe (s≤s sz) = no λ where
  ⟨ A , ⊢sub p-e (⊢sub p-e₁ ⊢e' A≤Σ₁ Σ≢□₁) A≤Σ Σ≢□ ⟩ → ⊥-elim (Σ≢□₁ refl)
-- lam2
⊢dec (suc k) Γ (⟦ e' ⟧⇒ Σ) (ƛ e) wfg (wfh-e wfh wfe' ve) (wfe-lam wfe) (s≤s sz) with ⊢dec k Γ □ e' wfg wfh-□ wfe' (sz-case-1 sz)
⊢dec (suc k) Γ (⟦ e' ⟧⇒ Σ) (ƛ e) wfg (wfh-e wfh wfe' ve) (wfe-lam wfe) (s≤s sz) | yes ⟨ A , ⊢e' ⟩
  with ⊢dec k (Γ , A) (Σ ⇧ 0) e (wfg-, wfg (⊢wf wfg wfh-□ wfe' ⊢e')) (wf-⇧ wfh) wfe (sz-case-3 {e = e} {Σ = Σ} {e' = e'} sz)
... | yes ⟨ B , ⊢e'' ⟩ = yes ⟨ (A `→ B) , (⊢lam₂ ⊢e' ⊢e'') ⟩
... | no ¬p = no (inv-case-lam' wfg wfe wfe' wfh ((⊢wf wfg wfh-□ wfe' ⊢e')) ⊢e' ¬p)
⊢dec (suc k) Γ (⟦ e' ⟧⇒ Σ) (ƛ e) wfg wfh wfe (s≤s sz) | no ¬p = no λ ih → inv-case-lam'' ¬p ih
-- lam-false
⊢dec k Γ (⌊ x ⌋⇒ Σ) (ƛ e) wfg wfh wfe sz = no λ where
  ⟨ A , ⊢sub p-e (⊢sub p-e₁ ⊢e' A≤Σ₁ Σ≢□₁) A≤Σ Σ≢□ ⟩ → ⊥-elim (Σ≢□₁ refl)
-- app
⊢dec (suc k) Γ Σ (e₁ · e₂) wfg wfh (wfe-app wfe1 wfe2 ve) (s≤s sz) with ⊢dec k Γ (⟦ e₂ ⟧⇒ Σ) e₁ wfg (wfh-e wfh wfe2 ve) wfe1 (sz-case-2 sz)
... | yes ⟨ Int , ⊢e ⟩ = ⊥-elim (inv-case-app ⊢e ht-int)
... | yes ⟨ Float , ⊢e ⟩ = ⊥-elim (inv-case-app ⊢e ht-flt)
... | yes ⟨ Top , ⊢e ⟩ = ⊥-elim (inv-case-app ⊢e ht-top)
... | yes ⟨ A `→ B , ⊢e ⟩ = yes ⟨ B , (⊢app ⊢e) ⟩
... | yes ⟨ A & B , ⊢e ⟩ = ⊥-elim (inv-case-app ⊢e ht-and)
... | yes ⟨ τ⟦ x ↦ A ⟧ , ⊢e ⟩ = ⊥-elim (inv-case-app ⊢e ht-rcd)
... | no ¬p = no λ where
  ⟨ A' , ⊢app {A = A''} ⊢e' ⟩ → ¬p ⟨ A'' `→ A' , ⊢e' ⟩
-- ann
⊢dec (suc k) Γ Σ (e ⦂ A) wfg wfh (wfe-ann wfe wfA) (s≤s sz)
  with ⊢dec k Γ (τ A) e wfg (wfh-τ wfA) wfe (sz-case-11 sz)
     | ≤dec k Γ Σ A wfg wfh wfA (m+n<o⇒n<o sz)
... | yes ⟨ A' , ⊢e' ⟩ | yes ⟨ B' , s ⟩ = yes ⟨ B' , subsumption-0 (⊢ann ⊢e') s ⟩
... | yes p | no ¬p  = no λ where
  ⟨ A' , ⊢ann ⊢e' ⟩ → ¬p ⟨ A , ≤□ ⟩
  ⟨ A' , ⊢sub p-e (⊢ann ⊢e') A≤Σ Σ≢□ ⟩ → ¬p ⟨ A' , A≤Σ ⟩
  ⟨ A' , ⊢sub p-e (⊢sub p-e₁ ⊢e' A≤Σ₁ Σ≢□₁) A≤Σ Σ≢□ ⟩ → ⊥-elim (Σ≢□₁ refl)
... | no ¬p | _      = no λ where
  ⟨ A' , ⊢ann {B = B} ⊢e' ⟩ → ¬p ⟨ B , ⊢e' ⟩
  ⟨ A' , ⊢sub p-e (⊢ann {B = B} ⊢e') A≤Σ Σ≢□ ⟩ → ¬p ⟨ B , ⊢e' ⟩
  ⟨ A' , ⊢sub p-e (⊢sub p-e₁ ⊢e' A≤Σ₁ Σ≢□₁) A≤Σ Σ≢□ ⟩ → ⊥-elim (Σ≢□₁ refl)
-- record
⊢dec (suc k) Γ Σ (𝕣 rs) wfg wfh (wfe-rcd wfr) (s≤s sz) with ⊢r-dec k Γ rs wfg wfr (≤-trans (s≤s (m≤m+n (size-r rs) (size-Σ Σ))) sz)
⊢dec (suc k) Γ Σ (𝕣 rs) wfg wfh (wfe-rcd wfr) (s≤s sz) | yes ⟨ A' , ⊢r' ⟩
  with ≤dec k Γ Σ A' wfg wfh (⊢r-wf wfg wfh-□ wfr ⊢r') (≤-trans (s≤s (m≤n+m (size-Σ Σ) (size-r rs))) sz)
... | yes ⟨ B' , s ⟩ = yes ⟨ B' , (subsumption-0 (⊢rcd ⊢r') s) ⟩
... | no ¬p = no λ where
  ⟨ B' , ⊢sub p-e (⊢sub p-e₁ ⊢e A≤Σ₁ Σ≢□₁) A≤Σ Σ≢□ ⟩ → ⊥-elim (Σ≢□₁ refl)
  ⟨ B' , ⊢sub p-e (⊢rcd x) A≤Σ Σ≢□ ⟩ → inv-case-rcd wfg wfr x ⊢r' A≤Σ ¬p
  ⟨ B' , ⊢rcd x ⟩ → ¬p ⟨ A' , ≤□ ⟩
⊢dec (suc k) Γ Σ (𝕣 rs) wfg wfh wfe (s≤s sz) | no ¬p = no λ where
  ⟨ B' , ⊢sub p-e (⊢sub p-e₁ ⊢e A≤Σ₁ Σ≢□₁) A≤Σ Σ≢□ ⟩ → ⊥-elim (Σ≢□₁ refl)
  ⟨ B' , ⊢sub p-e (⊢rcd {A = A} x) A≤Σ Σ≢□ ⟩ → ¬p ⟨ A , x ⟩
  ⟨ B' , ⊢rcd x ⟩ → ¬p ⟨ B' , x ⟩
-- proj
⊢dec (suc k) Γ Σ (e 𝕡 l) wfg wfh (wfe-prj wfe) (s≤s sz) with ⊢dec k Γ (⌊ l ⌋⇒ Σ) e wfg (wfh-l wfh) wfe (sz-case-14 sz)
... | yes ⟨ Int , ⊢e' ⟩ = ⊥-elim (inv-case-prj ⊢e' htr-int)
... | yes ⟨ Float , ⊢e' ⟩ = ⊥-elim (inv-case-prj ⊢e' htr-flt)
... | yes ⟨ Top , ⊢e' ⟩ = ⊥-elim (inv-case-prj ⊢e' htr-top)
... | yes ⟨ A' `→ A'' , ⊢e' ⟩ = ⊥-elim (inv-case-prj ⊢e' htr-arr)
... | yes ⟨ A' & A'' , ⊢e' ⟩ = ⊥-elim (inv-case-prj ⊢e' htr-and)
... | yes ⟨ τ⟦ x ↦ A' ⟧ , ⊢e' ⟩ = yes ⟨ A' , ⊢prj ⊢e' ⟩
... | no ¬p = no λ where
  ⟨ A'' , ⊢prj {l₂ = l'} ⊢e'' ⟩ → ¬p ⟨ τ⟦ l' ↦ A'' ⟧ , ⊢e'' ⟩

⊢r-dec k Γ rnil wfg wfr sz = yes ⟨ Top , ⊢nil ⟩
⊢r-dec (suc k) Γ (r⟦ l ↦ e ⟧ rnil) wfg (wfr-cons wfe wfr l∉rs) (s≤s sz)
  with ⊢dec k Γ □ e wfg wfh-□ wfe (sz-case-15 sz)
... | yes ⟨ A' , ⊢e' ⟩ = yes ⟨ τ⟦ l ↦ A' ⟧ , ⊢one ⊢e' ⟩
... | no ¬p = no λ where
  ⟨ (τ⟦ l ↦ A' ⟧) , ⊢one x ⟩ → ¬p ⟨ A' , x ⟩
  ⟨ (τ⟦ l ↦ A' ⟧ & _) , ⊢cons x ⊢e' rs≢ ⟩ → ¬p ⟨ A' , x ⟩
⊢r-dec (suc k) Γ (r⟦ l₁ ↦ e₁ ⟧ rs'@(r⟦ l₂ ↦ e₂ ⟧ rs)) wfg (wfr-cons wfe1 (wfr-cons wfe2 wfr l∉rs') l∉rs) (s≤s sz)
  with ⊢dec k Γ □ e₁ wfg wfh-□ wfe1 (sz-case-16 (size-e e₁) (size-e e₂) sz)
     | ⊢r-dec k Γ rs' wfg ((wfr-cons wfe2 wfr l∉rs')) (sz-case-17 {n = size-e e₂} sz)
... | yes ⟨ A' , ⊢e' ⟩ | yes ⟨ B' , ⊢r' ⟩ = yes ⟨ (τ⟦ l₁ ↦ A' ⟧ & B') , (⊢cons ⊢e' ⊢r' (λ ())) ⟩
... | yes ⟨ A' , ⊢e' ⟩ | no ¬p = no λ where
  ⟨ τ⟦ l₁ ↦ _ ⟧ & B' , ⊢cons x ⊢r' x₁ ⟩ → ¬p ⟨ B' , ⊢r' ⟩
... | no ¬p | _ = no λ where
  ⟨ τ⟦ l₁ ↦ A' ⟧ & _ , ⊢cons x ⊢r' x₁ ⟩ → ¬p ⟨ A' , x ⟩
