module Record.Algo.Properties where

open import Record.Prelude hiding (_≤?_) renaming (_≤_ to _≤n_)
open import Record.Common
open import Record.Properties
open import Record.Algo

----------------------------------------------------------------------
--+                             Shift                              +--
----------------------------------------------------------------------

⇧-⇧-comm : ∀ Σ m n
  → m ≤n n
  → Σ ⇧ m ⇧ suc n ≡ Σ ⇧ n ⇧ m
⇧-⇧-comm □ m n m≤n = refl
⇧-⇧-comm (τ A) m n m≤n = refl
⇧-⇧-comm (⟦ e ⟧⇒ Σ) m n m≤n rewrite ↑-↑-comm e m n m≤n | ⇧-⇧-comm Σ m n m≤n = refl
⇧-⇧-comm (⌊ l ⌋⇒ Σ) m n m≤n rewrite ⇧-⇧-comm Σ m n m≤n = refl

⇧-⇩-id : ∀ Σ n
  → Σ ⇧ n ⇩ n ≡ Σ
⇧-⇩-id □ n = refl  
⇧-⇩-id (τ A) n = refl
⇧-⇩-id (⟦ e ⟧⇒ Σ) n rewrite ↑-↓-id e n | ⇧-⇩-id Σ n = refl
⇧-⇩-id (⌊ l ⌋⇒ Σ) n rewrite ⇧-⇩-id Σ n = refl

Σ≢□→Σ⇧≢□ : ∀ {Σ n}
  → Σ ≢ □
  → (Σ ⇧ n) ≢ □
Σ≢□→Σ⇧≢□ {□} neq = ⊥-elim (neq refl)
Σ≢□→Σ⇧≢□ {τ x} neq = neq
Σ≢□→Σ⇧≢□ {⟦ x ⟧⇒ Σ} neq = λ ()
Σ≢□→Σ⇧≢□ {⌊ x ⌋⇒ Σ} neq = λ ()

Σ≢□→Σ⇩≢□ : ∀ {Σ n}
  → Σ ≢ □
  → (Σ ⇩ n) ≢ □
Σ≢□→Σ⇩≢□ {□} neq = ⊥-elim (neq refl)
Σ≢□→Σ⇩≢□ {τ x} neq = neq
Σ≢□→Σ⇩≢□ {⟦ x ⟧⇒ Σ} neq = λ ()
Σ≢□→Σ⇩≢□ {⌊ x ⌋⇒ Σ} neq = λ ()

rs≢rnil→rs↓r : ∀ {rs n}
  → rs ≢ rnil
  → rs ↓r n ≢ rnil
rs≢rnil→rs↓r {rnil} {n} rs≢rnil = ⊥-elim (rs≢rnil refl)
rs≢rnil→rs↓r {r⟦ x ↦ x₁ ⟧ rs} {n} rs≢rnil = λ ()

rs≢rnil→rs↑r : ∀ {rs n}
  → rs ≢ rnil
  → rs ↑r n ≢ rnil
rs≢rnil→rs↑r {rnil} {n} rs≢rnil = ⊥-elim (rs≢rnil refl)
rs≢rnil→rs↑r {r⟦ x ↦ x₁ ⟧ rs} {n} rs≢rnil = λ ()

infix 4 _~⇧~_
data _~⇧~_ : Context → ℕ → Set where

  sdh-□ : ∀ {n}
    → □ ~⇧~ n

  sdh-τ : ∀ {n A}
    → (τ A) ~⇧~ n

  sdh-h : ∀ {n e Σ}
    → e ~↑~ n
    → Σ ~⇧~ n
    → (⟦ e ⟧⇒ Σ) ~⇧~ n

  sdh-l : ∀ {n l Σ}
    → Σ ~⇧~ n
    → (⌊ l ⌋⇒ Σ) ~⇧~ n

⇧-shiftedh : ∀ {Σ n}
  → (Σ ⇧ n) ~⇧~ n
⇧-shiftedh {□} = sdh-□  
⇧-shiftedh {τ A} = sdh-τ
⇧-shiftedh {⟦ e ⟧⇒ Σ} = sdh-h ↑-shifted ⇧-shiftedh
⇧-shiftedh {⌊ l ⌋⇒ Σ} = sdh-l ⇧-shiftedh

⇧-shiftedh-n : ∀ {Σ m n}
  → m ≤n suc n
  → Σ ~⇧~ n
  → (Σ ⇧ m) ~⇧~ suc n
⇧-shiftedh-n {□} m≤n sdh = sdh-□
⇧-shiftedh-n {τ A} m≤n sdh = sdh-τ
⇧-shiftedh-n {⟦ e ⟧⇒ Σ} m≤n (sdh-h sd sdh) = sdh-h (↑-shifted-n m≤n sd) (⇧-shiftedh-n m≤n sdh)
⇧-shiftedh-n {⌊ l ⌋⇒ Σ} m≤n (sdh-l sd) = sdh-l (⇧-shiftedh-n m≤n sd)

⇩-⇧-comm : ∀ Σ m n
  → m ≤n n
  → Σ ~⇧~ n
  → Σ ⇩ n ⇧ m ≡ Σ ⇧ m ⇩ (suc n)
⇩-⇧-comm □ m n m≤n sdh = refl
⇩-⇧-comm (τ A) m n m≤n sdh = refl
⇩-⇧-comm (⟦ e ⟧⇒ Σ) m n m≤n (sdh-h sd sdh) rewrite ↓-↑-comm e m n m≤n sd rewrite ⇩-⇧-comm Σ m n m≤n sdh = refl
⇩-⇧-comm (⌊ l ⌋⇒ Σ) m n m≤n (sdh-l sd) rewrite ⇩-⇧-comm Σ m n m≤n sd = refl

Σ≢□-⇩ : ∀ {Σ n}
  → Σ ≢ □
  → Σ ⇩ n ≢ □
Σ≢□-⇩ {□} Σ≢□ = Σ≢□
Σ≢□-⇩ {τ x} Σ≢□ = Σ≢□
Σ≢□-⇩ {⟦ x ⟧⇒ Σ} Σ≢□ = λ ()

Σ≢□-⇧ : ∀ {Σ n}
  → Σ ≢ □
  → Σ ⇧ n ≢ □
Σ≢□-⇧ {□} Σ≢□ = Σ≢□
Σ≢□-⇧ {τ x} Σ≢□ = Σ≢□
Σ≢□-⇧ {⟦ x ⟧⇒ Σ} Σ≢□ = λ ()

----------------------------------------------------------------------
--+                           Weakening                            +--
----------------------------------------------------------------------

≤weaken : ∀ {Γ A B C Σ n n≤l}
  → Γ ⊢ B ≤ Σ ⇝ C
  → Γ ↑ n [ n≤l ] A ⊢ B ≤ (Σ ⇧ n) ⇝ C

⊢weaken : ∀ {Γ e Σ A B n n≤l}
  → Γ ⊢ Σ ⇒ e ⇒ B
  → Γ ↑ n [ n≤l ] A ⊢ Σ ⇧ n ⇒ e ↑ n ⇒ B

⊢r-weaken : ∀ {Γ rs A B n n≤l}
  → Γ ⊢r □ ⇒ rs ⇒ B
  → Γ ↑ n [ n≤l ] A ⊢r □ ⇒ rs ↑r n ⇒ B

≤weaken ≤int = ≤int
≤weaken ≤float = ≤float
≤weaken ≤top = ≤top
≤weaken ≤□ = ≤□
≤weaken (≤arr C≤ B≤D) = ≤arr (≤weaken C≤) (≤weaken B≤D)
≤weaken (≤hint ⊢e B≤Σ) = ≤hint (⊢weaken ⊢e) (≤weaken B≤Σ)
≤weaken (≤and-l ≤ Σ≢□) = ≤and-l (≤weaken ≤) (Σ≢□-⇧ Σ≢□)
≤weaken (≤and-r ≤ Σ≢□) = ≤and-r (≤weaken ≤) (Σ≢□-⇧ Σ≢□)
≤weaken (≤and ≤₁ ≤₂) = ≤and (≤weaken ≤₁) (≤weaken ≤₂)
≤weaken (≤rcd x) = ≤rcd (≤weaken x)
≤weaken (≤hint-l x) = ≤hint-l (≤weaken x)

≤weaken-0 : ∀ {Γ A B Σ C}
  → Γ ⊢ B ≤ Σ ⇝ C
  → Γ , A ⊢ B ≤ (Σ ⇧ 0) ⇝ C
≤weaken-0 B≤Σ = ≤weaken {n≤l = z≤n} B≤Σ  

⇧-⇧-comm-0 : ∀ Σ n
  → Σ ⇧ n ⇧ 0 ≡ Σ ⇧ 0 ⇧ (suc n)
⇧-⇧-comm-0 Σ n rewrite ⇧-⇧-comm Σ 0 n z≤n = refl

⊢weaken ⊢c = ⊢c
⊢weaken {n≤l = n≤l} (⊢var x∈Γ) = ⊢var (∋-weaken x∈Γ n≤l)
⊢weaken (⊢app ⊢e) = ⊢app (⊢weaken ⊢e)
⊢weaken (⊢ann ⊢e) = ⊢ann (⊢weaken ⊢e)
⊢weaken {n≤l = n≤l} (⊢lam₁ ⊢e) = ⊢lam₁ (⊢weaken {n≤l = s≤s n≤l} ⊢e)
⊢weaken {Σ = ⟦ _ ⟧⇒ Σ} {A = A} {n = n} {n≤l = n≤l} (⊢lam₂ ⊢e ⊢f) with ⊢weaken {A = A} {n = suc n} {n≤l = s≤s n≤l} ⊢f
... | ind-f rewrite sym (⇧-⇧-comm-0 Σ n) = ⊢lam₂ (⊢weaken ⊢e) ind-f
⊢weaken (⊢sub gc ⊢e B≤Σ Σ≢□) = ⊢sub (↑-gc-prv gc) (⊢weaken ⊢e) (≤weaken B≤Σ) (Σ≢□→Σ⇧≢□ Σ≢□)
⊢weaken {e = 𝕣 x} (⊢rcd ⊢rs) = ⊢rcd (⊢r-weaken ⊢rs)
⊢weaken {e = e 𝕡 x} (⊢prj ⊢e) = ⊢prj (⊢weaken ⊢e)

⊢r-weaken ⊢nil = ⊢nil
⊢r-weaken (⊢one x) = ⊢one (⊢weaken x)
⊢r-weaken (⊢cons x ⊢r rs≢) = ⊢cons (⊢weaken x) (⊢r-weaken ⊢r) (rs≢rnil→rs↑r rs≢)

up : ℕ → Apps → Apps
up n [] = []
up n (e ∷a as) = (e ↑ n) ∷a (up n as)
up n (l ∷l as) = l ∷l (up n as)

spl-weaken : ∀ {Σ A es T As A' n}
  → ⟦ Σ , A ⟧→⟦ es , T , As , A' ⟧
  → ⟦ Σ ⇧ n , A ⟧→⟦ up n es , T , As , A' ⟧
spl-weaken none-□ = none-□
spl-weaken none-τ = none-τ
spl-weaken (have-a spl) = have-a (spl-weaken spl)
spl-weaken (have-l spl) = have-l (spl-weaken spl)

⊢id : ∀ {Γ Σ e A A' T es As}
  → Γ ⊢ Σ ⇒ e ⇒ A
  → ⟦ Σ , A ⟧→⟦ es , τ T , As , A' ⟧
  → T ≡ A'

≤id : ∀ {Γ Σ A B Bs B' es T}
  → Γ ⊢ A ≤ Σ ⇝ B
  → ⟦ Σ , B ⟧→⟦ es , τ T , Bs , B' ⟧
  → T ≡ B'

⊢id-0 : ∀ {Γ e A B}
  → Γ ⊢ τ B ⇒ e ⇒ A
  → A ≡ B
⊢id-0 ⊢e = sym (⊢id ⊢e none-τ)

≤id-0 : ∀ {Γ A B C}
  → Γ ⊢ A ≤ τ B ⇝ C
  → C ≡ B
≤id-0 A≤B = sym (≤id A≤B none-τ)

≤id ≤int none-τ = refl
≤id ≤float none-τ = refl
≤id ≤top none-τ = refl
≤id (≤arr A≤Σ A≤Σ₁) none-τ = refl
≤id (≤rcd A≤Σ) none-τ rewrite ≤id-0 A≤Σ = refl
≤id (≤hint x A≤Σ) (have-a spl) = ≤id A≤Σ spl
≤id (≤hint-l A≤Σ) (have-l spl) = ≤id A≤Σ spl
≤id (≤and-l A≤Σ x) spl = ≤id A≤Σ spl
≤id (≤and-r A≤Σ x) spl = ≤id A≤Σ spl
≤id (≤and A≤Σ A≤Σ₁) none-τ rewrite ≤id-0 A≤Σ | ≤id-0 A≤Σ₁ = refl
⊢id (⊢app ⊢e) spl = ⊢id ⊢e (have-a spl)
⊢id (⊢lam₁ ⊢e) none-τ rewrite ⊢id-0 ⊢e = refl
⊢id (⊢lam₂ ⊢e ⊢e₁) (have-a spl) = ⊢id ⊢e₁ (spl-weaken spl)
⊢id (⊢sub pe ⊢e A≤Σ Σ≢□) spl = ≤id A≤Σ spl
⊢id (⊢prj ⊢e) spl = ⊢id ⊢e (have-l spl)

----------------------------------------------------------------------
--+                         Strengthening                          +--
----------------------------------------------------------------------


≤strengthen : ∀ {Γ A B Σ n}
  → Γ ⊢ A ≤ Σ ⇝ B
  → Σ ~⇧~ n
  → (n≤l : n ≤n length Γ)
  → Γ ↓ n [ n≤l ] ⊢ A ≤ (Σ ⇩ n) ⇝ B
  
⊢strengthen : ∀ {Γ A Σ n e}
  → Γ ⊢ Σ ⇒ e ⇒ A -- Σ, e is shifted
  → e ~↑~ n
  → Σ ~⇧~ n
  → (n≤l : n ≤n length Γ)
  → Γ ↓ n [ n≤l ] ⊢ (Σ ⇩ n) ⇒ e ↓ n ⇒ A

⊢r-strengthen : ∀ {Γ A n rs}
  → Γ ⊢r □ ⇒ rs ⇒ A
  → rs ~↑r~ n
  → (n≤l : n ≤n length Γ)
  → Γ ↓ n [ n≤l ] ⊢r □ ⇒ rs ↓r n ⇒ A

≤strengthen ≤int sdh n≤l = ≤int
≤strengthen ≤float sdh n≤l = ≤float
≤strengthen ≤top sdh n≤l = ≤top
≤strengthen ≤□ sdh n≤l = ≤□
≤strengthen (≤arr A≤Σ A≤Σ₁) sdh n≤l = ≤arr (≤strengthen A≤Σ sdh-τ n≤l) (≤strengthen A≤Σ₁ sdh-τ n≤l)
≤strengthen (≤hint ⊢e A≤Σ) (sdh-h sd sdh) n≤l = ≤hint (⊢strengthen ⊢e sd sdh-τ n≤l) (≤strengthen A≤Σ sdh n≤l)
≤strengthen (≤and-l x₁ Σ≢□) x n≤l = ≤and-l (≤strengthen x₁ x n≤l) (Σ≢□-⇩ Σ≢□)
≤strengthen (≤and-r x₁ Σ≢□) x n≤l = ≤and-r (≤strengthen x₁ x n≤l) (Σ≢□-⇩ Σ≢□)
≤strengthen (≤and x₁ x₂) x n≤l = ≤and (≤strengthen x₁ sdh-τ n≤l) (≤strengthen x₂ sdh-τ n≤l)
≤strengthen (≤rcd x₁) x n≤l = ≤rcd (≤strengthen x₁ sdh-τ n≤l)
≤strengthen (≤hint-l x₁) (sdh-l x) n≤l = ≤hint-l (≤strengthen x₁ x n≤l)

⊢strengthen ⊢c sd sdh n≤l = ⊢c
⊢strengthen (⊢var x∈Γ) sd sdh n≤l = ⊢var (∋-strenghthen x∈Γ sd n≤l)
⊢strengthen (⊢app ⊢e) (sd-app sd₁ sd₂) sdh n≤l = ⊢app (⊢strengthen ⊢e sd₁ (sdh-h sd₂ sdh) n≤l)
⊢strengthen (⊢ann ⊢e) (sd-ann sd) sdh n≤l = ⊢ann (⊢strengthen ⊢e sd sdh-τ n≤l)
⊢strengthen (⊢lam₁ ⊢e) (sd-lam sd) sdh n≤l = ⊢lam₁ (⊢strengthen ⊢e sd sdh-τ (s≤s n≤l))
⊢strengthen {Σ = ⟦ _ ⟧⇒ Σ} {n = n} (⊢lam₂ ⊢e ⊢f) (sd-lam sd₁) (sdh-h sd₂ sdh) n≤l with ⊢strengthen ⊢f sd₁ (⇧-shiftedh-n z≤n sdh) (s≤s n≤l)
... | ind-f rewrite sym (⇩-⇧-comm Σ 0 n z≤n sdh) = ⊢lam₂ (⊢strengthen ⊢e sd₂ sdh-□ n≤l) ind-f
⊢strengthen (⊢sub gc ⊢e A≤Σ Σ≢□) sd sdh n≤l = ⊢sub (↓-gc-prv gc) (⊢strengthen ⊢e sd sdh-□ n≤l) (≤strengthen A≤Σ sdh n≤l) (Σ≢□→Σ⇩≢□ Σ≢□)
⊢strengthen (⊢rcd x₃) (sd-rcd x) x₁ n≤l = ⊢rcd (⊢r-strengthen x₃ x n≤l)
⊢strengthen (⊢prj x₃) (sd-prj x) x₁ n≤l = ⊢prj (⊢strengthen x₃ x (sdh-l x₁) n≤l)

⊢r-strengthen ⊢nil sd n≤l = ⊢nil
⊢r-strengthen (⊢one x) (sdr-cons x₁ sd) n≤l = ⊢one (⊢strengthen x x₁ sdh-□ n≤l)
⊢r-strengthen (⊢cons x ⊢r rs≢) (sdr-cons x₁ sd) n≤l = ⊢cons (⊢strengthen x x₁ sdh-□ n≤l) (⊢r-strengthen ⊢r sd n≤l) (rs≢rnil→rs↓r rs≢)

≤strengthen-0 : ∀ {Γ A B C Σ}
  → Γ , A ⊢ B ≤ Σ ⇧ 0 ⇝ C
  → Γ ⊢ B ≤ Σ ⇝ C
≤strengthen-0 {Σ = Σ} B≤Σ with ≤strengthen {n = 0} B≤Σ ⇧-shiftedh z≤n
... | ind-h rewrite ⇧-⇩-id Σ 0 = ind-h  

⊢strengthen-0 : ∀ {Γ Σ e A B}
  → Γ , A ⊢ Σ ⇧ 0 ⇒ e ↑ 0 ⇒ B
  → Γ ⊢ Σ ⇒ e ⇒ B
⊢strengthen-0 {Σ = Σ} {e = e} ⊢e with ⊢strengthen {n = 0} ⊢e ↑-shifted ⇧-shiftedh z≤n
... | ind-e rewrite ↑-↓-id e 0 | ⇧-⇩-id Σ 0  = ind-e


----------------------------------------------------------------------
--+                      General Subsumption                       +--
----------------------------------------------------------------------

≤rigid : ∀ {Γ A B C}
  → Γ ⊢ A ≤ τ B ⇝ C
  → Γ ⊢ A ≤ τ B ⇝ B
≤rigid s with ≤id-0 s
... | refl = s  

≤refined : ∀ {Γ A B Σ}
  → Γ ⊢ A ≤ Σ ⇝ B
  → Γ ⊢ B ≤ Σ ⇝ B
≤refined ≤int = ≤int
≤refined ≤float = ≤float
≤refined ≤top = ≤top
≤refined ≤□ = ≤□
≤refined (≤arr A≤Σ A≤Σ₁) = ≤arr ≤refl ≤refl
≤refined (≤hint x A≤Σ) = ≤hint x (≤refined A≤Σ)
≤refined (≤and-l A≤Σ Σ≢□) = ≤refined A≤Σ
≤refined (≤and-r A≤Σ Σ≢□) = ≤refined A≤Σ
≤refined (≤and A≤Σ A≤Σ₁) = ≤and (≤and-l (≤refined A≤Σ) λ ()) (≤and-r (≤refined A≤Σ₁) λ ())
≤refined (≤rcd x) = ≤rcd (≤refined x)
≤refined (≤hint-l x) = ≤hint-l (≤refined x)

data chain : Apps → Context → Context → Set where
  ch-none : ∀ {Σ}
    → chain [] Σ Σ

  ch-cons-h : ∀ {Σ e es Σ'}
    → chain es Σ Σ'
    → chain (e ∷a es) Σ (⟦ e ⟧⇒ Σ')

  ch-cons-l : ∀ {Σ l es Σ'}
    → chain es Σ Σ'
    → chain (l ∷l es) Σ (⌊ l ⌋⇒ Σ')

ch-weaken : ∀ {es Σ' Σ n}
  → chain es Σ' Σ
  → chain (up n es) (Σ' ⇧ n) (Σ ⇧ n)
ch-weaken ch-none = ch-none
ch-weaken (ch-cons-h ch) = ch-cons-h (ch-weaken ch)
ch-weaken (ch-cons-l ch) = ch-cons-l (ch-weaken ch)

chainΣ≢□ : ∀ {Σ Σ' Σ'' es As A' T}
  → Σ ≢ □
  → ⟦ Σ , A' ⟧→⟦ es , □ , As , T ⟧
  → chain es Σ'' Σ'
  → Σ' ≢ □
chainΣ≢□ {□} Σ≢□ spl newΣ' = ⊥-elim (Σ≢□ refl)
chainΣ≢□ {⟦ x ⟧⇒ Σ} Σ≢□ (have-a spl) (ch-cons-h newΣ') = λ ()
chainΣ≢□ {⌊ x ⌋⇒ Σ} Σ≢□ (have-l spl) (ch-cons-l newΣ') = λ ()

≤trans : ∀ {Γ A Σ Σ' Σ'' T es A' A'' As}
  → Γ ⊢ A ≤ Σ ⇝ A'
  → ⟦ Σ , A' ⟧→⟦ es , □ , As , T ⟧
  → chain es Σ'' Σ'
  → Γ ⊢ A' ≤ Σ' ⇝ A''
  → Γ ⊢ A ≤ Σ' ⇝ A''
≤trans ≤□ none-□ ch-none A≤Σ' = A≤Σ'
≤trans (≤hint x A≤Σ) (have-a spl) (ch-cons-h newΣ') (≤hint x₁ A≤Σ') = ≤hint x₁ (≤trans A≤Σ spl newΣ' A≤Σ')
≤trans (≤hint-l A≤Σ) (have-l spl) (ch-cons-l newΣ') (≤hint-l A≤Σ') = ≤hint-l (≤trans A≤Σ spl newΣ' A≤Σ')
≤trans (≤and-l A≤Σ x) spl newΣ' A≤Σ' = ≤and-l (≤trans A≤Σ spl newΣ'  A≤Σ') (chainΣ≢□ x spl newΣ')
≤trans (≤and-r A≤Σ x) spl newΣ' A≤Σ' = ≤and-r (≤trans A≤Σ spl newΣ'  A≤Σ') (chainΣ≢□ x spl newΣ')

⊢to-≤ : ∀ {Γ e Σ A}
  → Γ ⊢ Σ ⇒ e ⇒ A
  → Γ ⊢ A ≤ Σ ⇝ A

subsumption : ∀ {Γ Σ e A Σ' Σ'' es As T A'}
  → Γ ⊢ Σ ⇒ e ⇒ A
  → ⟦ Σ , A ⟧→⟦ es , □ , As , T ⟧
  → chain es Σ'' Σ'
  → Γ ⊢ A ≤ Σ' ⇝ A'
  → Γ ⊢ Σ' ⇒ e ⇒ A'

subsumption-0 : ∀ {Γ Σ e A A'}
  → Γ ⊢ □ ⇒ e ⇒ A
  → Γ ⊢ A ≤ Σ ⇝ A'
  → Γ ⊢ Σ ⇒ e ⇒ A'
subsumption-0 ⊢e A≤Σ = subsumption ⊢e none-□ ch-none A≤Σ  

⊢to-≤ ⊢c = ≤□
⊢to-≤ (⊢var x) = ≤□
⊢to-≤ (⊢ann ⊢e) = ≤□
⊢to-≤ (⊢app ⊢e) with ⊢to-≤ ⊢e
... | ≤hint x r = r
⊢to-≤ (⊢lam₁ ⊢e) with ⊢to-≤ ⊢e
... | r rewrite ⊢id-0 ⊢e = ≤refl
⊢to-≤ (⊢lam₂ ⊢e ⊢e₁) = ≤hint (rebase ⊢e ≤refl) (≤strengthen-0 (⊢to-≤ ⊢e₁))
  where
    rebase : ∀ {Γ e A B B'}
      → Γ ⊢ □ ⇒ e ⇒ B
      → Γ ⊢ B ≤ τ A ⇝ B'
      → Γ ⊢ τ A ⇒ e ⇒ B'
    rebase ⊢f B≤ = subsumption ⊢f none-□ ch-none B≤
⊢to-≤ (⊢sub x ⊢e x₁ Σ≢□) = ≤refined x₁
⊢to-≤ (⊢rcd x) = ≤□
⊢to-≤ (⊢prj ⊢e) with ⊢to-≤ ⊢e
... | ≤hint-l r = r

□-dec : ∀ Σ
  → Dec (Σ ≡ □)
□-dec □ = yes refl
□-dec (τ x) = no (λ ())
□-dec (⟦ x ⟧⇒ Σ) = no (λ ())
□-dec (⌊ x ⌋⇒ Σ) = no (λ ())

subsumption {Σ' = Σ'} ⊢e spl ch A≤Σ' with □-dec Σ'
subsumption {Σ' = .□} ⊢e none-□ ch-none ≤□ | yes refl = ⊢e
subsumption {Σ' = .□} ⊢e none-□ ch-none (≤and-l A≤Σ' x) | yes refl = ⊥-elim (x refl)
subsumption {Σ' = .□} ⊢e none-□ ch-none (≤and-r A≤Σ' x) | yes refl = ⊥-elim (x refl)
subsumption {Σ' = Σ'} ⊢c spl ch A≤Σ' | no ¬p = ⊢sub gc-i ⊢c A≤Σ' ¬p
subsumption {Σ' = Σ'} (⊢var x) spl ch A≤Σ' | no ¬p = ⊢sub gc-var (⊢var x) A≤Σ' ¬p
subsumption {Σ' = Σ'} (⊢ann ⊢e) spl ch A≤Σ' | no ¬p = ⊢sub gc-ann (⊢ann ⊢e) A≤Σ' ¬p
subsumption {Σ' = Σ'} (⊢app ⊢e) spl ch A≤Σ' | no ¬p with ⊢to-≤ ⊢e
... | ≤hint x r = ⊢app (subsumption ⊢e (have-a spl) (ch-cons-h ch) (≤hint x A≤Σ'))
subsumption {Σ' = .(⟦ _ ⟧⇒ _)} (⊢lam₂ ⊢e ⊢e₁) (have-a spl) (ch-cons-h ch) (≤hint x A≤Σ') | no ¬p =
  ⊢lam₂ ⊢e (subsumption ⊢e₁ (spl-weaken spl) (ch-weaken ch) (≤weaken {n≤l = z≤n} A≤Σ'))
subsumption {Σ' = Σ'} (⊢sub x ⊢e x₁ Σ≢□) spl ch A≤Σ' | no ¬p = ⊢sub x ⊢e (≤trans x₁ spl ch A≤Σ') ¬p
subsumption {Σ' = Σ'} (⊢rcd x) spl ch A≤Σ' | no ¬p = ⊢sub gc-rcd (⊢rcd x) A≤Σ' ¬p
subsumption {Σ' = Σ'} (⊢prj ⊢e) spl ch A≤Σ' | no ¬p with ⊢to-≤ ⊢e
... | ≤hint-l r = ⊢prj (subsumption ⊢e (have-l spl) (ch-cons-l ch) (≤hint-l A≤Σ'))

⊢spl-τ : ∀ {Γ Σ e A es As A' T}
  → Γ ⊢ Σ ⇒ e ⇒ A
  → ⟦ Σ , A ⟧→⟦ es , τ T , As , A' ⟧
  → T ≡ A'

≤spl-τ : ∀ {Γ A₁ A A' As Σ T es}
  → Γ ⊢ A₁ ≤ Σ ⇝ A
  → ⟦ Σ , A ⟧→⟦ es , τ T , As , A' ⟧
  → T ≡ A'

⊢spl-τ (⊢app ⊢e) spl = ⊢spl-τ ⊢e (have-a spl)
⊢spl-τ (⊢lam₁ ⊢e) none-τ rewrite ⊢spl-τ ⊢e none-τ = refl
⊢spl-τ (⊢lam₂ ⊢e ⊢e₁) (have-a spl) = ⊢spl-τ ⊢e₁ (spl-weaken spl)
⊢spl-τ (⊢sub x ⊢e x₁ _) spl = ≤spl-τ x₁ spl
⊢spl-τ (⊢prj ⊢e) spl = ⊢spl-τ ⊢e (have-l spl)

≤spl-τ ≤int none-τ = refl
≤spl-τ ≤float none-τ = refl
≤spl-τ ≤top none-τ = refl
≤spl-τ (≤arr A≤Σ A≤Σ₁) none-τ = refl
≤spl-τ (≤rcd A≤Σ) none-τ rewrite ≤spl-τ A≤Σ none-τ = refl
≤spl-τ (≤hint x A≤Σ) (have-a spl) = ≤spl-τ A≤Σ spl
≤spl-τ (≤hint-l A≤Σ) (have-l spl) = ≤spl-τ A≤Σ spl
≤spl-τ (≤and-l A≤Σ x) spl = ≤spl-τ A≤Σ spl
≤spl-τ (≤and-r A≤Σ x) spl = ≤spl-τ A≤Σ spl
≤spl-τ (≤and A≤Σ A≤Σ₁) none-τ rewrite ≤spl-τ A≤Σ none-τ | ≤spl-τ A≤Σ₁ none-τ = refl
