module STLC.Algo.Properties where

open import STLC.Prelude hiding (_≤?_) renaming (_≤_ to _≤n_)
open import STLC.Common
open import STLC.Properties
open import STLC.Algo

----------------------------------------------------------------------
--+                             Shift                              +--
----------------------------------------------------------------------

⇧-⇧-comm : ∀ Σ m n
  → m ≤n n
  → Σ ⇧ m ⇧ suc n ≡ Σ ⇧ n ⇧ m
⇧-⇧-comm □ m n m≤n = refl
⇧-⇧-comm (τ A) m n m≤n = refl
⇧-⇧-comm ([ e ]↝ Σ) m n m≤n rewrite ↑-↑-comm e m n m≤n | ⇧-⇧-comm Σ m n m≤n = refl

⇧-⇩-id : ∀ Σ n
  → Σ ⇧ n ⇩ n ≡ Σ
⇧-⇩-id □ n = refl
⇧-⇩-id (τ A) n = refl
⇧-⇩-id ([ e ]↝ Σ) n rewrite ↑-↓-id e n | ⇧-⇩-id Σ n = refl

infix 4 _~⇧~_
data _~⇧~_ : Context → ℕ → Set where

  sdh-□ : ∀ {n}
    → □ ~⇧~ n

  sdh-τ : ∀ {n A}
    → (τ A) ~⇧~ n

  sdh-h : ∀ {n e Σ}
    → e ~↑~ n
    → Σ ~⇧~ n
    → ([ e ]↝ Σ) ~⇧~ n

⇧-shiftedh : ∀ {Σ n}
  → (Σ ⇧ n) ~⇧~ n
⇧-shiftedh {□} = sdh-□
⇧-shiftedh {τ A} = sdh-τ
⇧-shiftedh {[ e ]↝ Σ} = sdh-h ↑-shifted ⇧-shiftedh

⇧-shiftedh-n : ∀ {Σ m n}
  → m ≤n suc n
  → Σ ~⇧~ n
  → (Σ ⇧ m) ~⇧~ suc n
⇧-shiftedh-n {□} m≤n sdh = sdh-□
⇧-shiftedh-n {τ A} m≤n sdh = sdh-τ
⇧-shiftedh-n {[ e ]↝ Σ} m≤n (sdh-h sd sdh) = sdh-h (↑-shifted-n m≤n sd) (⇧-shiftedh-n m≤n sdh)

⇩-⇧-comm : ∀ Σ m n
  → m ≤n n
  → Σ ~⇧~ n
  → Σ ⇩ n ⇧ m ≡ Σ ⇧ m ⇩ (suc n)
⇩-⇧-comm (□) m n m≤n sdh = refl
⇩-⇧-comm (τ A) m n m≤n sdh = refl
⇩-⇧-comm ([ e ]↝ Σ) m n m≤n (sdh-h sd sdh) rewrite ↓-↑-comm e m n m≤n sd rewrite ⇩-⇧-comm Σ m n m≤n sdh = refl

----------------------------------------------------------------------
--+                           Weakening                            +--
----------------------------------------------------------------------

↑-gc : ∀ {e n}
  → GenericConsumer e
  → GenericConsumer (e ↑ n)
↑-gc gc-lit = gc-lit
↑-gc gc-var = gc-var
↑-gc gc-ann = gc-ann

↓-gc : ∀ {e n}
  → GenericConsumer e
  → GenericConsumer (e ↓ n)
↓-gc gc-lit = gc-lit
↓-gc gc-var = gc-var
↓-gc gc-ann = gc-ann

≈weaken : ∀ {Γ A B Σ n n≤l}
  → Γ ⊢ B ≈ Σ
  → Γ ↑ n [ n≤l ] A ⊢ B ≈ (Σ ⇧ n)

⊢weaken : ∀ {Γ e Σ A B n n≤l}
  → Γ ⊢ Σ ⇒ e ⇒ B
  → Γ ↑ n [ n≤l ] A ⊢ Σ ⇧ n ⇒ e ↑ n ⇒ B

≈weaken ≈□ = ≈□
≈weaken ≈τ = ≈τ
≈weaken (≈term ⊢e B≈Σ) = ≈term (⊢weaken ⊢e) (≈weaken B≈Σ)

⇧-⇧-comm-0 : ∀ Σ n
  → Σ ⇧ n ⇧ 0 ≡ Σ ⇧ 0 ⇧ (suc n)
⇧-⇧-comm-0 Σ n rewrite ⇧-⇧-comm Σ 0 n z≤n = refl

⊢weaken ⊢lit = ⊢lit
⊢weaken {n≤l = n≤l} (⊢var x∈Γ) = ⊢var (∋-weaken x∈Γ n≤l)
⊢weaken (⊢ann ⊢e) = ⊢ann (⊢weaken ⊢e)
⊢weaken (⊢app ⊢e) = ⊢app (⊢weaken ⊢e)
⊢weaken {n≤l = n≤l} (⊢lam₁ ⊢e) = ⊢lam₁ (⊢weaken {n≤l = s≤s n≤l} ⊢e)
⊢weaken {Σ = [ _ ]↝ Σ} {A = A} {n = n} {n≤l = n≤l} (⊢lam₂ ⊢e ⊢f) with ⊢weaken {A = A} {n = suc n} {n≤l = s≤s n≤l} ⊢f
... | ind-f rewrite sym (⇧-⇧-comm-0 Σ n) = ⊢lam₂ (⊢weaken ⊢e) ind-f
⊢weaken (⊢sub ⊢e B≈Σ p Σ≢□) = ⊢sub (⊢weaken ⊢e) (≈weaken B≈Σ) (↑-gc p) (ts Σ≢□)
  where ts : ∀ {Σ n} → ¬□ Σ → ¬□ (Σ ⇧ n)
        ts {τ x} nh = nh
        ts {[ x ]↝ Σ} nh = ¬□-term

spl-weaken : ∀ {Σ A es T As A' n}
  → ⟦ Σ , A ⟧→⟦ es , T , As , A' ⟧
  → ⟦ Σ ⇧ n , A ⟧→⟦ map (_↑ n) es , T , As , A' ⟧
spl-weaken {T = .□} none-□ = none-□
spl-weaken {T = .(τ _)} none-τ = none-τ
spl-weaken (have spl) = have (spl-weaken spl)


----------------------------------------------------------------------
--+                         Strengthening                          +--
----------------------------------------------------------------------

≈strengthen : ∀ {Γ A Σ n}
  → Γ ⊢ A ≈ Σ
  → Σ ~⇧~ n
  → (n≤l : n ≤n length Γ)
  → Γ ↓ n [ n≤l ] ⊢ A ≈ (Σ ⇩ n)
  
⊢strengthen : ∀ {Γ A Σ n e}
  → Γ ⊢ Σ ⇒ e ⇒ A -- Σ, e is shifted
  → e ~↑~ n
  → Σ ~⇧~ n
  → (n≤l : n ≤n length Γ)
  → Γ ↓ n [ n≤l ] ⊢ (Σ ⇩ n) ⇒ e ↓ n ⇒ A

≈strengthen ≈□ Σn n≤l = ≈□
≈strengthen ≈τ Σn n≤l = ≈τ
≈strengthen (≈term ⊢e A≈Σ) (sdh-h x Σn) n≤l = ≈term (⊢strengthen ⊢e x sdh-τ n≤l) (≈strengthen A≈Σ Σn n≤l)

⊢strengthen ⊢lit en Σn n≤l = ⊢lit
⊢strengthen (⊢var x∈Γ) en Σn n≤l = ⊢var (∋-strenghthen x∈Γ en n≤l)
⊢strengthen (⊢ann ⊢e) (sd-ann en) Σn n≤l = ⊢ann (⊢strengthen ⊢e en sdh-τ n≤l)
⊢strengthen (⊢app ⊢e) (sd-app en en₁) Σn n≤l = ⊢app (⊢strengthen ⊢e en (sdh-h en₁ Σn) n≤l)
⊢strengthen (⊢lam₁ ⊢e) (sd-lam sd) sdh n≤l = ⊢lam₁ (⊢strengthen ⊢e sd sdh-τ (s≤s n≤l))
⊢strengthen {Σ = [ _ ]↝ Σ} {n = n} (⊢lam₂ ⊢e ⊢f) (sd-lam sd₁) (sdh-h sd₂ sdh) n≤l with ⊢strengthen ⊢f sd₁ (⇧-shiftedh-n z≤n sdh) (s≤s n≤l)
... | ind-f rewrite sym (⇩-⇧-comm Σ 0 n z≤n sdh) = ⊢lam₂ (⊢strengthen ⊢e sd₂ sdh-□ n≤l) ind-f
⊢strengthen (⊢sub ⊢e A≈Σ p Σ≢□) en Σn n≤l = ⊢sub (⊢strengthen ⊢e en sdh-□ n≤l) (≈strengthen A≈Σ Σn n≤l) (↓-gc p) (ts Σ≢□)
  where ts : ∀ {Σ n} → ¬□ Σ → ¬□ (Σ ⇩ n)
        ts {τ x} nh = nh
        ts {[ x ]↝ Σ} nh = ¬□-term

≈a-strengthen-0 : ∀ {Γ A B Σ}
  → Γ , A ⊢ B ≈ Σ ⇧ 0
  → Γ ⊢ B ≈ Σ
≈a-strengthen-0 {Σ = Σ} B≤Σ with ≈strengthen {n = 0} B≤Σ ⇧-shiftedh z≤n
... | ind-h rewrite ⇧-⇩-id Σ 0 = ind-h  

⊢-strengthen-0 : ∀ {Γ Σ e A B}
  → Γ , A ⊢ Σ ⇧ 0 ⇒ e ↑ 0 ⇒ B
  → Γ ⊢ Σ ⇒ e ⇒ B
⊢-strengthen-0 {Σ = Σ} {e = e} ⊢e with ⊢strengthen {n = 0} ⊢e ↑-shifted ⇧-shiftedh z≤n
... | ind-e rewrite ↑-↓-id e 0 | ⇧-⇩-id Σ 0  = ind-e

----------------------------------------------------------------------
--+                      General Subsumption                       +--
----------------------------------------------------------------------

-- a aux judgment to prove the general subsumption
-- chain e̅ Σ Σ' simply put the e̅ onto Σ and the result is Σ'
-- thus the variant would be [ e̅ ]↝ Σ ≡ Σ'
data chain : List Term → Context → Context → Set where
  ch-none : ∀ {Σ}
    → chain [] Σ Σ

  ch-cons : ∀ {Σ e es Σ'}
    → chain es Σ Σ'
    → chain (e ∷ es) Σ ([ e ]↝ Σ')

ch-weaken : ∀ {es Σ' Σ n}
  → chain es Σ' Σ
  → chain (map (_↑ n) es) (Σ' ⇧ n) (Σ ⇧ n)
ch-weaken ch-none = ch-none
ch-weaken (ch-cons ch) = ch-cons (ch-weaken ch)


-- the typing implies a mathcing
-- we prove it simultaneously with general subsumption
⊢to≈ : ∀ {Γ e Σ A}
  → Γ ⊢ Σ ⇒ e ⇒ A
  → Γ ⊢ A ≈ Σ

-- the general subsumption
-- the intuition is we extract all the terms out of the context: e̅
-- then chain this argument to some arbitrary context Σ''
-- if the new Σ' matches the type A, then the e can infers A under such context
subsumption : ∀ {Γ Σ e A Σ' Σ'' es As A'}
  → Γ ⊢ Σ ⇒ e ⇒ A
  → ⟦ Σ , A ⟧→⟦ es , □ , As , A' ⟧
  → chain es Σ'' Σ'
  → Γ ⊢ A ≈ Σ'
  → Γ ⊢ Σ' ⇒ e ⇒ A

subsumption {Σ' = □} ⊢e none-□ ch-none ≈□ = ⊢e
subsumption {Σ' = τ _} ⊢lit spl ch A≤Σ' = ⊢sub ⊢lit A≤Σ' gc-lit ¬□-τ
subsumption {Σ' = τ _} (⊢var x) spl ch A≤Σ' = ⊢sub (⊢var x) A≤Σ' gc-var ¬□-τ
subsumption {Σ' = τ _} (⊢ann ⊢e) spl ch A≤Σ' = ⊢sub (⊢ann ⊢e) A≤Σ' gc-ann ¬□-τ
subsumption {Σ' = τ _} (⊢app ⊢e) spl ch A≤Σ' with ⊢to≈ ⊢e
... | ≈term x r = ⊢app (subsumption ⊢e (have spl) (ch-cons ch) (≈term x A≤Σ'))
subsumption {Σ' = τ _} (⊢lam₂ ⊢e ⊢e₁) (have spl) () A≤Σ'
subsumption {Σ' = τ _} (⊢sub ⊢e x x₁ x₂) spl ch A≤Σ' = ⊢sub ⊢e A≤Σ' x₁ ¬□-τ
subsumption {Σ' = [ e ]↝ Σ'} (⊢var x) spl ch A≤Σ' = ⊢sub (⊢var x) A≤Σ' gc-var ¬□-term
subsumption {Σ' = [ e ]↝ Σ'} (⊢ann ⊢e) spl ch A≤Σ' = ⊢sub (⊢ann ⊢e) A≤Σ' gc-ann ¬□-term
subsumption {Σ' = [ e ]↝ Σ'} (⊢app ⊢e) spl ch A≤Σ' with ⊢to≈ ⊢e
... | ≈term x r = ⊢app (subsumption ⊢e (have spl) (ch-cons ch) (≈term x A≤Σ'))
subsumption {Σ' = [ _ ]↝ Σ'} (⊢lam₂ ⊢e ⊢e₁) (have spl) (ch-cons ch) (≈term x A≤Σ') =
  ⊢lam₂ ⊢e (subsumption ⊢e₁ (spl-weaken spl) (ch-weaken ch) (≈weaken {n≤l = z≤n} A≤Σ'))
subsumption {Σ' = [ e ]↝ Σ'} (⊢sub ⊢e x x₁ x₂) spl ch A≤Σ' = ⊢sub ⊢e A≤Σ' x₁ ¬□-term
  
⊢to≈ ⊢lit = ≈□
⊢to≈ (⊢var x) = ≈□
⊢to≈ (⊢ann ⊢e) = ≈□
⊢to≈ (⊢app ⊢e) with ⊢to≈ ⊢e
... | ≈term ⊢e A≈Σ = A≈Σ
⊢to≈ (⊢lam₁ ⊢e) with ⊢to≈ ⊢e
... | ≈τ = ≈τ
⊢to≈ (⊢lam₂ ⊢e ⊢f) = ≈term (rebase ⊢e ≈τ) (≈a-strengthen-0 (⊢to≈ ⊢f))
  where
    rebase : ∀ {Γ e A B}
      → Γ ⊢ □  ⇒ e ⇒ B
      → Γ ⊢ B ≈ τ A
      → Γ ⊢ τ A ⇒ e ⇒ B
    rebase ⊢f B≤A = subsumption ⊢f none-□ ch-none B≤A
⊢to≈ (⊢sub ⊢e x x₁ Σ≢□) = x

-- the subsumption rule without side conditions can be derived
subsumption-0 : ∀ {Γ Σ e A}
  → Γ ⊢ □  ⇒ e ⇒ A
  → Γ ⊢ A ≈ Σ
  → Γ ⊢ Σ ⇒ e ⇒ A
subsumption-0 ⊢e A≈Σ = subsumption ⊢e none-□ ch-none A≈Σ  

----------------------------------------------------------------------
--+                             Check                              +--
----------------------------------------------------------------------

-- if the context is a full type, then the inferred type should be same with the context
⊢context-full-type : ∀ {Γ e A B}
  → Γ ⊢ τ A ⇒ e ⇒ B
  → A ≡ B
⊢context-full-type ⊢e with ⊢to≈ ⊢e
... | ≈τ = refl
