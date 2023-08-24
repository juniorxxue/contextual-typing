module SubGen.Algo.Properties where

open import SubGen.Prelude hiding (_≤?_) renaming (_≤_ to _≤n_)
open import SubGen.Common
open import SubGen.Properties
open import SubGen.Algo

----------------------------------------------------------------------
--                                                                  --
--                            Subtyping                             --
--                                                                  --
----------------------------------------------------------------------

{-
-- inversion lemmas

≤a-hint-inv₁ : ∀ {Γ H A B e}
  → Γ ⊢a A ⇒ B ≤ ⟦ e ⟧⇒ H
  → ∃[ C ] Γ ⊢a τ A ⇛ e ⇛ C
≤a-hint-inv₁ (≤a-hint {C = C} x ≤a) = ⟨ C , x ⟩

≤a-hint-inv₂ : ∀ {Γ H A B e}
  → Γ ⊢a A ⇒ B ≤ ⟦ e ⟧⇒ H
  → Γ ⊢a B ≤ H
≤a-hint-inv₂ (≤a-hint x ≤) = ≤
-}

{-
-- this lemma is obviously wrong

≤a-refl-τ : ∀ {Γ A B C}
  → Γ ⊢a B ≤ τ A ⇝ C
  → A ≢ Top
  → C ≡ A
≤a-refl-τ ≤a-int neq = refl
≤a-refl-τ ≤a-base neq = refl
≤a-refl-τ ≤a-top neq = ⊥-elim (neq refl)
≤a-refl-τ (≤a-arr B≤A B≤A₁) neq = {!!}
≤a-refl-τ (≤a-and-l B≤A) neq = ≤a-refl-τ B≤A neq
≤a-refl-τ (≤a-and-r B≤A) neq = ≤a-refl-τ B≤A neq
≤a-refl-τ (≤a-and B≤A B≤A₁) neq = {!!}

⊢a-refl : ∀ {Γ A B e}
  → Γ ⊢a τ A ⇛ e ⇛ B
  → A ≢ Top
  → B ≡ A
⊢a-refl ⊢a-lit neq = ⊥-elim (neq refl)
⊢a-refl (⊢a-var x) neq =  ⊥-elim (neq refl)
⊢a-refl (⊢a-app ⊢e) neq = {!!}
⊢a-refl (⊢a-ann ⊢e) neq =  ⊥-elim (neq refl)
⊢a-refl (⊢a-lam₁ ⊢e) neq = {!⊢a-refl ⊢e!} -- A -> Top
⊢a-refl (⊢a-lam₃ ⊢e ⊢e₁) neq = {!⊢a-refl ⊢e₁!} -- Top & Top
⊢a-refl (⊢a-sub x ⊢e x₁) neq = ≤a-refl-τ x₁ neq

-}

----------------------------------------------------------------------
--+                                                                +--
--+                             Shift                              +--
--+                                                                +--
----------------------------------------------------------------------

⇧-⇧-comm : ∀ H m n
  → m ≤n n
  → H ⇧ m ⇧ suc n ≡ H ⇧ n ⇧ m
⇧-⇧-comm (τ A) m n m≤n = refl
⇧-⇧-comm (⟦ e ⟧⇒ H) m n m≤n rewrite ↑-↑-comm e m n m≤n | ⇧-⇧-comm H m n m≤n = refl

⇧-⇩-id : ∀ H n
  → H ⇧ n ⇩ n ≡ H
⇧-⇩-id (τ A) n = refl
⇧-⇩-id (⟦ e ⟧⇒ H) n rewrite ↑-↓-id e n | ⇧-⇩-id H n = refl


infix 4 _~⇧~_
data _~⇧~_ : Hint → ℕ → Set where

  sdh-τ : ∀ {n A}
    → (τ A) ~⇧~ n

  sdh-h : ∀ {n e H}
    → e ~↑~ n
    → H ~⇧~ n
    → (⟦ e ⟧⇒ H) ~⇧~ n

⇧-shiftedh : ∀ {H n}
  → (H ⇧ n) ~⇧~ n
⇧-shiftedh {τ A} = sdh-τ
⇧-shiftedh {⟦ e ⟧⇒ H} = sdh-h ↑-shifted ⇧-shiftedh

⇧-shiftedh-n : ∀ {H m n}
  → m ≤n suc n
  → H ~⇧~ n
  → (H ⇧ m) ~⇧~ suc n
⇧-shiftedh-n {τ A} m≤n sdh = sdh-τ
⇧-shiftedh-n {⟦ e ⟧⇒ H} m≤n (sdh-h sd sdh) = sdh-h (↑-shifted-n m≤n sd) (⇧-shiftedh-n m≤n sdh)

⇩-⇧-comm : ∀ H m n
  → m ≤n n
  → H ~⇧~ n
  → H ⇩ n ⇧ m ≡ H ⇧ m ⇩ (suc n)
⇩-⇧-comm (τ A) m n m≤n sdh = refl
⇩-⇧-comm (⟦ e ⟧⇒ H) m n m≤n (sdh-h sd sdh) rewrite ↓-↑-comm e m n m≤n sd rewrite ⇩-⇧-comm H m n m≤n sdh = refl

----------------------------------------------------------------------
--+                                                                +--
--+                           Weakening                            +--
--+                                                                +--
----------------------------------------------------------------------

≤a-weaken : ∀ {Γ A B C H n n≤l}
  → Γ ⊢a B ≤ H ⇝ C
  → Γ ↑ n [ n≤l ] A ⊢a B ≤ (H ⇧ n) ⇝ C

⊢a-weaken : ∀ {Γ e H A B n n≤l}
  → Γ ⊢a H ⇛ e ⇛ B
  → Γ ↑ n [ n≤l ] A ⊢a H ⇧ n ⇛ e ↑ n ⇛ B

≤a-weaken ≤a-int = ≤a-int
≤a-weaken ≤a-base = ≤a-base
≤a-weaken ≤a-top = ≤a-top
≤a-weaken (≤a-arr C≤A B≤D) = ≤a-arr (≤a-weaken C≤A) (≤a-weaken B≤D)
≤a-weaken (≤a-hint ⊢e B≤H) = ≤a-hint (⊢a-weaken ⊢e) (≤a-weaken B≤H)
≤a-weaken (≤a-and-l ≤) = ≤a-and-l (≤a-weaken ≤)
≤a-weaken (≤a-and-r ≤) = ≤a-and-r (≤a-weaken ≤)
≤a-weaken (≤a-and ≤₁ ≤₂) = ≤a-and (≤a-weaken ≤₁) (≤a-weaken ≤₂)

⇧-⇧-comm-0 : ∀ H n
  → H ⇧ n ⇧ 0 ≡ H ⇧ 0 ⇧ (suc n)
⇧-⇧-comm-0 H n rewrite ⇧-⇧-comm H 0 n z≤n = refl

⊢a-weaken ⊢a-lit = ⊢a-lit
⊢a-weaken {n≤l = n≤l} (⊢a-var x∈Γ) = ⊢a-var (∋-weaken x∈Γ n≤l)
⊢a-weaken (⊢a-app ⊢e) = ⊢a-app (⊢a-weaken ⊢e)
⊢a-weaken (⊢a-ann ⊢e) = ⊢a-ann (⊢a-weaken ⊢e)
⊢a-weaken {n≤l = n≤l} (⊢a-lam₁ ⊢e) = ⊢a-lam₁ (⊢a-weaken {n≤l = s≤s n≤l} ⊢e)
⊢a-weaken {H = ⟦ _ ⟧⇒ H} {A = A} {n = n} {n≤l = n≤l} (⊢a-lam₂ ⊢e ⊢f) with ⊢a-weaken {A = A} {n = suc n} {n≤l = s≤s n≤l} ⊢f
... | ind-f rewrite sym (⇧-⇧-comm-0 H n) = ⊢a-lam₂ (⊢a-weaken ⊢e) ind-f
⊢a-weaken (⊢a-lam₃ ⊢1 ⊢2) = ⊢a-lam₃ (⊢a-weaken ⊢1) (⊢a-weaken ⊢2)
⊢a-weaken (⊢a-sub pv ⊢e B≤H) = ⊢a-sub (↑-pv-prv pv) (⊢a-weaken ⊢e) (≤a-weaken B≤H)

spl-weaken : ∀ {H A es T As A' n}
  → ❪ H , A ❫↣❪ es , T , As , A' ❫
  → ❪ H ⇧ n , A ❫↣❪ map (_↑ n) es , T , As , A' ❫
spl-weaken {T = T} none = none
spl-weaken (have spl) = have (spl-weaken spl)


----------------------------------------------------------------------
--+                                                                +--
--+                         Strengthening                          +--
--+                                                                +--
----------------------------------------------------------------------

≤a-strengthen : ∀ {Γ A B H n}
  → Γ ⊢a A ≤ H ⇝ B
  → H ~⇧~ n
  → (n≤l : n ≤n length Γ)
  → Γ ↓ n [ n≤l ] ⊢a A ≤ (H ⇩ n) ⇝ B
  
⊢a-strengthen : ∀ {Γ A H n e}
  → Γ ⊢a H ⇛ e ⇛ A -- H, e is shifted
  → e ~↑~ n
  → H ~⇧~ n
  → (n≤l : n ≤n length Γ)
  → Γ ↓ n [ n≤l ] ⊢a (H ⇩ n) ⇛ e ↓ n ⇛ A

≤a-strengthen ≤a-int sdh n≤l = ≤a-int
≤a-strengthen ≤a-base sdh n≤l = ≤a-base
≤a-strengthen ≤a-top sdh n≤l = ≤a-top
≤a-strengthen (≤a-arr A≤H A≤H₁) sdh n≤l = ≤a-arr (≤a-strengthen A≤H sdh-τ n≤l) (≤a-strengthen A≤H₁ sdh-τ n≤l)
≤a-strengthen (≤a-hint ⊢e A≤H) (sdh-h sd sdh) n≤l = ≤a-hint (⊢a-strengthen ⊢e sd sdh-τ n≤l) (≤a-strengthen A≤H sdh n≤l)
≤a-strengthen (≤a-and-l x₁) x n≤l = ≤a-and-l (≤a-strengthen x₁ x n≤l)
≤a-strengthen (≤a-and-r x₁) x n≤l = ≤a-and-r (≤a-strengthen x₁ x n≤l)
≤a-strengthen (≤a-and x₁ x₂) x n≤l = ≤a-and (≤a-strengthen x₁ sdh-τ n≤l) (≤a-strengthen x₂ sdh-τ n≤l)

⊢a-strengthen ⊢a-lit sd sdh n≤l = ⊢a-lit
⊢a-strengthen (⊢a-var x∈Γ) sd sdh n≤l = ⊢a-var (∋-strenghthen x∈Γ sd n≤l)
⊢a-strengthen (⊢a-app ⊢e) (sd-app sd₁ sd₂) sdh n≤l = ⊢a-app (⊢a-strengthen ⊢e sd₁ (sdh-h sd₂ sdh) n≤l)
⊢a-strengthen (⊢a-ann ⊢e) (sd-ann sd) sdh n≤l = ⊢a-ann (⊢a-strengthen ⊢e sd sdh-τ n≤l)
⊢a-strengthen (⊢a-lam₁ ⊢e) (sd-lam sd) sdh n≤l = ⊢a-lam₁ (⊢a-strengthen ⊢e sd sdh-τ (s≤s n≤l))
⊢a-strengthen {H = ⟦ _ ⟧⇒ H} {n = n} (⊢a-lam₂ ⊢e ⊢f) (sd-lam sd₁) (sdh-h sd₂ sdh) n≤l with ⊢a-strengthen ⊢f sd₁ (⇧-shiftedh-n z≤n sdh) (s≤s n≤l)
... | ind-f rewrite sym (⇩-⇧-comm H 0 n z≤n sdh) = ⊢a-lam₂ (⊢a-strengthen ⊢e sd₂ sdh-τ n≤l) ind-f
⊢a-strengthen (⊢a-lam₃ x₁ x₂) (sd-lam x₃) sdh-τ n≤l = ⊢a-lam₃ (⊢a-strengthen x₁ (sd-lam x₃) sdh-τ n≤l) (⊢a-strengthen x₂ (sd-lam x₃) sdh-τ n≤l)
⊢a-strengthen (⊢a-sub pv ⊢e A≤H) sd sdh n≤l = ⊢a-sub (↓-pv-prv pv) (⊢a-strengthen ⊢e sd sdh-τ n≤l) (≤a-strengthen A≤H sdh n≤l)

≤a-strengthen-0 : ∀ {Γ A B C H}
  → Γ , A ⊢a B ≤ H ⇧ 0 ⇝ C
  → Γ ⊢a B ≤ H ⇝ C
≤a-strengthen-0 {H = H} B≤H with ≤a-strengthen {n = 0} B≤H ⇧-shiftedh z≤n
... | ind-h rewrite ⇧-⇩-id H 0 = ind-h  

⊢a-strengthen-0 : ∀ {Γ H e A B}
  → Γ , A ⊢a H ⇧ 0 ⇛ e ↑ 0 ⇛ B
  → Γ ⊢a H ⇛ e ⇛ B
⊢a-strengthen-0 {H = H} {e = e} ⊢e with ⊢a-strengthen {n = 0} ⊢e ↑-shifted ⇧-shiftedh z≤n
... | ind-e rewrite ↑-↓-id e 0 | ⇧-⇩-id H 0  = ind-e

-- meta judgment

data _⊢m_≤_ : Context → Type → Hint → Set where
  ≤a-int : ∀ {Γ}
    → Γ ⊢m Int ≤ τ Int
  ≤a-base : ∀ {Γ n}
    → Γ ⊢m * n ≤ τ (* n)
  ≤a-top : ∀ {Γ A}
    → Γ ⊢m A ≤ τ Top
  ≤a-arr : ∀ {Γ A B C D}
    → Γ ⊢m C ≤ τ A
    → Γ ⊢m B ≤ τ D
    ---------------------------
    → Γ ⊢m (A ⇒ B) ≤ τ (C ⇒ D)
  ≤a-hint : ∀ {Γ A B C H e}
    → Γ ⊢a τ A ⇛ e ⇛ C
    → Γ ⊢m B ≤ H
    ------------------------
    → Γ ⊢m A ⇒ B ≤ (⟦ e ⟧⇒ H)
  ≤a-and-l : ∀ {Γ A B H}
    → Γ ⊢m A ≤ H
    → Γ ⊢m A & B ≤ H
  ≤a-and-r : ∀ {Γ A B H}
    → Γ ⊢m B ≤ H
    → Γ ⊢m A & B ≤ H
  ≤a-and : ∀ {Γ A B C}
    → Γ ⊢m A ≤ τ B
    → Γ ⊢m A ≤ τ C
    → Γ ⊢m A ≤ τ (B & C)

≤m-refl : ∀ {Γ A} → Γ ⊢m A ≤ τ A
≤m-refl {A = Int} = ≤a-int
≤m-refl {A = * x} = ≤a-base
≤m-refl {A = Top} = ≤a-top
≤m-refl {A = A ⇒ A₁} = ≤a-arr ≤m-refl ≤m-refl
≤m-refl {A = A & A₁} = ≤a-and (≤a-and-l ≤m-refl) (≤a-and-r ≤m-refl)

≤a-to-≤m : ∀ {Γ A H A'}
  → Γ ⊢a A ≤ H ⇝ A'
  → Γ ⊢m A ≤ H
≤a-to-≤m ≤a-int = ≤a-int
≤a-to-≤m ≤a-base = ≤a-base
≤a-to-≤m ≤a-top = ≤a-top
≤a-to-≤m (≤a-arr A≤H A≤H₁) = ≤a-arr (≤a-to-≤m A≤H) (≤a-to-≤m A≤H₁)
≤a-to-≤m (≤a-hint x A≤H) = ≤a-hint x (≤a-to-≤m A≤H)
≤a-to-≤m (≤a-and-l A≤H) = ≤a-and-l (≤a-to-≤m A≤H)
≤a-to-≤m (≤a-and-r A≤H) = ≤a-and-r (≤a-to-≤m A≤H)
≤a-to-≤m (≤a-and A≤H A≤H₁) = ≤a-and (≤a-to-≤m A≤H) (≤a-to-≤m A≤H₁)

≤a-refine-prv₁ : ∀ {Γ A A' H}
  → Γ ⊢a A ≤ H ⇝ A'
  → Γ ⊢m A ≤ τ A'

≤a-refine-prv₂ : ∀ {Γ A A' H}
  → Γ ⊢a A ≤ H ⇝ A'
  → Γ ⊢m A' ≤ H
 
≤a-refine-prv₁ ≤a-int = ≤a-int
≤a-refine-prv₁ ≤a-base = ≤a-base
≤a-refine-prv₁ ≤a-top = ≤m-refl
≤a-refine-prv₁ (≤a-arr C≤A B≤D) = ≤a-arr (≤a-refine-prv₂ C≤A) (≤a-refine-prv₁ B≤D)
≤a-refine-prv₁ (≤a-hint ⊢e B≤H) = ≤a-arr ≤m-refl (≤a-refine-prv₁ B≤H)
≤a-refine-prv₁ (≤a-and-l A≤H) = ≤a-and-l (≤a-refine-prv₁ A≤H)
≤a-refine-prv₁ (≤a-and-r A≤H) = ≤a-and-r (≤a-refine-prv₁ A≤H)
≤a-refine-prv₁ (≤a-and A≤B A≤C) = ≤a-and (≤a-refine-prv₁ A≤B) (≤a-refine-prv₁ A≤C)

≤a-refine-prv₂ ≤a-int = ≤a-int
≤a-refine-prv₂ ≤a-base = ≤a-base
≤a-refine-prv₂ ≤a-top = ≤a-top
≤a-refine-prv₂ (≤a-arr C≤A B≤D) = ≤a-arr (≤a-refine-prv₁ C≤A) (≤a-refine-prv₂ B≤D)
≤a-refine-prv₂ (≤a-hint ⊢e B≤H) = ≤a-hint ⊢e (≤a-refine-prv₂ B≤H)
≤a-refine-prv₂ (≤a-and-l A≤H) = ≤a-refine-prv₂ A≤H
≤a-refine-prv₂ (≤a-and-r A≤H) = ≤a-refine-prv₂ A≤H
≤a-refine-prv₂ (≤a-and A≤B A≤C) = ≤a-and (≤a-and-l (≤a-refine-prv₂ A≤B)) (≤a-and-r (≤a-refine-prv₂ A≤C))
