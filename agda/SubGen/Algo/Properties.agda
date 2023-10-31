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
⇧-⇧-comm □ m n m≤n = refl
⇧-⇧-comm (τ A) m n m≤n = refl
⇧-⇧-comm (⟦ e ⟧⇒ H) m n m≤n rewrite ↑-↑-comm e m n m≤n | ⇧-⇧-comm H m n m≤n = refl

⇧-⇩-id : ∀ H n
  → H ⇧ n ⇩ n ≡ H
⇧-⇩-id □ n = refl  
⇧-⇩-id (τ A) n = refl
⇧-⇩-id (⟦ e ⟧⇒ H) n rewrite ↑-↓-id e n | ⇧-⇩-id H n = refl


infix 4 _~⇧~_
data _~⇧~_ : Hint → ℕ → Set where

  sdh-□ : ∀ {n}
    → □ ~⇧~ n

  sdh-τ : ∀ {n A}
    → (τ A) ~⇧~ n

  sdh-h : ∀ {n e H}
    → e ~↑~ n
    → H ~⇧~ n
    → (⟦ e ⟧⇒ H) ~⇧~ n

⇧-shiftedh : ∀ {H n}
  → (H ⇧ n) ~⇧~ n
⇧-shiftedh {□} = sdh-□  
⇧-shiftedh {τ A} = sdh-τ
⇧-shiftedh {⟦ e ⟧⇒ H} = sdh-h ↑-shifted ⇧-shiftedh

⇧-shiftedh-n : ∀ {H m n}
  → m ≤n suc n
  → H ~⇧~ n
  → (H ⇧ m) ~⇧~ suc n
⇧-shiftedh-n {□} m≤n sdh = sdh-□
⇧-shiftedh-n {τ A} m≤n sdh = sdh-τ
⇧-shiftedh-n {⟦ e ⟧⇒ H} m≤n (sdh-h sd sdh) = sdh-h (↑-shifted-n m≤n sd) (⇧-shiftedh-n m≤n sdh)

⇩-⇧-comm : ∀ H m n
  → m ≤n n
  → H ~⇧~ n
  → H ⇩ n ⇧ m ≡ H ⇧ m ⇩ (suc n)
⇩-⇧-comm □ m n m≤n sdh = refl
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
≤a-weaken ≤a-□ = ≤a-□
≤a-weaken (≤a-arr C≤A B≤D) = ≤a-arr (≤a-weaken C≤A) (≤a-weaken B≤D)
≤a-weaken (≤a-hint ⊢e B≤H) = ≤a-hint (⊢a-weaken ⊢e) (≤a-weaken B≤H)
≤a-weaken (≤a-and-l ≤) = ≤a-and-l (≤a-weaken ≤)
≤a-weaken (≤a-and-r ≤) = ≤a-and-r (≤a-weaken ≤)
≤a-weaken (≤a-and ≤₁ ≤₂) = ≤a-and (≤a-weaken ≤₁) (≤a-weaken ≤₂)

≤a-weaken-0 : ∀ {Γ A B H C}
  → Γ ⊢a B ≤ H ⇝ C
  → Γ , A ⊢a B ≤ (H ⇧ 0) ⇝ C
≤a-weaken-0 B≤H = ≤a-weaken {n≤l = z≤n} B≤H  

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
⊢a-weaken (⊢a-sub pv ⊢e B≤H) = ⊢a-sub (↑-pv-prv pv) (⊢a-weaken ⊢e) (≤a-weaken B≤H)
⊢a-weaken (⊢a-& ⊢e₁ ⊢e₂) = ⊢a-& (⊢a-weaken ⊢e₁) (⊢a-weaken ⊢e₂)

spl-weaken : ∀ {H A es T As A' n}
  → ❪ H , A ❫↣❪ es , T , As , A' ❫
  → ❪ H ⇧ n , A ❫↣❪ map (_↑ n) es , T , As , A' ❫
spl-weaken {T = .□} none-□ = none-□
spl-weaken {T = .(τ _)} none-τ = none-τ
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
≤a-strengthen ≤a-□ sdh n≤l = ≤a-□
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
... | ind-f rewrite sym (⇩-⇧-comm H 0 n z≤n sdh) = ⊢a-lam₂ (⊢a-strengthen ⊢e sd₂ sdh-□ n≤l) ind-f
⊢a-strengthen (⊢a-sub pv ⊢e A≤H) sd sdh n≤l = ⊢a-sub (↓-pv-prv pv) (⊢a-strengthen ⊢e sd sdh-□ n≤l) (≤a-strengthen A≤H sdh n≤l)
⊢a-strengthen (⊢a-& ⊢e₁ ⊢e₂) sd sdh n≤l = ⊢a-& (⊢a-strengthen ⊢e₁ sd sdh-τ n≤l) (⊢a-strengthen ⊢e₂ sd sdh-τ n≤l)

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


----------------------------------------------------------------------
--+                                                                +--
--+                      General Subsumption                       +--
--+                                                                +--
----------------------------------------------------------------------


data chain : List Term → Hint → Hint → Set where
  ch-none : ∀ {H}
    → chain [] H H

  ch-cons : ∀ {H e es H'}
    → chain es H H'
    → chain (e ∷ es) H (⟦ e ⟧⇒ H')

ch-weaken : ∀ {es H' H n}
  → chain es H' H
  → chain (map (_↑ n) es) (H' ⇧ n) (H ⇧ n)
ch-weaken ch-none = ch-none
ch-weaken (ch-cons ch) = ch-cons (ch-weaken ch)


{-
⊢a-to-≤a : ∀ {Γ e H A}
  → Γ ⊢a H ⇛ e ⇛ A
  → ∃[ A' ] (Γ ⊢a A ≤ H ⇝ A')

subsumption : ∀ {Γ H e A H' H'' es As T A'}
  → Γ ⊢a H ⇛ e ⇛ A
  → ❪ H , A ❫↣❪ es , □ , As , T ❫
  → chain es H'' H'
  → Γ ⊢a A ≤ H' ⇝ A'
  → Γ ⊢a H' ⇛ e ⇛ A'

⊢a-to-≤a ⊢e = {!!}

subsumption ⊢a-lit none-□ ch A≤H' = ⊢a-sub pv-i ⊢a-lit A≤H'
subsumption (⊢a-var x) spl ch A≤H' = ⊢a-sub pv-var (⊢a-var x) A≤H'
subsumption (⊢a-ann ⊢e) spl ch A≤H' = ⊢a-sub pv-ann (⊢a-ann ⊢e) A≤H'
subsumption (⊢a-app ⊢e) spl ch A≤H' with ⊢a-to-≤a ⊢e
... | ⟨ .(_ ⇒ _) , ≤a-hint ⊢e' A≤H ⟩ = ⊢a-app (subsumption ⊢e (have spl) (ch-cons ch) (≤a-hint ⊢e' A≤H'))
subsumption (⊢a-lam₂ ⊢e ⊢e₁) spl ch A≤H' = {!!}
subsumption (⊢a-sub x ⊢e x₁) spl ch A≤H' = {!!}
-}

≤a-refined : ∀ {Γ A B H}
  → Γ ⊢a A ≤ H ⇝ B
  → Γ ⊢a B ≤ H ⇝ B
≤a-refined ≤a-int = ≤a-int
≤a-refined ≤a-base = ≤a-base
≤a-refined ≤a-top = ≤a-top
≤a-refined ≤a-□ = ≤a-□
≤a-refined (≤a-arr A≤H A≤H₁) = ≤a-arr ≤a-refl (≤a-refined A≤H₁)
≤a-refined (≤a-hint x A≤H) = ≤a-hint x (≤a-refined A≤H)
≤a-refined (≤a-and-l A≤H) = ≤a-refined A≤H
≤a-refined (≤a-and-r A≤H) = ≤a-refined A≤H
≤a-refined (≤a-and A≤H A≤H₁) = ≤a-and (≤a-and-l (≤a-refined A≤H)) (≤a-and-r (≤a-refined A≤H₁))

≤a-trans : ∀ {Γ A H H' H'' T es A' A'' As}
  → Γ ⊢a A ≤ H ⇝ A'
  → ❪ H , A' ❫↣❪ es , □ , As , T ❫
  → chain es H'' H'
  → Γ ⊢a A' ≤ H' ⇝ A''
  → Γ ⊢a A ≤ H' ⇝ A''
≤a-trans ≤a-□ none-□ ch-none A'≤H' = A'≤H'
≤a-trans (≤a-hint x A≤H) (have spl) (ch-cons ch) (≤a-hint x₁ A'≤H') = ≤a-hint x₁ (≤a-trans A≤H spl ch A'≤H')
≤a-trans (≤a-and-l A≤H) spl ch A'≤H' = ≤a-and-l (≤a-trans A≤H spl ch A'≤H')
≤a-trans (≤a-and-r A≤H) spl ch A'≤H' = ≤a-and-r (≤a-trans A≤H spl ch A'≤H')


⊢a-to-≤a : ∀ {Γ e H A}
  → Γ ⊢a H ⇛ e ⇛ A
  → Γ ⊢a A ≤ H ⇝ A

subsumption : ∀ {Γ H e A H' H'' es As T A'}
  → Γ ⊢a H ⇛ e ⇛ A
  → ❪ H , A ❫↣❪ es , □ , As , T ❫
  → chain es H'' H'
  → Γ ⊢a A ≤ H' ⇝ A'
  → Γ ⊢a H' ⇛ e ⇛ A'

⊢a-to-≤a ⊢a-lit = ≤a-□
⊢a-to-≤a (⊢a-var x) = ≤a-□
⊢a-to-≤a (⊢a-ann ⊢e) = ≤a-□
⊢a-to-≤a (⊢a-app ⊢e) with ⊢a-to-≤a ⊢e
... | ≤a-hint x r = r
⊢a-to-≤a (⊢a-lam₁ ⊢e) with ⊢a-to-≤a ⊢e
... | r rewrite ⊢a-id-0 ⊢e = ≤a-refl
⊢a-to-≤a (⊢a-lam₂ ⊢e ⊢e₁) = ≤a-hint (rebase ⊢e ≤a-refl) (≤a-strengthen-0 (⊢a-to-≤a ⊢e₁))
  where
    rebase : ∀ {Γ e A B B'}
      → Γ ⊢a □ ⇛ e ⇛ B
      → Γ ⊢a B ≤ τ A ⇝ B'
      → Γ ⊢a τ A ⇛ e ⇛ B'
    rebase ⊢f B≤A = subsumption ⊢f none-□ ch-none B≤A
⊢a-to-≤a (⊢a-sub x ⊢e x₁) = ≤a-refined x₁
⊢a-to-≤a (⊢a-& ⊢e₁ ⊢e₂) rewrite ⊢a-id-0 ⊢e₁ | ⊢a-id-0 ⊢e₂ = ≤a-refl

subsumption ⊢a-lit none-□ ch A≤H' = ⊢a-sub pv-i ⊢a-lit A≤H'
subsumption (⊢a-var x) spl ch A≤H' = ⊢a-sub pv-var (⊢a-var x) A≤H'
subsumption (⊢a-ann ⊢e) spl ch A≤H' = ⊢a-sub pv-ann (⊢a-ann ⊢e) A≤H'
subsumption (⊢a-app ⊢e) spl ch A≤H' with ⊢a-to-≤a ⊢e
... |  ≤a-hint ⊢e' A≤H = ⊢a-app (subsumption ⊢e (have spl) (ch-cons ch) (≤a-hint ⊢e' A≤H'))
subsumption (⊢a-lam₂ ⊢e ⊢e₁) (have spl) (ch-cons ch) (≤a-hint x A≈H') =
  ⊢a-lam₂ ⊢e (subsumption ⊢e₁ (spl-weaken spl) (ch-weaken ch) (≤a-weaken {n≤l = z≤n} A≈H'))
subsumption (⊢a-sub ⊢e x x₁) spl ch A≤H' = ⊢a-sub ⊢e x (≤a-trans x₁ spl ch A≤H')

subsumption-0 : ∀ {Γ H e A A'}
  → Γ ⊢a □ ⇛ e ⇛ A
  → Γ ⊢a A ≤ H ⇝ A'
  → Γ ⊢a H ⇛ e ⇛ A'
subsumption-0 ⊢e A≤H = subsumption ⊢e none-□ ch-none A≤H  

