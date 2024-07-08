module STLC.Algo.Properties where

open import STLC.Prelude hiding (_≤?_) renaming (_≤_ to _≤n_)
open import STLC.Common
open import STLC.Properties
open import STLC.Algo

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
⇩-⇧-comm (□) m n m≤n sdh = refl
⇩-⇧-comm (τ A) m n m≤n sdh = refl
⇩-⇧-comm (⟦ e ⟧⇒ H) m n m≤n (sdh-h sd sdh) rewrite ↓-↑-comm e m n m≤n sd rewrite ⇩-⇧-comm H m n m≤n sdh = refl

----------------------------------------------------------------------
--+                                                                +--
--+                           Weakening                            +--
--+                                                                +--
----------------------------------------------------------------------

↑-pv : ∀ {e n}
  → pv e
  → pv (e ↑ n)
↑-pv pv-lit = pv-lit
↑-pv pv-var = pv-var
↑-pv pv-ann = pv-ann

↓-pv : ∀ {e n}
  → pv e
  → pv (e ↓ n)
↓-pv pv-lit = pv-lit
↓-pv pv-var = pv-var
↓-pv pv-ann = pv-ann

≈a-weaken : ∀ {Γ A B H n n≤l}
  → Γ ⊢a B ≈ H
  → Γ ↑ n [ n≤l ] A ⊢a B ≈ (H ⇧ n)

⊢a-weaken : ∀ {Γ e H A B n n≤l}
  → Γ ⊢a H ⇛ e ⇛ B
  → Γ ↑ n [ n≤l ] A ⊢a H ⇧ n ⇛ e ↑ n ⇛ B

≈a-weaken ≈□ = ≈□
≈a-weaken ≈τ = ≈τ
≈a-weaken (≈hole ⊢e B≈H) = ≈hole (⊢a-weaken ⊢e) (≈a-weaken B≈H)

⇧-⇧-comm-0 : ∀ H n
  → H ⇧ n ⇧ 0 ≡ H ⇧ 0 ⇧ (suc n)
⇧-⇧-comm-0 H n rewrite ⇧-⇧-comm H 0 n z≤n = refl

⊢a-weaken ⊢a-lit = ⊢a-lit
⊢a-weaken {n≤l = n≤l} (⊢a-var x∈Γ) = ⊢a-var (∋-weaken x∈Γ n≤l)
⊢a-weaken (⊢a-ann ⊢e) = ⊢a-ann (⊢a-weaken ⊢e)
⊢a-weaken (⊢a-app ⊢e) = ⊢a-app (⊢a-weaken ⊢e)
⊢a-weaken {n≤l = n≤l} (⊢a-lam₁ ⊢e) = ⊢a-lam₁ (⊢a-weaken {n≤l = s≤s n≤l} ⊢e)
⊢a-weaken {H = ⟦ _ ⟧⇒ H} {A = A} {n = n} {n≤l = n≤l} (⊢a-lam₂ ⊢e ⊢f) with ⊢a-weaken {A = A} {n = suc n} {n≤l = s≤s n≤l} ⊢f
... | ind-f rewrite sym (⇧-⇧-comm-0 H n) = ⊢a-lam₂ (⊢a-weaken ⊢e) ind-f
⊢a-weaken (⊢a-sub ⊢e B≈H p) = ⊢a-sub (⊢a-weaken ⊢e) (≈a-weaken B≈H) (↑-pv p)

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

≈a-strengthen : ∀ {Γ A H n}
  → Γ ⊢a A ≈ H
  → H ~⇧~ n
  → (n≤l : n ≤n length Γ)
  → Γ ↓ n [ n≤l ] ⊢a A ≈ (H ⇩ n)
  
⊢a-strengthen : ∀ {Γ A H n e}
  → Γ ⊢a H ⇛ e ⇛ A -- H, e is shifted
  → e ~↑~ n
  → H ~⇧~ n
  → (n≤l : n ≤n length Γ)
  → Γ ↓ n [ n≤l ] ⊢a (H ⇩ n) ⇛ e ↓ n ⇛ A

≈a-strengthen ≈□ Hn n≤l = ≈□
≈a-strengthen ≈τ Hn n≤l = ≈τ
≈a-strengthen (≈hole ⊢e A≈H) (sdh-h x Hn) n≤l = ≈hole (⊢a-strengthen ⊢e x sdh-τ n≤l) (≈a-strengthen A≈H Hn n≤l)

⊢a-strengthen ⊢a-lit en Hn n≤l = ⊢a-lit
⊢a-strengthen (⊢a-var x∈Γ) en Hn n≤l = ⊢a-var (∋-strenghthen x∈Γ en n≤l)
⊢a-strengthen (⊢a-ann ⊢e) (sd-ann en) Hn n≤l = ⊢a-ann (⊢a-strengthen ⊢e en sdh-τ n≤l)
⊢a-strengthen (⊢a-app ⊢e) (sd-app en en₁) Hn n≤l = ⊢a-app (⊢a-strengthen ⊢e en (sdh-h en₁ Hn) n≤l)
⊢a-strengthen (⊢a-lam₁ ⊢e) (sd-lam sd) sdh n≤l = ⊢a-lam₁ (⊢a-strengthen ⊢e sd sdh-τ (s≤s n≤l))
⊢a-strengthen {H = ⟦ _ ⟧⇒ H} {n = n} (⊢a-lam₂ ⊢e ⊢f) (sd-lam sd₁) (sdh-h sd₂ sdh) n≤l with ⊢a-strengthen ⊢f sd₁ (⇧-shiftedh-n z≤n sdh) (s≤s n≤l)
... | ind-f rewrite sym (⇩-⇧-comm H 0 n z≤n sdh) = ⊢a-lam₂ (⊢a-strengthen ⊢e sd₂ sdh-□ n≤l) ind-f
⊢a-strengthen (⊢a-sub ⊢e A≈H p) en Hn n≤l = ⊢a-sub (⊢a-strengthen ⊢e en sdh-□ n≤l) (≈a-strengthen A≈H Hn n≤l) (↓-pv p)

≈a-strengthen-0 : ∀ {Γ A B H}
  → Γ , A ⊢a B ≈ H ⇧ 0
  → Γ ⊢a B ≈ H
≈a-strengthen-0 {H = H} B≤H with ≈a-strengthen {n = 0} B≤H ⇧-shiftedh z≤n
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

⊢a-to-≈a : ∀ {Γ e H A}
  → Γ ⊢a H ⇛ e ⇛ A
  → Γ ⊢a A ≈ H

subsumption : ∀ {Γ H e A H' H'' es As A'}
  → Γ ⊢a H ⇛ e ⇛ A
  → ❪ H , A ❫↣❪ es , □ , As , A' ❫
  → chain es H'' H'
  → Γ ⊢a A ≈ H'
  → Γ ⊢a H' ⇛ e ⇛ A
  
⊢a-to-≈a ⊢a-lit = ≈□
⊢a-to-≈a (⊢a-var x) = ≈□
⊢a-to-≈a (⊢a-ann ⊢e) = ≈□
⊢a-to-≈a (⊢a-app ⊢e) with ⊢a-to-≈a ⊢e
... | ≈hole ⊢e A≈H = A≈H
⊢a-to-≈a (⊢a-lam₁ ⊢e) with ⊢a-to-≈a ⊢e
... | ≈τ = ≈τ
⊢a-to-≈a (⊢a-lam₂ ⊢e ⊢f) = ≈hole (rebase ⊢e ≈τ) (≈a-strengthen-0 (⊢a-to-≈a ⊢f))
  where
    rebase : ∀ {Γ e A B}
      → Γ ⊢a □  ⇛ e ⇛ B
      → Γ ⊢a B ≈ τ A
      → Γ ⊢a τ A ⇛ e ⇛ B
    rebase ⊢f B≤A = subsumption ⊢f none-□ ch-none B≤A
⊢a-to-≈a (⊢a-sub ⊢e x x₁) = x

subsumption ⊢a-lit spl ch A≈H' = ⊢a-sub ⊢a-lit A≈H' pv-lit
subsumption (⊢a-var x) spl ch A≈H' = ⊢a-sub (⊢a-var x) A≈H' pv-var
subsumption (⊢a-ann ⊢e) spl ch A≈H' = ⊢a-sub (⊢a-ann ⊢e) A≈H' pv-ann
subsumption (⊢a-app ⊢e) spl ch A≈H with ⊢a-to-≈a ⊢e
... | ≈hole ⊢e' A≈H' = ⊢a-app (subsumption ⊢e (have spl) (ch-cons ch) (≈hole ⊢e' A≈H))
subsumption (⊢a-lam₂ ⊢e ⊢e₁) (have spl) (ch-cons ch) (≈hole x A≈H') =
  ⊢a-lam₂ ⊢e (subsumption ⊢e₁ (spl-weaken spl) (ch-weaken ch) (≈a-weaken {n≤l = z≤n} A≈H'))
subsumption (⊢a-sub ⊢e x x₁) spl ch A≈H' = ⊢a-sub ⊢e A≈H' x₁


subsumption-0 : ∀ {Γ H e A}
  → Γ ⊢a □  ⇛ e ⇛ A
  → Γ ⊢a A ≈ H
  → Γ ⊢a H ⇛ e ⇛ A
subsumption-0 ⊢e A≈H = subsumption ⊢e none-□ ch-none A≈H  

----------------------------------------------------------------------
--+                                                                +--
--+                             Check                              +--
--+                                                                +--
----------------------------------------------------------------------

⊢a-hint-self : ∀ {Γ e A B}
  → Γ ⊢a τ A ⇛ e ⇛ B
  → A ≡ B
⊢a-hint-self ⊢e with ⊢a-to-≈a ⊢e
... | ≈τ = refl


⊢a-spl-eq : ∀ {Γ H A e es T As A'}
  → Γ ⊢a H ⇛ e ⇛ A
  → ❪ H , A ❫↣❪ es , τ T , As , A' ❫
  → T ≡ A'
⊢a-spl-eq ⊢e none-τ = ⊢a-hint-self ⊢e
⊢a-spl-eq ⊢e (have spl) = ⊢a-spl-eq (⊢a-app ⊢e) spl
