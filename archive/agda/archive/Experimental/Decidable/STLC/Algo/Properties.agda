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
⊢a-weaken (⊢a-sub ⊢e B≈H H≢□ p) = ⊢a-sub (⊢a-weaken ⊢e) (≈a-weaken B≈H) {!!} (↑-pv p)

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
⊢a-strengthen (⊢a-sub ⊢e A≈H x p) en Hn n≤l = ⊢a-sub (⊢a-strengthen ⊢e en sdh-□ n≤l) (≈a-strengthen A≈H Hn n≤l) {!!} (↓-pv p)

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
subsumption = {!!}  
  
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
⊢a-to-≈a (⊢a-sub ⊢e x x₁ x₂) = x

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

----------------------------------------------------------------------
--+                                                                +--
--+                              Dec                               +--
--+                                                                +--
----------------------------------------------------------------------

n<o⇒n+0<o : ∀ {n o}
  → n < o
  → n + 0 < o
n<o⇒n+0<o {n} {o} n<o rewrite +-comm n 0 = n<o

m+n<o⇒m<o : ∀ m {n o}
  → m + n < o
  → m < o
m+n<o⇒m<o m m+n<o = m+n≤o⇒m≤o (suc m) m+n<o

m+n<o⇒n<o : ∀ n {m o}
  → m + n < o
  → n < o
m+n<o⇒n<o n {m} m+n<o rewrite +-comm m n = m+n<o⇒m<o n m+n<o

size-e : Term → ℕ
size-e (lit x) = 1
size-e (` x) = 1
size-e (ƛ e) = 1 + size-e e
size-e (e₁ · e₂) = 2 + size-e e₁ + size-e e₂
size-e (e ⦂ _) = 1 + size-e e

size-H : Hint → ℕ
size-H □ = 0
size-H (τ _) = 0
size-H (⟦ e ⟧⇒ H) = 1 + size-e e + size-H H

size-↑ : ∀ e {n}
  → size-e e ≡ size-e (e ↑ n)
size-↑ (lit x) {n} = refl
size-↑ (` x) {n} = refl
size-↑ (ƛ e) {n} rewrite size-↑ e {suc n} = refl
size-↑ (e · e₁) {n} rewrite size-↑ e {n} | size-↑ e₁ {n} = refl
size-↑ (e ⦂ _) {n} rewrite size-↑ e {n} = refl

size-⇧ : ∀ H {n}
  → size-H H ≡ size-H (H ⇧ n)
size-⇧ □ = refl
size-⇧ (τ _) = refl
size-⇧ (⟦ e ⟧⇒ H) {n} rewrite size-⇧ H {n} | size-↑ e {n} = refl

x∈Γ-unique : ∀ {Γ x A B}
  → Γ ∋ x ⦂ A
  → Γ ∋ x ⦂ B
  → A ≡ B
x∈Γ-unique {x = zero} Z Z = refl
x∈Γ-unique {x = suc x} (S A∈Γ) (S B∈Γ) rewrite x∈Γ-unique A∈Γ B∈Γ = refl

⊢a-unique : ∀ {Γ H e A B}
  → Γ ⊢a H ⇛ e ⇛ A
  → Γ ⊢a H ⇛ e ⇛ B
  → A ≡ B
⊢a-unique ⊢a-lit ⊢a-lit = refl
⊢a-unique ⊢a-lit (⊢a-sub ⊢2 A≈H H≢□ pv-e) = ⊥-elim (H≢□ refl)
⊢a-unique (⊢a-var x∈Γ) (⊢a-var x∈Γ₁) = x∈Γ-unique x∈Γ x∈Γ₁
⊢a-unique (⊢a-var x∈Γ) (⊢a-sub ⊢2 A≈H H≢□ pv-e) = ⊥-elim (H≢□ refl)
⊢a-unique (⊢a-ann ⊢1) (⊢a-ann ⊢2) = refl
⊢a-unique (⊢a-ann ⊢1) (⊢a-sub ⊢2 A≈H H≢□ pv-e) = ⊢a-unique (⊢a-ann ⊢1) ⊢2
⊢a-unique (⊢a-app ⊢1) (⊢a-app ⊢2) with ⊢a-unique ⊢1 ⊢2
... | refl = refl
⊢a-unique (⊢a-lam₁ ⊢1) (⊢a-lam₁ ⊢2) rewrite ⊢a-unique ⊢1 ⊢2 = refl
⊢a-unique (⊢a-lam₂ ⊢1 ⊢3) (⊢a-lam₂ ⊢2 ⊢4) rewrite ⊢a-unique ⊢1 ⊢2 | ⊢a-unique ⊢3 ⊢4 = refl
⊢a-unique (⊢a-sub ⊢a-lit A≈H H≢□ pv-e) ⊢a-lit = refl
⊢a-unique (⊢a-sub (⊢a-sub ⊢1 A≈H₁ H≢□₁ pv-e₁) A≈H H≢□ pv-e) ⊢a-lit = ⊢a-unique ⊢1 ⊢a-lit
⊢a-unique (⊢a-sub ⊢1 A≈H H≢□ pv-e) (⊢a-var x∈Γ) = ⊢a-unique ⊢1 (⊢a-var x∈Γ)
⊢a-unique (⊢a-sub ⊢1 A≈H H≢□ pv-e) (⊢a-ann ⊢2) = ⊢a-unique ⊢1 (⊢a-ann ⊢2)
⊢a-unique (⊢a-sub ⊢1 A≈H H≢□ pv-e) (⊢a-sub ⊢2 A≈H₁ H≢□₁ pv-e₁) = ⊢a-unique ⊢1 ⊢2

x∈Γ-dec : ∀ Γ n
  → Dec (∃[ A ] (Γ ∋ n ⦂ A))
x∈Γ-dec ∅ n = no λ ()
x∈Γ-dec (Γ , A) zero = yes ⟨ A , Z ⟩
x∈Γ-dec (Γ , A) (suc n) with x∈Γ-dec Γ n
... | yes ⟨ A' , x∈Γ ⟩ = yes ⟨ A' , S x∈Γ ⟩
... | no ¬p = no λ where
  ⟨ A' , S x∈Γ ⟩ → ¬p ⟨ A' , x∈Γ ⟩

τ-dec : ∀ (A B : Type)
  → Dec (A ≡ B)
τ-dec Int Int = yes refl
τ-dec Int (B ⇒ B₁) = no (λ ())
τ-dec (A ⇒ A₁) Int = no (λ ())
τ-dec (A ⇒ A₁) (B ⇒ B₁) with τ-dec A B | τ-dec A₁ B₁
... | yes p | yes p' rewrite p | p' = yes refl
... | yes p | no ¬p = no λ where
  refl → ¬p refl
... | no ¬p | _ = no λ where
  refl → ¬p refl

≈a-dec : ∀ k Γ H A
  → size-H H < k
  → Dec (Γ ⊢a A ≈ H) 

⊢a-dec : ∀ k Γ H e
  → size-e e + size-H H < k
  → Dec (∃[ A ](Γ ⊢a H ⇛ e ⇛ A))

private
  inv-case : ∀ {Γ x A A' e H}
    → Γ ∋ x ⦂ A
    → Γ ∋ x ⦂ A'
    → Γ ⊢a A' ≈ ⟦ e ⟧⇒ H
    → ¬ Γ ⊢a A ≈ ⟦ e ⟧⇒ H
    → ⊥
  inv-case x∈Γ x∈Γ' A≈H ¬A≈H' rewrite x∈Γ-unique x∈Γ x∈Γ' = ¬A≈H' A≈H

  inv-hole-int : ∀ {Γ e₁ e₂ H}
    → Γ ⊢a ⟦ e₂ ⟧⇒ H ⇛ e₁ ⇛ Int
    → ⊥
  inv-hole-int ⊢e with ⊢a-to-≈a ⊢e
  ... | ()

  inv-case-int : ∀ {Γ H n A}
    → Γ ⊢a H ⇛ lit n ⇛ A
    → ¬ Γ ⊢a Int ≈ H
    → ⊥
  inv-case-int ⊢a-lit ¬Int≈H = ¬Int≈H ≈□
  inv-case-int (⊢a-sub ⊢a-lit A≈H H≢□ pv-e) ¬Int≈H = ¬Int≈H A≈H
  inv-case-int (⊢a-sub (⊢a-sub ⊢e A≈H₁ H≢□₁ pv-e₁) A≈H H≢□ pv-e) ¬Int≈H = ⊥-elim (H≢□₁ refl)

  inv-case-var : ∀ {Γ H x A A'}
    → Γ ⊢a H ⇛ ` x ⇛ A'
    → Γ ∋ x ⦂ A
    →  ¬ Γ ⊢a A ≈ H
    → ⊥
  inv-case-var (⊢a-var x∈Γ') x∈Γ ¬p rewrite x∈Γ-unique x∈Γ x∈Γ' = ¬p ≈□
  inv-case-var (⊢a-sub (⊢a-var x∈Γ') A≈H H≢□ pv-e) x∈Γ ¬p rewrite x∈Γ-unique x∈Γ x∈Γ' = ¬p A≈H
  inv-case-var (⊢a-sub (⊢a-sub ⊢e A≈H₁ H≢□₁ pv-e₁) A≈H H≢□ pv-e) x∈Γ ¬p = ⊥-elim (H≢□₁ refl)

  inv-case-var' : ∀ {Γ H x A}
    → Γ ⊢a H ⇛ ` x ⇛ A
    → ¬ (∃[ B ](Γ ∋ x ⦂ B))
    → ⊥
  inv-case-var' {A = A} (⊢a-var x∈Γ) ¬p = ¬p ⟨ A , x∈Γ ⟩
  inv-case-var' {A = A} (⊢a-sub (⊢a-var x∈Γ) A≈H H≢□ pv-e) ¬p = ¬p ⟨ A , x∈Γ ⟩
  inv-case-var' (⊢a-sub (⊢a-sub ⊢e A≈H₁ H≢□₁ pv-e₁) A≈H H≢□ pv-e) ¬p = ⊥-elim (H≢□₁ refl)

  inv-case-lam : ∀ {Γ e}
    → ∃[ C ](Γ ⊢a τ Int ⇛ ƛ e ⇛ C)
    → ⊥
  inv-case-lam ⟨ .Int , ⊢a-sub (⊢a-sub ⊢e A≈H H≢□₁ pv-e₁) ≈τ H≢□ pv-e ⟩ = ⊥-elim (H≢□₁ refl)

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

  -- deal with size

  -- m + (1 + n + o)
  -- 1 + n + o + m
  -- 
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


≈a-dec k Γ □ A sz = yes ≈□
≈a-dec k Γ (τ B) A sz with τ-dec A B
... | yes p rewrite p = yes ≈τ
... | no ¬p = no λ where
  ≈τ → ¬p refl
≈a-dec (suc k) Γ (⟦ e ⟧⇒ H) Int sz = no (λ ())
≈a-dec (suc k) Γ (⟦ e ⟧⇒ H) (A ⇒ B) (s≤s sz) with ≈a-dec k Γ H B (m+n<o⇒n<o (size-H H) sz)
                                                | ⊢a-dec k Γ (τ A) e (n<o⇒n+0<o (m+n<o⇒m<o (size-e e) sz))
... | yes p | yes ⟨ C , ⊢e ⟩ = yes (≈hole ⊢e p)
... | yes p | no ¬p = no λ where
  (≈hole {C = C} ⊢e B≈H) → ¬p ⟨ C , ⊢e ⟩
... | no ¬p | _ = no λ where
  (≈hole ⊢e B≈H) → ¬p B≈H

-- lit
⊢a-dec (suc k) Γ H (lit n) (s≤s sz) with ≈a-dec k Γ H Int sz
... | yes p = yes ⟨ Int , (subsumption-0 ⊢a-lit p) ⟩
... | no ¬p = no λ where
  ⟨ A , ⊢e ⟩ → inv-case-int ⊢e ¬p
-- var  
⊢a-dec (suc k) Γ H (` x) (s≤s sz) with x∈Γ-dec Γ x
⊢a-dec (suc k) Γ H (` x) (s≤s sz) | yes ⟨ A , x∈Γ ⟩ with ≈a-dec k Γ H A sz
... | yes p = yes ⟨ A , (subsumption-0 (⊢a-var x∈Γ) p) ⟩
... | no ¬p = no λ where
  ⟨ A' , ⊢e ⟩ → inv-case-var ⊢e x∈Γ ¬p
⊢a-dec (suc k) Γ H (` x) (s≤s sz) | no ¬p = no λ where
  ⟨ A , ⊢e ⟩ → inv-case-var' ⊢e ¬p
-- lam  
⊢a-dec (suc k) Γ □ (ƛ e) (s≤s sz) = no λ where
  ⟨ _ , ⊢a-sub snd A≈H H≢□ pv-e ⟩ → ⊥-elim (H≢□ refl)
⊢a-dec (suc k) Γ (τ Int) (ƛ e) (s≤s sz) = no inv-case-lam
-- lam1
⊢a-dec (suc k) Γ (τ (A ⇒ B)) (ƛ e) (s≤s sz) with ⊢a-dec k (Γ , A) (τ B) e sz
... | yes ⟨ C , ⊢e ⟩ = yes ⟨ A ⇒ C , ⊢a-lam₁ ⊢e ⟩
... | no ¬p = no λ where
  ⟨ A ⇒ C , ⊢a-lam₁ ⊢e' ⟩ → ¬p ⟨ C , ⊢e' ⟩
-- lam2
⊢a-dec (suc k) Γ (⟦ e' ⟧⇒ H) (ƛ e) (s≤s sz) with ⊢a-dec k Γ □ e' (sz-case-1 sz)
⊢a-dec (suc k) Γ (⟦ e' ⟧⇒ H) (ƛ e) (s≤s sz) | yes ⟨ A , ⊢e' ⟩ with ⊢a-dec k (Γ , A) (H ⇧ 0) e (sz-case-3 {e = e} {H = H} {e' = e'} sz)
... | yes ⟨ B , ⊢e'' ⟩ = yes ⟨ (A ⇒ B) , (⊢a-lam₂ ⊢e' ⊢e'') ⟩
... | no ¬p = no (inv-case-lam' ⊢e' ¬p)
⊢a-dec (suc k) Γ (⟦ e' ⟧⇒ H) (ƛ e) (s≤s sz) | no ¬p = no λ ih → inv-case-lam'' ¬p ih
-- app
⊢a-dec (suc k) Γ H (e₁ · e₂) (s≤s sz) with ⊢a-dec k Γ (⟦ e₂ ⟧⇒ H) e₁ (sz-case-2 sz)
... | yes ⟨ Int , ⊢e ⟩ = ⊥-elim (inv-hole-int ⊢e)
... | yes ⟨ A ⇒ B , ⊢e ⟩ = yes ⟨ B , (⊢a-app ⊢e) ⟩
... | no ¬p = no λ where
  ⟨ A' , ⊢a-app {A = A''} ⊢e' ⟩ → ¬p ⟨ A'' ⇒ A' , ⊢e' ⟩
-- ann  
⊢a-dec (suc k) Γ H (e ⦂ A) (s≤s sz) with ⊢a-dec k Γ (τ A) e (n<o⇒n+0<o (m+n<o⇒m<o (size-e e) sz))
                                       | ≈a-dec k Γ H A (m+n<o⇒n<o (size-H H) sz)
... | yes ⟨ A' , ⊢e' ⟩ | yes p' = yes ⟨ A , subsumption-0 (⊢a-ann ⊢e') p' ⟩
... | yes p | no ¬p  = no λ where
  ⟨ A' , ⊢a-ann ⊢e' ⟩ → ¬p ≈□
  ⟨ A' , ⊢a-sub (⊢a-ann ⊢e') A≈H H≢□ pv-e ⟩ → ¬p A≈H
  ⟨ A' , ⊢a-sub (⊢a-sub ⊢e' A≈H₁ H≢□₁ pv-e₁) A≈H H≢□ pv-e ⟩ → ⊥-elim (H≢□₁ refl)
... | no ¬p | _      = no λ where
  ⟨ A' , ⊢a-ann {B = B} ⊢e' ⟩ → ¬p ⟨ B , ⊢e' ⟩
  ⟨ A' , ⊢a-sub (⊢a-ann {B = B} ⊢e') A≈H H≢□ pv-e ⟩ → ¬p ⟨ B , ⊢e' ⟩
  ⟨ A' , ⊢a-sub (⊢a-sub ⊢e' A≈H₁ H≢□₁ pv-e₁) A≈H H≢□ pv-e ⟩ → ⊥-elim (H≢□₁ refl)

