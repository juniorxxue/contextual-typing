module Algo.Properties where

open import Prelude hiding (length; _≤?_) renaming (_≤_ to _≤n_)
open import Common
open import Algo

----------------------------------------------------------------------
--                                                                  --
--                            Subtyping                             --
--                                                                  --
----------------------------------------------------------------------

≤a-refl-τ : ∀ {A Γ}
  → Γ ⊢a A ≤ τ A
≤a-refl-τ {A = Int} = ≤a-int
≤a-refl-τ {A = Top} = ≤a-top
≤a-refl-τ {A = _ ⇒ _} = ≤a-arr ≤a-refl-τ ≤a-refl-τ

-- inversion lemmas

≤a-hint-inv₁ : ∀ {Γ H A B e}
  → Γ ⊢a A ⇒ B ≤ ⟦ e ⟧⇒ H
  → ∃[ C ] Γ ⊢a τ A ⇛ e ⇛ C
≤a-hint-inv₁ (≤a-hint {C = C} x ≤a) = ⟨ C , x ⟩

≤a-hint-inv₂ : ∀ {Γ H A B e}
  → Γ ⊢a A ⇒ B ≤ ⟦ e ⟧⇒ H
  → Γ ⊢a B ≤ H
≤a-hint-inv₂ (≤a-hint x ≤) = ≤

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

length : Context → ℕ
length ∅        =  zero
length (Γ , _)  =  suc (length Γ)

infix 6 _↑_[_]_

_↑_[_]_ : (Γ : Context) → (n : ℕ) → (n ≤n length Γ) → Type → Context
Γ ↑ zero [ n≤l ] T = Γ , T
∅ ↑ (suc n) [ () ] T
(Γ , A) ↑ (suc n) [ s≤s n≤l ] T = (Γ ↑ n [ n≤l ] T) , A

↑Γ-var₁ : ∀ {Γ n A B x n≤l}
  → Γ ∋ x ⦂ B
  → n ≤n x
  → Γ ↑ n [ n≤l ] A ∋ suc x ⦂ B
↑Γ-var₁ {n = zero} x∈Γ n≤x = S x∈Γ
↑Γ-var₁ {n = suc n} {n≤l = s≤s n≤l} (S x∈Γ) (s≤s n≤x) = S (↑Γ-var₁ x∈Γ n≤x)

↑Γ-var₂ : ∀ {Γ n A B x n≤l}
  → Γ ∋ x ⦂ B
  → ¬ n ≤n x
  → Γ ↑ n [ n≤l ] A ∋ x ⦂ B
↑Γ-var₂ {n = zero} {x = zero} x∈Γ n>x = ⊥-elim (n>x z≤n)
↑Γ-var₂ {n = zero} {x = suc x} x∈Γ n>x = ⊥-elim (n>x z≤n)
↑Γ-var₂ {n = suc n} {x = zero} {s≤s n≤l} Z n>x = Z
↑Γ-var₂ {Γ , C} {n = suc n} {x = suc x} {s≤s n≤l} (S x∈Γ) n>x = S (↑Γ-var₂ x∈Γ λ n≤x → n>x (s≤s n≤x))

∋-weaken : ∀ {Γ A n x B}
  → Γ ∋ x ⦂ B
  → (n≤l : n ≤n length Γ)
  → Γ ↑ n [ n≤l ] A ∋ ↑-var n x ⦂ B
∋-weaken {Γ = Γ} {n = n} {x = x} x∈Γ n≤l with n ≤? x
... | yes p = ↑Γ-var₁ x∈Γ p
... | no ¬p = ↑Γ-var₂ x∈Γ ¬p

≤a-weaken : ∀ {Γ A B H n n≤l}
  → Γ ⊢a B ≤ H
  → Γ ↑ n [ n≤l ] A ⊢a B ≤ (H ⇧ n)

⊢a-weaken : ∀ {Γ e H A B n n≤l}
  → Γ ⊢a H ⇛ e ⇛ B
  → Γ ↑ n [ n≤l ] A ⊢a H ⇧ n ⇛ e ↑ n ⇛ B

≤a-weaken ≤a-int = ≤a-int
≤a-weaken ≤a-top = ≤a-top
≤a-weaken (≤a-arr C≤A B≤D) = ≤a-arr (≤a-weaken C≤A) (≤a-weaken B≤D)
≤a-weaken (≤a-hint ⊢e B≤H) = ≤a-hint (⊢a-weaken ⊢e) (≤a-weaken B≤H)

⇧-⇧-comm-0 : ∀ H n
  → H ⇧ n ⇧ 0 ≡ H ⇧ 0 ⇧ (suc n)
⇧-⇧-comm-0 H n rewrite ⇧-⇧-comm H 0 n z≤n = refl

⊢a-weaken (⊢a-lit B≤H) = ⊢a-lit (≤a-weaken B≤H)
⊢a-weaken {n≤l = n≤l} (⊢a-var x∈Γ B≤H) = ⊢a-var (∋-weaken x∈Γ n≤l) (≤a-weaken B≤H)
⊢a-weaken (⊢a-app ⊢e) = ⊢a-app (⊢a-weaken ⊢e)
⊢a-weaken (⊢a-ann ⊢e B≤H) = ⊢a-ann (⊢a-weaken ⊢e) (≤a-weaken B≤H)
⊢a-weaken {n≤l = n≤l} (⊢a-lam₁ ⊢e) = ⊢a-lam₁ (⊢a-weaken {n≤l = s≤s n≤l} ⊢e)
⊢a-weaken {H = ⟦ _ ⟧⇒ H} {A = A} {n = n} {n≤l = n≤l} (⊢a-lam₂ ⊢e ⊢f) with ⊢a-weaken {A = A} {n = suc n} {n≤l = s≤s n≤l} ⊢f
... | ind-f rewrite sym (⇧-⇧-comm-0 H n) = ⊢a-lam₂ (⊢a-weaken ⊢e) ind-f

----------------------------------------------------------------------
--+                                                                +--
--+                         Strengthening                          +--
--+                                                                +--
----------------------------------------------------------------------

infix 6 _↓_[_]

_↓_[_] : (Γ : Context) → (n : ℕ) → (n ≤n length Γ) → Context
∅ ↓ .zero [ z≤n ] = ∅
(Γ , A) ↓ zero [ n≤l ] = Γ
(Γ , A) ↓ suc n [ s≤s n≤l ] = Γ ↓ n [ n≤l ] , A

↓-var₁' : ∀ {Γ x A B n}
  → Γ , B ∋ x ⦂ A
  → suc n ≤n x
  → (n≤l : n ≤n suc (length Γ))
  → (Γ , B) ↓ n [ n≤l ] ∋ pred x ⦂ A
↓-var₁' {n = zero} (S x∈Γ) (s≤s n+1≤x) n≤l = x∈Γ
↓-var₁' {Γ , C} {n = suc n} (S (S x∈Γ)) (s≤s n+1≤x) (s≤s n≤l) = S (↓-var₁' (S x∈Γ) n+1≤x n≤l)

↓-var₁ : ∀ {Γ x A B n}
  → Γ , B ∋ x ⦂ A
  → (` x) ~↑~ n
  → n ≤n x
  → (n≤l : n ≤n suc (length Γ))
  → (Γ , B) ↓ n [ n≤l ] ∋ pred x ⦂ A
↓-var₁ {x = x} x∈Γ (sd-var n≢x) n≤x n≤l = ↓-var₁' x∈Γ (≤∧≢⇒< n≤x n≢x) n≤l

↓-var₂ : ∀ {Γ x A B n}
  → Γ , B ∋ x ⦂ A
  → x < n
  → (n≤l : n ≤n suc (length Γ))
  → (Γ , B) ↓ n [ n≤l ] ∋ x ⦂ A
↓-var₂ {x = .zero} {n = suc n} Z x<n (s≤s n≤l) = Z
↓-var₂ {Γ , C} {x = .(suc _)} {n = .(suc _)} (S x∈Γ) (s≤s x<n) (s≤s n≤l) = S (↓-var₂ x∈Γ x<n n≤l)

∋-strenghthen : ∀ {Γ n x A}
  → Γ ∋ x ⦂ A
  → (` x) ~↑~ n
  → (n≤l : n ≤n length Γ)
  → Γ ↓ n [ n≤l ] ∋ ↓-var n x ⦂ A
∋-strenghthen {Γ , B} {n} {x} {A} x∈Γ sd n≤l with n ≤? x
... | yes n≤x = ↓-var₁ x∈Γ sd n≤x n≤l
... | no  n≰x = ↓-var₂ x∈Γ (m≰n⇒n<m n≰x) n≤l

≤a-strengthen : ∀ {Γ A H n}
  → Γ ⊢a A ≤ H
  → H ~⇧~ n
  → (n≤l : n ≤n length Γ)
  → Γ ↓ n [ n≤l ] ⊢a A ≤ (H ⇩ n)
  
⊢a-strengthen : ∀ {Γ A H n e}
  → Γ ⊢a H ⇛ e ⇛ A -- H, e is shifted
  → e ~↑~ n
  → H ~⇧~ n
  → (n≤l : n ≤n length Γ)
  → Γ ↓ n [ n≤l ] ⊢a (H ⇩ n) ⇛ e ↓ n ⇛ A

≤a-strengthen ≤a-int sdh n≤l = ≤a-int
≤a-strengthen ≤a-top sdh n≤l = ≤a-top
≤a-strengthen (≤a-arr A≤H A≤H₁) sdh n≤l = ≤a-arr (≤a-strengthen A≤H sdh-τ n≤l) (≤a-strengthen A≤H₁ sdh-τ n≤l)
≤a-strengthen (≤a-hint ⊢e A≤H) (sdh-h sd sdh) n≤l = ≤a-hint (⊢a-strengthen ⊢e sd sdh-τ n≤l) (≤a-strengthen A≤H sdh n≤l)

⊢a-strengthen (⊢a-lit B≤H) sd sdh n≤l = ⊢a-lit (≤a-strengthen B≤H sdh n≤l)
⊢a-strengthen (⊢a-var x∈Γ B≤H) sd sdh n≤l = ⊢a-var (∋-strenghthen x∈Γ sd n≤l) (≤a-strengthen B≤H sdh n≤l)
⊢a-strengthen (⊢a-app ⊢e) (sd-app sd₁ sd₂) sdh n≤l = ⊢a-app (⊢a-strengthen ⊢e sd₁ (sdh-h sd₂ sdh) n≤l)
⊢a-strengthen (⊢a-ann ⊢e B≤H) (sd-ann sd) sdh n≤l = ⊢a-ann (⊢a-strengthen ⊢e sd sdh-τ n≤l) (≤a-strengthen B≤H sdh n≤l)
⊢a-strengthen (⊢a-lam₁ ⊢e) (sd-lam sd) sdh n≤l = ⊢a-lam₁ (⊢a-strengthen ⊢e sd sdh-τ (s≤s n≤l))
⊢a-strengthen {H = ⟦ _ ⟧⇒ H} {n = n} (⊢a-lam₂ ⊢e ⊢f) (sd-lam sd₁) (sdh-h sd₂ sdh) n≤l with ⊢a-strengthen ⊢f sd₁ (⇧-shiftedh-n z≤n sdh) (s≤s n≤l)
... | ind-f rewrite sym (⇩-⇧-comm H 0 n z≤n sdh) = ⊢a-lam₂ (⊢a-strengthen ⊢e sd₂ sdh-τ n≤l) ind-f

≤a-strengthen-0 : ∀ {Γ A B H}
  → Γ , A ⊢a B ≤ H ⇧ 0
  → Γ ⊢a B ≤ H
≤a-strengthen-0 {H = H} B≤H with ≤a-strengthen {n = 0} B≤H ⇧-shiftedh z≤n
... | ind-h rewrite ⇧-⇩-id H 0 = ind-h  

⊢a-strengthen-0 : ∀ {Γ H e A B}
  → Γ , A ⊢a H ⇧ 0 ⇛ e ↑ 0 ⇛ B
  → Γ ⊢a H ⇛ e ⇛ B
⊢a-strengthen-0 {H = H} {e = e} ⊢e with ⊢a-strengthen {n = 0} ⊢e ↑-shifted ⇧-shiftedh z≤n
... | ind-e rewrite ↑-↓-id e 0 | ⇧-⇩-id H 0  = ind-e
