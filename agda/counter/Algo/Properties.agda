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

data shifted : ℕ → Term → Set where

  sd-lit : ∀ {n i}
    → shifted n (lit i)

  sd-var₁ : ∀ {n x}
    → x < n
    → shifted n (` x)

  sd-var₂ : ∀ {n x}
    → (suc n) ≤n x
    → shifted n (` x)

  sd-lam : ∀ {n e}
    → shifted (suc n) e
    → shifted n (ƛ e)

  sd-app : ∀ {n e₁ e₂}
    → shifted n e₁
    → shifted n e₂
    → shifted n (e₁ · e₂)

  sd-ann : ∀ {n e A}
    → shifted n e
    → shifted n (e ⦂ A)

infix 6 _↓_[_]

_↓_[_] : (Γ : Context) → (n : ℕ) → (n ≤n length Γ) → Context
∅ ↓ .zero [ z≤n ] = ∅
(Γ , A) ↓ zero [ n≤l ] = Γ
(Γ , A) ↓ suc n [ s≤s n≤l ] = Γ ↓ n [ n≤l ] , A

↓-var₁ : ∀ {Γ x A B n}
  → Γ , B ∋ x ⦂ A
  → n ≤n x
  → (n≤l : n ≤n suc (length Γ))
  → (Γ , B) ↓ n [ n≤l ] ∋ pred x ⦂ A
↓-var₁ {Γ} {n = zero} Z n≤x n≤l = {!!}
↓-var₁ {Γ} {n = zero} (S x∈Γ) n≤x n≤l = x∈Γ
↓-var₁ {Γ} {n = suc n} (S x∈Γ) (s≤s n≤x) (s≤s n≤l) = {!!}

↓-var₂ : ∀ {Γ x A B n}
  → Γ , B ∋ x ⦂ A
  → x < n
  → (n≤l : n ≤n suc (length Γ))
  → (Γ , B) ↓ n [ n≤l ] ∋ x ⦂ A
↓-var₂ {x = .zero} {n = suc n} Z x<n (s≤s n≤l) = Z
↓-var₂ {Γ , C} {x = .(suc _)} {n = .(suc _)} (S x∈Γ) (s≤s x<n) (s≤s n≤l) = S (↓-var₂ x∈Γ x<n n≤l)

∋-strenghthen : ∀ {Γ n x A}
  → Γ ∋ x ⦂ A
  → (n≤l : n ≤n length Γ)
  → Γ ↓ n [ n≤l ] ∋ ↓-var n x ⦂ A
∋-strenghthen {Γ , B} {n} {x} {A} x∈Γ n≤l with n ≤? x
... | yes n≤x = ↓-var₁ x∈Γ n≤x n≤l
... | no  n≰x = ↓-var₂ x∈Γ (m≰n⇒n<m n≰x) n≤l

≤a-strengthen : ∀ {Γ A H n n≤l}
  → Γ ⊢a A ≤ H
  → Γ ↓ n [ n≤l ] ⊢a A ≤ (H ⇩ n)
  
⊢a-strengthen : ∀ {Γ A H n n≤l e}
  → Γ ⊢a H ⇛ e ⇛ A -- e is shifted
  → Γ ↓ n [ n≤l ] ⊢a (H ⇩ n) ⇛ e ↓ n ⇛ A

≤a-strengthen A≤H = {!!}
⊢a-strengthen (⊢a-lit x) = {!!}
⊢a-strengthen {n≤l = n≤l} (⊢a-var x∈Γ A≤H) = ⊢a-var (∋-strenghthen x∈Γ n≤l) (≤a-strengthen A≤H)
⊢a-strengthen (⊢a-app ⊢e) = {!!}
⊢a-strengthen (⊢a-ann ⊢e x) = {!!}
⊢a-strengthen (⊢a-lam₁ ⊢e) = {!!}
⊢a-strengthen (⊢a-lam₂ ⊢e ⊢e₁) = {!!}

⊢a-strengthen-0 : ∀ {Γ H e A B}
  → Γ , A ⊢a H ⇧ 0 ⇛ e ↑ 0 ⇛ B
  → Γ ⊢a H ⇛ e ⇛ B
⊢a-strengthen-0 {H = H} {e = e} ⊢e with ⊢a-strengthen {n = 0} {n≤l = z≤n} ⊢e
... | ind-e rewrite ↑-↓-id e 0 | ⇧-⇩-id H 0  = ind-e

↑-shifted : ∀ {e n}
  → shifted n (e ↑ n)
↑-shifted {lit i} {n} = sd-lit
↑-shifted {` x} {n} with n ≤? x
... | yes n≤x = sd-var₂ (s≤s n≤x)
... | no  n≰x = sd-var₁ (m≰n⇒n<m n≰x)
↑-shifted {ƛ e} {n} = sd-lam ↑-shifted
↑-shifted {e₁ · e₂} {n} = sd-app ↑-shifted ↑-shifted
↑-shifted {e ⦂ A} {n} = sd-ann ↑-shifted
