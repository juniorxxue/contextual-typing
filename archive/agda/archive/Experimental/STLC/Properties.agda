module STLC.Properties where

open import STLC.Prelude hiding (_≤?_)
open import STLC.Common

length : Context → ℕ
length ∅        =  zero
length (Γ , _)  =  suc (length Γ)

----------------------------------------------------------------------
--+                                                                +--
--+                           Weakening                            +--
--+                                                                +--
----------------------------------------------------------------------

infix 6 _↑_[_]_

_↑_[_]_ : (Γ : Context) → (n : ℕ) → (n ≤ length Γ) → Type → Context
Γ ↑ zero [ n≤l ] T = Γ , T
∅ ↑ (suc n) [ () ] T
(Γ , A) ↑ (suc n) [ s≤s n≤l ] T = (Γ ↑ n [ n≤l ] T) , A

↑Γ-var₁ : ∀ {Γ n A B x n≤l}
  → Γ ∋ x ⦂ B
  → n ≤ x
  → Γ ↑ n [ n≤l ] A ∋ suc x ⦂ B
↑Γ-var₁ {n = zero} x∈Γ n≤x = S x∈Γ
↑Γ-var₁ {n = suc n} {n≤l = s≤s n≤l} (S x∈Γ) (s≤s n≤x) = S (↑Γ-var₁ x∈Γ n≤x)

↑Γ-var₂ : ∀ {Γ n A B x n≤l}
  → Γ ∋ x ⦂ B
  → ¬ n ≤ x
  → Γ ↑ n [ n≤l ] A ∋ x ⦂ B
↑Γ-var₂ {n = zero} {x = zero} x∈Γ n>x = ⊥-elim (n>x z≤n)
↑Γ-var₂ {n = zero} {x = suc x} x∈Γ n>x = ⊥-elim (n>x z≤n)
↑Γ-var₂ {n = suc n} {x = zero} {s≤s n≤l} Z n>x = Z
↑Γ-var₂ {Γ , C} {n = suc n} {x = suc x} {s≤s n≤l} (S x∈Γ) n>x = S (↑Γ-var₂ x∈Γ λ n≤x → n>x (s≤s n≤x))

∋-weaken : ∀ {Γ A n x B}
  → Γ ∋ x ⦂ B
  → (n≤l : n ≤ length Γ)
  → Γ ↑ n [ n≤l ] A ∋ ↑-var n x ⦂ B
∋-weaken {Γ = Γ} {n = n} {x = x} x∈Γ n≤l with n ≤? x
... | yes p = ↑Γ-var₁ x∈Γ p
... | no ¬p = ↑Γ-var₂ x∈Γ ¬p

----------------------------------------------------------------------
--+                                                                +--
--+                         Strengthening                          +--
--+                                                                +--
----------------------------------------------------------------------

infix 6 _↓_[_]

_↓_[_] : (Γ : Context) → (n : ℕ) → (n ≤ length Γ) → Context
∅ ↓ .zero [ z≤n ] = ∅
(Γ , A) ↓ zero [ n≤l ] = Γ
(Γ , A) ↓ suc n [ s≤s n≤l ] = Γ ↓ n [ n≤l ] , A

↓-var₁' : ∀ {Γ x A B n}
  → Γ , B ∋ x ⦂ A
  → suc n ≤ x
  → (n≤l : n ≤ suc (length Γ))
  → (Γ , B) ↓ n [ n≤l ] ∋ pred x ⦂ A
↓-var₁' {n = zero} (S x∈Γ) (s≤s n+1≤x) n≤l = x∈Γ
↓-var₁' {Γ , C} {n = suc n} (S (S x∈Γ)) (s≤s n+1≤x) (s≤s n≤l) = S (↓-var₁' (S x∈Γ) n+1≤x n≤l)

↓-var₁ : ∀ {Γ x A B n}
  → Γ , B ∋ x ⦂ A
  → (` x) ~↑~ n
  → n ≤ x
  → (n≤l : n ≤ suc (length Γ))
  → (Γ , B) ↓ n [ n≤l ] ∋ pred x ⦂ A
↓-var₁ {x = x} x∈Γ (sd-var n≢x) n≤x n≤l = ↓-var₁' x∈Γ (≤∧≢⇒< n≤x n≢x) n≤l

↓-var₂ : ∀ {Γ x A B n}
  → Γ , B ∋ x ⦂ A
  → x < n
  → (n≤l : n ≤ suc (length Γ))
  → (Γ , B) ↓ n [ n≤l ] ∋ x ⦂ A
↓-var₂ {x = .zero} {n = suc n} Z x<n (s≤s n≤l) = Z
↓-var₂ {Γ , C} {x = .(suc _)} {n = .(suc _)} (S x∈Γ) (s≤s x<n) (s≤s n≤l) = S (↓-var₂ x∈Γ x<n n≤l)

∋-strenghthen : ∀ {Γ n x A}
  → Γ ∋ x ⦂ A
  → (` x) ~↑~ n
  → (n≤l : n ≤ length Γ)
  → Γ ↓ n [ n≤l ] ∋ ↓-var n x ⦂ A
∋-strenghthen {Γ , B} {n} {x} {A} x∈Γ sd n≤l with n ≤? x
... | yes n≤x = ↓-var₁ x∈Γ sd n≤x n≤l
... | no  n≰x = ↓-var₂ x∈Γ (m≰n⇒n<m n≰x) n≤l
