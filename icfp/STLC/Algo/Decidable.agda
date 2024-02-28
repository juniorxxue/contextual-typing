module STLC.Algo.Decidable where

open import STLC.Prelude hiding (_≤?_) renaming (_≤_ to _≤n_)
open import STLC.Common
open import STLC.Properties
open import STLC.Algo
open import STLC.Algo.Properties

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
⊢a-unique (⊢a-var x∈Γ) (⊢a-var x∈Γ₁) = x∈Γ-unique x∈Γ x∈Γ₁
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


----------------------------------------------------------------------
--+                                                                +--
--+                   Main Theorem of Decidable                    +--
--+                                                                +--
----------------------------------------------------------------------

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

  inv-case-var : ∀ {Γ H x A A'}
    → Γ ⊢a H ⇛ ` x ⇛ A'
    → Γ ∋ x ⦂ A
    →  ¬ Γ ⊢a A ≈ H
    → ⊥
  inv-case-var (⊢a-var x∈Γ') x∈Γ ¬p rewrite x∈Γ-unique x∈Γ x∈Γ' = ¬p ≈□
  inv-case-var (⊢a-sub (⊢a-var x∈Γ') A≈H H≢□ pv-e) x∈Γ ¬p rewrite x∈Γ-unique x∈Γ x∈Γ' = ¬p A≈H

  inv-case-var' : ∀ {Γ H x A}
    → Γ ⊢a H ⇛ ` x ⇛ A
    → ¬ (∃[ B ](Γ ∋ x ⦂ B))
    → ⊥
  inv-case-var' {A = A} (⊢a-var x∈Γ) ¬p = ¬p ⟨ A , x∈Γ ⟩
  inv-case-var' {A = A} (⊢a-sub (⊢a-var x∈Γ) A≈H H≢□ pv-e) ¬p = ¬p ⟨ A , x∈Γ ⟩

  inv-case-lam : ∀ {Γ e}
    → ∃[ C ](Γ ⊢a τ Int ⇛ ƛ e ⇛ C)
    → ⊥
  inv-case-lam ⟨ fst , ⊢a-sub (⊢a-sub snd x₃ x₄ ()) x x₁ x₂ ⟩

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
  ⟨ _ , ⊢a-sub snd A≈H H≢□ () ⟩
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
... | no ¬p | _      = no λ where
  ⟨ A' , ⊢a-ann {B = B} ⊢e' ⟩ → ¬p ⟨ B , ⊢e' ⟩
  ⟨ A' , ⊢a-sub (⊢a-ann {B = B} ⊢e') A≈H H≢□ pv-e ⟩ → ¬p ⟨ B , ⊢e' ⟩

⊢a-dec' : ∀ Γ H e
  → Dec (∃[ A ](Γ ⊢a H ⇛ e ⇛ A))
⊢a-dec' Γ H e = ⊢a-dec (suc (size-e e + size-H H)) Γ H e (s≤s m≤m)  
