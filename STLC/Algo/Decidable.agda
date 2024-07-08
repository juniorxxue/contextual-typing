module STLC.Algo.Decidable where

open import STLC.Prelude hiding (_≤?_) renaming (_≤_ to _≤n_)
open import STLC.Common
open import STLC.Properties
open import STLC.Algo
open import STLC.Algo.Properties

n<o↝n+0<o : ∀ {n o}
  → n < o
  → n + 0 < o
n<o↝n+0<o {n} {o} n<o rewrite +-comm n 0 = n<o

m+n<o↝m<o : ∀ m {n o}
  → m + n < o
  → m < o
m+n<o↝m<o m m+n<o = m+n≤o⇒m≤o (suc m) m+n<o

m+n<o↝n<o : ∀ n {m o}
  → m + n < o
  → n < o
m+n<o↝n<o n {m} m+n<o rewrite +-comm m n = m+n<o↝m<o n m+n<o

size-e : Term → ℕ
size-e (lit x) = 1
size-e (` x) = 1
size-e (ƛ e) = 1 + size-e e
size-e (e₁ · e₂) = 2 + size-e e₁ + size-e e₂
size-e (e ⦂ _) = 1 + size-e e

size-Σ : Context → ℕ
size-Σ □ = 0
size-Σ (τ _) = 0
size-Σ ([ e ]↝ Σ) = 1 + size-e e + size-Σ Σ

size-↑ : ∀ e {n}
  → size-e e ≡ size-e (e ↑ n)
size-↑ (lit x) {n} = refl
size-↑ (` x) {n} = refl
size-↑ (ƛ e) {n} rewrite size-↑ e {suc n} = refl
size-↑ (e · e₁) {n} rewrite size-↑ e {n} | size-↑ e₁ {n} = refl
size-↑ (e ⦂ _) {n} rewrite size-↑ e {n} = refl

size-⇧ : ∀ Σ {n}
  → size-Σ Σ ≡ size-Σ (Σ ⇧ n)
size-⇧ □ = refl
size-⇧ (τ _) = refl
size-⇧ ([ e ]↝ Σ) {n} rewrite size-⇧ Σ {n} | size-↑ e {n} = refl

x∈Γ-unique : ∀ {Γ x A B}
  → Γ ∋ x ⦂ A
  → Γ ∋ x ⦂ B
  → A ≡ B
x∈Γ-unique {x = zero} Z Z = refl
x∈Γ-unique {x = suc x} (S A∈Γ) (S B∈Γ) rewrite x∈Γ-unique A∈Γ B∈Γ = refl

⊢unique : ∀ {Γ Σ e A B}
  → Γ ⊢ Σ ⇒ e ⇒ A
  → Γ ⊢ Σ ⇒ e ⇒ B
  → A ≡ B
⊢unique ⊢lit ⊢lit = refl
⊢unique (⊢var x∈Γ) (⊢var x∈Γ₁) = x∈Γ-unique x∈Γ x∈Γ₁
⊢unique (⊢ann ⊢1) (⊢ann ⊢2) = refl
⊢unique (⊢ann ⊢1) (⊢sub ⊢2 A≈Σ Σ≢□ pv-e) = ⊢unique (⊢ann ⊢1) ⊢2
⊢unique (⊢app ⊢1) (⊢app ⊢2) with ⊢unique ⊢1 ⊢2
... | refl = refl
⊢unique (⊢lam₁ ⊢1) (⊢lam₁ ⊢2) rewrite ⊢unique ⊢1 ⊢2 = refl
⊢unique (⊢lam₂ ⊢1 ⊢3) (⊢lam₂ ⊢2 ⊢4) rewrite ⊢unique ⊢1 ⊢2 | ⊢unique ⊢3 ⊢4 = refl
⊢unique (⊢sub ⊢lit A≈Σ Σ≢□ pv-e) ⊢lit = refl
⊢unique (⊢sub (⊢sub ⊢1 A≈Σ₁ Σ≢□₁ pv-e₁) A≈Σ Σ≢□ pv-e) ⊢lit = ⊢unique ⊢1 ⊢lit
⊢unique (⊢sub ⊢1 A≈Σ Σ≢□ pv-e) (⊢var x∈Γ) = ⊢unique ⊢1 (⊢var x∈Γ)
⊢unique (⊢sub ⊢1 A≈Σ Σ≢□ pv-e) (⊢ann ⊢2) = ⊢unique ⊢1 (⊢ann ⊢2)
⊢unique (⊢sub ⊢1 A≈Σ Σ≢□ pv-e) (⊢sub ⊢2 A≈Σ₁ Σ≢□₁ pv-e₁) = ⊢unique ⊢1 ⊢2

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
τ-dec Int (B `→ B₁) = no (λ ())
τ-dec (A `→ A₁) Int = no (λ ())
τ-dec (A `→ A₁) (B `→ B₁) with τ-dec A B | τ-dec A₁ B₁
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

≈dec : ∀ k Γ Σ A
  → size-Σ Σ < k
  → Dec (Γ ⊢ A ≈ Σ) 

⊢dec : ∀ k Γ Σ e
  → size-e e + size-Σ Σ < k
  → Dec (∃[ A ](Γ ⊢ Σ ⇒ e ⇒ A))

private
  inv-case : ∀ {Γ x A A' e Σ}
    → Γ ∋ x ⦂ A
    → Γ ∋ x ⦂ A'
    → Γ ⊢ A' ≈ [ e ]↝ Σ
    → ¬ Γ ⊢ A ≈ [ e ]↝ Σ
    → ⊥
  inv-case x∈Γ x∈Γ' A≈Σ ¬A≈Σ' rewrite x∈Γ-unique x∈Γ x∈Γ' = ¬A≈Σ' A≈Σ

  inv-term-int : ∀ {Γ e₁ e₂ Σ}
    → Γ ⊢ [ e₂ ]↝ Σ ⇒ e₁ ⇒ Int
    → ⊥
  inv-term-int ⊢e with ⊢to≈ ⊢e
  ... | ()

  inv-case-int : ∀ {Γ Σ n A}
    → Γ ⊢ Σ ⇒ lit n ⇒ A
    → ¬ Γ ⊢ Int ≈ Σ
    → ⊥
  inv-case-int ⊢lit ¬Int≈Σ = ¬Int≈Σ ≈□
  inv-case-int (⊢sub ⊢lit A≈Σ Σ≢□ pv-e) ¬Int≈Σ = ¬Int≈Σ A≈Σ

  inv-case-var : ∀ {Γ Σ x A A'}
    → Γ ⊢ Σ ⇒ ` x ⇒ A'
    → Γ ∋ x ⦂ A
    →  ¬ Γ ⊢ A ≈ Σ
    → ⊥
  inv-case-var (⊢var x∈Γ') x∈Γ ¬p rewrite x∈Γ-unique x∈Γ x∈Γ' = ¬p ≈□
  inv-case-var (⊢sub (⊢var x∈Γ') A≈Σ Σ≢□ pv-e) x∈Γ ¬p rewrite x∈Γ-unique x∈Γ x∈Γ' = ¬p A≈Σ

  inv-case-var' : ∀ {Γ Σ x A}
    → Γ ⊢ Σ ⇒ ` x ⇒ A
    → ¬ (∃[ B ](Γ ∋ x ⦂ B))
    → ⊥
  inv-case-var' {A = A} (⊢var x∈Γ) ¬p = ¬p ⟨ A , x∈Γ ⟩
  inv-case-var' {A = A} (⊢sub (⊢var x∈Γ) A≈Σ Σ≢□ pv-e) ¬p = ¬p ⟨ A , x∈Γ ⟩

  inv-case-lam : ∀ {Γ e}
    → ∃[ C ](Γ ⊢ τ Int ⇒ ƛ e ⇒ C)
    → ⊥
  inv-case-lam ⟨ fst , ⊢sub (⊢sub snd x₃ x₄ ()) x x₁ x₂ ⟩

  inv-case-lam' : ∀ {Γ e e' Σ A}
    → Γ ⊢ □ ⇒ e' ⇒ A
    → ¬ (∃[ C ](Γ , A ⊢ Σ ⇧ 0 ⇒ e ⇒ C))
    → ¬ (∃[ D ](Γ ⊢ ([ e' ]↝ Σ) ⇒ ƛ e ⇒ D))
  inv-case-lam' ⊢e ¬p ⟨ D `→ E , ⊢lam₂ ⊢e' ⊢e'' ⟩ rewrite ⊢unique ⊢e ⊢e' = ¬p ⟨ E , ⊢e'' ⟩

  inv-case-lam'' : ∀ {Γ e' e Σ}
    → ¬ (∃[ C ](Γ ⊢ □ ⇒ e' ⇒ C))
    → ∃[ D ](Γ ⊢ [ e' ]↝ Σ ⇒ ƛ e ⇒ D)
    → ⊥
  inv-case-lam'' ¬p ⟨ A `→ B , ⊢lam₂ ⊢e ⊢e₁ ⟩ = ¬p ⟨ A , ⊢e ⟩

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

  sz-case-3 : ∀ {e Σ e' k}
    → suc (size-e e + suc (size-e e' + size-Σ Σ)) ≤n k
    → size-e e + size-Σ (Σ ⇧ 0) < k
  sz-case-3 {Σ = Σ} sz rewrite sym (size-⇧ Σ {0}) = sz-case-3' sz

≈dec k Γ □ A sz = yes ≈□
≈dec k Γ (τ B) A sz with τ-dec A B
... | yes p rewrite p = yes ≈τ
... | no ¬p = no λ where
  ≈τ → ¬p refl
≈dec (suc k) Γ ([ e ]↝ Σ) Int sz = no (λ ())
≈dec (suc k) Γ ([ e ]↝ Σ) (A `→ B) (s≤s sz) with ≈dec k Γ Σ B (m+n<o↝n<o (size-Σ Σ) sz)
                                                | ⊢dec k Γ (τ A) e (n<o↝n+0<o (m+n<o↝m<o (size-e e) sz))
... | yes p | yes ⟨ C , ⊢e ⟩ = yes (≈term ⊢e p)
... | yes p | no ¬p = no λ where
  (≈term {C = C} ⊢e B≈Σ) → ¬p ⟨ C , ⊢e ⟩
... | no ¬p | _ = no λ where
  (≈term ⊢e B≈Σ) → ¬p B≈Σ

-- lit
⊢dec (suc k) Γ Σ (lit n) (s≤s sz) with ≈dec k Γ Σ Int sz
... | yes p = yes ⟨ Int , (subsumption-0 ⊢lit p) ⟩
... | no ¬p = no λ where
  ⟨ A , ⊢e ⟩ → inv-case-int ⊢e ¬p
-- var  
⊢dec (suc k) Γ Σ (` x) (s≤s sz) with x∈Γ-dec Γ x
⊢dec (suc k) Γ Σ (` x) (s≤s sz) | yes ⟨ A , x∈Γ ⟩ with ≈dec k Γ Σ A sz
... | yes p = yes ⟨ A , (subsumption-0 (⊢var x∈Γ) p) ⟩
... | no ¬p = no λ where
  ⟨ A' , ⊢e ⟩ → inv-case-var ⊢e x∈Γ ¬p
⊢dec (suc k) Γ Σ (` x) (s≤s sz) | no ¬p = no λ where
  ⟨ A , ⊢e ⟩ → inv-case-var' ⊢e ¬p
-- lam  
⊢dec (suc k) Γ □ (ƛ e) (s≤s sz) = no λ where
  ⟨ _ , ⊢sub snd A≈Σ Σ≢□ () ⟩
⊢dec (suc k) Γ (τ Int) (ƛ e) (s≤s sz) = no inv-case-lam
-- lam1
⊢dec (suc k) Γ (τ (A `→ B)) (ƛ e) (s≤s sz) with ⊢dec k (Γ , A) (τ B) e sz
... | yes ⟨ C , ⊢e ⟩ = yes ⟨ A `→ C , ⊢lam₁ ⊢e ⟩
... | no ¬p = no λ where
  ⟨ A `→ C , ⊢lam₁ ⊢e' ⟩ → ¬p ⟨ C , ⊢e' ⟩
-- lam2
⊢dec (suc k) Γ ([ e' ]↝ Σ) (ƛ e) (s≤s sz) with ⊢dec k Γ □ e' (sz-case-1 sz)
⊢dec (suc k) Γ ([ e' ]↝ Σ) (ƛ e) (s≤s sz) | yes ⟨ A , ⊢e' ⟩ with ⊢dec k (Γ , A) (Σ ⇧ 0) e (sz-case-3 {e = e} {Σ = Σ} {e' = e'} sz)
... | yes ⟨ B , ⊢e'' ⟩ = yes ⟨ (A `→ B) , (⊢lam₂ ⊢e' ⊢e'') ⟩
... | no ¬p = no (inv-case-lam' ⊢e' ¬p)
⊢dec (suc k) Γ ([ e' ]↝ Σ) (ƛ e) (s≤s sz) | no ¬p = no λ ih → inv-case-lam'' ¬p ih
-- app
⊢dec (suc k) Γ Σ (e₁ · e₂) (s≤s sz) with ⊢dec k Γ ([ e₂ ]↝ Σ) e₁ (sz-case-2 sz)
... | yes ⟨ Int , ⊢e ⟩ = ⊥-elim (inv-term-int ⊢e)
... | yes ⟨ A `→ B , ⊢e ⟩ = yes ⟨ B , (⊢app ⊢e) ⟩
... | no ¬p = no λ where
  ⟨ A' , ⊢app {A = A''} ⊢e' ⟩ → ¬p ⟨ A'' `→ A' , ⊢e' ⟩
-- ann  
⊢dec (suc k) Γ Σ (e ⦂ A) (s≤s sz) with ⊢dec k Γ (τ A) e (n<o↝n+0<o (m+n<o↝m<o (size-e e) sz))
                                       | ≈dec k Γ Σ A (m+n<o↝n<o (size-Σ Σ) sz)
... | yes ⟨ A' , ⊢e' ⟩ | yes p' = yes ⟨ A , subsumption-0 (⊢ann ⊢e') p' ⟩
... | yes p | no ¬p  = no λ where
  ⟨ A' , ⊢ann ⊢e' ⟩ → ¬p ≈□
  ⟨ A' , ⊢sub (⊢ann ⊢e') A≈Σ Σ≢□ pv-e ⟩ → ¬p A≈Σ
... | no ¬p | _      = no λ where
  ⟨ A' , ⊢ann {B = B} ⊢e' ⟩ → ¬p ⟨ B , ⊢e' ⟩
  ⟨ A' , ⊢sub (⊢ann {B = B} ⊢e') A≈Σ Σ≢□ pv-e ⟩ → ¬p ⟨ B , ⊢e' ⟩

⊢dec' : ∀ Γ Σ e
  → Dec (∃[ A ](Γ ⊢ Σ ⇒ e ⇒ A))
⊢dec' Γ Σ e = ⊢dec (1 + (size-e e + size-Σ Σ)) Γ Σ e (s≤s m≤m)

≈dec' : ∀ Γ Σ A
  → Dec (Γ ⊢ A ≈ Σ)
≈dec' Γ Σ A = ≈dec (suc (size-Σ Σ)) Γ Σ A (s≤s m≤m)
