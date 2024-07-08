module Record.Common where

open import Record.Prelude hiding (_≤?_)

  
Id : Set
Id = String

infixr 5  ƛ_
infixl 7  _·_
infix  9  `_
infix  5  _⦂_
infixr 8 _⇒_
-- infixr 8 _&_
infix  2 𝕣_
infixr 5 r⟦_↦_⟧_

infix 9 *_ 
Label = ℕ

data Type : Set where
  Int : Type
  Float : Type
  *_ : ℕ → Type
  Top : Type
  _⇒_ : Type → Type → Type
  _&_ : Type → Type → Type
  τ⟦_↦_⟧ : Label → Type → Type

data Constant : Set where
  lit      : ℕ → Constant
  flt      : 𝔽 → Constant
  +s       : Constant
  +i       : ℕ → Constant
  +f       : 𝔽 → Constant

data Term : Set
data Record : Set

data Term where
  𝕔_       : Constant → Term
  `_       : ℕ → Term
  ƛ_       : Term → Term
  _·_      : Term → Term → Term
  _⦂_      : Term → Type → Term
  𝕣_       : Record → Term
  _𝕡_      : Term → Label → Term

data Record where
  rnil : Record
  r⟦_↦_⟧_ : Label → Term → Record → Record

c-τ : Constant → Type
c-τ (lit n) = Int
c-τ (flt n) = Float
c-τ +s = (Int ⇒ Int ⇒ Int) & (Float ⇒ Float ⇒ Float)
c-τ (+i n) = Int ⇒ Int
c-τ (+f n) = Float ⇒ Float

infixl 5  _,_

data Context : Set where
  ∅     : Context
  _,_   : Context → Type → Context

infix  4  _∋_⦂_

data _∋_⦂_ : Context → ℕ → Type → Set where

  Z : ∀ {Γ A}
      ------------------
    → Γ , A ∋ zero ⦂ A

  S : ∀ {Γ A B n}
    → Γ ∋ n ⦂ A
      ------------------
    → Γ , B ∋ (suc n) ⦂ A

----------------------------------------------------------------------
--+                                                                +--
--+                             Shift                              +--
--+                                                                +--
----------------------------------------------------------------------
abstract
  _≤?_ : (x y : ℕ) → Dec (x ≤ y)
  _≤?_ = Record.Prelude._≤?_

↑-var : ℕ → ℕ → ℕ
↑-var n x with n ≤? x
... | yes n≤x = suc x
... | no  n>x = x

infixl 7 _↑_
infixl 7 _↑r_
_↑_ : Term → ℕ → Term
_↑r_ : Record → ℕ → Record

(𝕔 c) ↑ n = 𝕔 c
` x ↑ n = ` (↑-var n x)
(ƛ e) ↑ n = ƛ (e ↑ (suc n))
e₁ · e₂ ↑ n = (e₁ ↑ n) · (e₂ ↑ n)
(e ⦂ A) ↑ n = (e ↑ n) ⦂ A
(𝕣 rs) ↑ n = 𝕣 (rs ↑r n)
(e 𝕡 l) ↑ n = (e ↑ n) 𝕡 l

rnil ↑r n = rnil
(r⟦ l ↦ e ⟧ rs) ↑r n = r⟦ l ↦ (e ↑ n) ⟧ (rs ↑r n)

↓-var : ℕ → ℕ → ℕ
↓-var n x with n ≤? x
... | yes n≤x = pred x
... | no n>x   = x

infixl 7 _↓_
infixl 7 _↓r_

_↓_ : Term → ℕ → Term
_↓r_ : Record → ℕ → Record

𝕔 c ↓ n = 𝕔 c
` x ↓ n = ` (↓-var n x)
(ƛ e) ↓ n = ƛ (e ↓ (suc n))
e₁ · e₂ ↓ n = (e₁ ↓ n) · (e₂ ↓ n)
(e ⦂ A) ↓ n = (e ↓ n) ⦂ A
(𝕣 rs) ↓ n = 𝕣 (rs ↓r n)
(e 𝕡 l) ↓ n = (e ↓ n) 𝕡 l

rnil ↓r n = rnil
(r⟦ l ↦ e ⟧ rs) ↓r n = r⟦ l ↦ (e ↓ n) ⟧ (rs ↓r n)



↑-↓-var : ∀ x n → ↓-var n (↑-var n x) ≡ x
↑-↓-var x n with n ≤? x
...         | yes n≤x with n ≤? suc x
...                   | yes n≤x+1 = refl
...                   | no  n≰x+1 = ⊥-elim (n≰x+1 (m≤n⇒m≤1+n n≤x))
↑-↓-var x n | no  n≰x with n ≤? x
...                   | yes n≤x = ⊥-elim (n≰x n≤x)
...                   | no  n≰x = refl


↑-↓-id : ∀ e n
  → e ↑ n ↓ n ≡ e

↑r-↓r-id : ∀ rs n
  → rs ↑r n ↓r n ≡ rs

↑-↓-id (𝕔 _) n = refl
↑-↓-id (` x) n = cong `_ (↑-↓-var x n)
↑-↓-id (ƛ e) n rewrite ↑-↓-id e (suc n) = refl
↑-↓-id (e₁ · e₂) n rewrite ↑-↓-id e₁ n | ↑-↓-id e₂ n = refl
↑-↓-id (e ⦂ A) n rewrite ↑-↓-id e n = refl
↑-↓-id (𝕣 rs) n rewrite ↑r-↓r-id rs n = refl
↑-↓-id (e 𝕡 l) n rewrite ↑-↓-id e n = refl

↑r-↓r-id rnil n = refl
↑r-↓r-id (r⟦ l ↦ e ⟧ rs) n rewrite ↑-↓-id e n | ↑r-↓r-id rs n = refl


↑-↑-comm-var : ∀ m n x
  → m ≤ n
  → ↑-var (suc n) (↑-var m x) ≡ ↑-var m (↑-var n x)
↑-↑-comm-var m n x m≤n with m ≤? x | n ≤? x
...               | yes m≤x | yes n≤x with suc n ≤? suc x | m ≤? suc x
...                                   | yes n+1≤x+1 | yes m≤x+1 = refl
...                                   | yes n+1≤x+1 | no  m≰x+1 = ⊥-elim (m≰x+1 (m≤n⇒m≤1+n m≤x))
...                                   | no  n+1≰x+1 | yes m≤x+1 = ⊥-elim (n+1≰x+1 (s≤s n≤x))
...                                   | no  n+1≰x+1 | no  m≰x+1 = refl
↑-↑-comm-var m n x m≤n | yes m≤x | no n≰x  with suc n ≤? suc x | m ≤? x
...                                   | yes n+1≤x+1 | yes m≤x = ⊥-elim (n≰x (≤-pred n+1≤x+1))
...                                   | yes n+1≤x+1 | no  m≰x = ⊥-elim (m≰x m≤x)
...                                   | no  n+1≰x+1 | yes m≤x = refl
...                                   | no  n+1≰x+1 | no  m≰x = ⊥-elim (m≰x m≤x)
↑-↑-comm-var m n x m≤n | no  m≰x | yes n≤x with suc n ≤? x | m ≤? suc x
...                                   | yes n+1≤x | yes m≤x+1 = ⊥-elim (m≰x (≤-trans m≤n n≤x))
...                                   | yes n+1≤x | no  m≰x+1 = refl
...                                   | no  n+1≰x | yes m≤x+1 = ⊥-elim (m≰x (≤-trans m≤n n≤x))
...                                   | no  n+1≰x | no  m≰x+1 = ⊥-elim (m≰x (≤-trans m≤n n≤x))
↑-↑-comm-var m n x m≤n | no  m≰x | no n≰x  with suc n ≤? x | m ≤? x
...                                   | yes n+1≤x | yes m≤x = refl
...                                   | yes n+1≤x | no  m≰x = ⊥-elim (n≰x (m+1≤n→m≤n n+1≤x))
...                                   | no  n+1≰x | yes m≤x = ⊥-elim (m≰x m≤x)
...                                   | no  n+1≰x | no  m≰x = refl


↑-↑-comm : ∀ e m n → m ≤ n → e ↑ m ↑ suc n ≡ e ↑ n ↑ m
↑r-↑r-comm : ∀ rs m n → m ≤ n → rs ↑r m ↑r suc n ≡ rs ↑r n ↑r m

↑-↑-comm (𝕔 _) m n m≤n = refl
↑-↑-comm (` x) m n m≤n = cong `_ (↑-↑-comm-var m n x m≤n)
↑-↑-comm (ƛ e) m n m≤n rewrite ↑-↑-comm e (suc m) (suc n) (s≤s m≤n) = refl
↑-↑-comm (e₁ · e₂) m n m≤n rewrite ↑-↑-comm e₁ m n m≤n | ↑-↑-comm e₂ m n m≤n = refl
↑-↑-comm (e ⦂ A) m n m≤n rewrite ↑-↑-comm e m n m≤n = refl
↑-↑-comm (𝕣 rs) m n m≤n rewrite ↑r-↑r-comm rs m n m≤n = refl
↑-↑-comm (e 𝕡 l) m n m≤n rewrite ↑-↑-comm e m n m≤n = refl
↑r-↑r-comm rnil m n m≤n = refl
↑r-↑r-comm (r⟦ l ↦ e ⟧ rs) m n m≤n rewrite ↑-↑-comm e m n m≤n | ↑r-↑r-comm rs m n m≤n = refl

infix 4 _~↑~_
infix 4 _~↑r~_

data _~↑~_ : Term → ℕ → Set
data _~↑r~_ : Record → ℕ → Set

data _~↑~_ where

  sd-c : ∀ {n c}
    → (𝕔 c) ~↑~ n

  sd-var : ∀ {n x}
    → n ≢ x
    → (` x) ~↑~ n

  sd-lam : ∀ {n e}
    → e ~↑~ (suc n)
    → (ƛ e) ~↑~ n

  sd-app : ∀ {n e₁ e₂}
    → e₁ ~↑~ n
    → e₂ ~↑~ n
    → (e₁ · e₂) ~↑~ n

  sd-ann : ∀ {n e A}
    → e ~↑~ n
    → (e ⦂ A) ~↑~ n

  sd-rcd : ∀ {n rs}
    → rs ~↑r~ n
    → (𝕣 rs) ~↑~ n

  sd-prj : ∀ {e l n}
    → e ~↑~ n
    → (e 𝕡 l) ~↑~ n

data _~↑r~_ where

  sdr-nil : ∀ {n}
    → rnil ~↑r~ n

  sdr-cons : ∀ {e n rs l}
    → e ~↑~ n
    → rs ~↑r~ n
    → r⟦ l ↦ e ⟧ rs ~↑r~ n


↑-shifted : ∀ {e n}
  → (e ↑ n) ~↑~ n
↑r-shifted : ∀ {rs n}
  → (rs ↑r n) ~↑r~ n

↑-shifted {𝕔 c} {n} = sd-c
↑-shifted {` x} {n} with n ≤? x
... | yes p = sd-var (<⇒≢ (s≤s p))
... | no ¬p = sd-var (>⇒≢ (≰⇒> ¬p))
↑-shifted {ƛ e} {n} = sd-lam (↑-shifted {e})
↑-shifted {e₁ · e₂} {n} = sd-app (↑-shifted {e₁}) (↑-shifted {e₂})
↑-shifted {e ⦂ A} {n} = sd-ann (↑-shifted {e})
↑-shifted {𝕣 rs} {n} = sd-rcd ↑r-shifted
↑-shifted {e 𝕡 l} {n} = sd-prj ↑-shifted

↑r-shifted {rnil} {n} = sdr-nil
↑r-shifted {r⟦ l ↦ e ⟧ rs} {n} = sdr-cons ↑-shifted (↑r-shifted {rs})

↓-↑-comm-var : ∀ m n x
  → m ≤ n
  → n ≢ x
  → ↑-var m (↓-var n x) ≡ ↓-var (suc n) (↑-var m x)
↓-↑-comm-var m n x m≤n n≢x with n ≤? x | m ≤? x
...                        | yes n≤x | yes m≤x with m ≤? pred x | suc n ≤? suc x
...                                            | yes m≤x-1 | yes n+1≤x+1 = n-1+1≡n+1-1 (m<n⇒0<n (≤∧≢⇒< n≤x n≢x))
...                                            | yes m≤x-1 | no  n+1≰x+1 = ⊥-elim (n+1≰x+1 (s≤s n≤x))
...                                            | no  m≰x-1 | yes n+1≤x+1 = ⊥-elim (m≰x-1 (<⇒≤pred m<x)) where m<x = <-transʳ m≤n (≤∧≢⇒< n≤x n≢x)
...                                            | no  m≰x-1 | no  n+1≰x+1 = ⊥-elim (n+1≰x+1 (s≤s n≤x))
↓-↑-comm-var m n x m≤n n≢x | yes n≤x | no  m≰x with m ≤? pred x | suc n ≤? x
...                                            | yes m≤x-1 | yes n+1≤x = ⊥-elim (m≰x (≤-trans m≤n n≤x))
...                                            | yes m≤x-1 | no  n+1≰x = n-1+1≡n+1-1 (m<n⇒0<n (≤∧≢⇒< n≤x n≢x))
...                                            | no  m≰x-1 | yes n+1≤x = refl
...                                            | no  m≰x-1 | no  n+1≰x = ⊥-elim (n+1≰x (≤∧≢⇒< n≤x n≢x))
↓-↑-comm-var m n x m≤n n≢x | no  n≰x | yes m≤x with m ≤? x | suc n ≤? suc x
...                                            | yes m≤x | yes n+1≤x+1 = ⊥-elim (n≰x (≤-pred n+1≤x+1))
...                                            | yes m≤x | no  n+1≰x+1 = refl
...                                            | no  m≰x | yes n+1≤x+1 = refl
...                                            | no  m≰x | no  n+1≰x+1 = ⊥-elim (m≰x m≤x)
↓-↑-comm-var m n x m≤n n≢x | no  n≰x | no  m≰x with m ≤? x | suc n ≤? x
...                                            | yes m≤x | yes n+1≤x = ⊥-elim (m≰x m≤x)
...                                            | yes m≤x | no  n+1≰x = ⊥-elim (m≰x m≤x)
...                                            | no  m≰x | yes n+1≤x = ⊥-elim (n≰x (m+1≤n→m≤n n+1≤x))
...                                            | no  m≰x | no  n+1≰x = refl
  

↓-↑-comm : ∀ e m n
  → m ≤ n
  → e ~↑~ n
  → e ↓ n ↑ m ≡ e ↑ m ↓ (suc n)
↓r-↑r-comm : ∀ rs m n
  → m ≤ n
  → rs ~↑r~ n
  → rs ↓r n ↑r m ≡ rs ↑r m ↓r (suc n)  
↓-↑-comm (𝕔 x) m n m≤n sd = refl
↓-↑-comm (` x) m n m≤n (sd-var n≢x) = cong `_ (↓-↑-comm-var m n x m≤n n≢x)
↓-↑-comm (ƛ e) m n m≤n (sd-lam sd) rewrite ↓-↑-comm e (suc m) (suc n) (s≤s m≤n) sd = refl
↓-↑-comm (e₁ · e₂) m n m≤n (sd-app sd₁ sd₂) rewrite ↓-↑-comm e₁ m n m≤n sd₁ | ↓-↑-comm e₂ m n m≤n sd₂ = refl
↓-↑-comm (e ⦂ A) m n m≤n (sd-ann sd) rewrite ↓-↑-comm e m n m≤n sd = refl
↓-↑-comm (𝕣 rs) m n m≤n (sd-rcd x) rewrite ↓r-↑r-comm rs m n m≤n x = refl
↓-↑-comm (e 𝕡 l) m n m≤n (sd-prj sd) rewrite ↓-↑-comm e m n m≤n sd = refl

↓r-↑r-comm rnil m n m≤n sd = refl
↓r-↑r-comm (r⟦ l ↦ e ⟧ rs) m n m≤n (sdr-cons x sd) rewrite ↓-↑-comm e m n m≤n x | ↓r-↑r-comm rs m n m≤n sd = refl


↑-shifted-n : ∀ {e m n}
  → m ≤ suc n
  → e ~↑~ n
  → (e ↑ m) ~↑~ suc n
↑r-shifted-n : ∀ {rs m n}
  → m ≤ suc n
  → rs ~↑r~ n
  → (rs ↑r m) ~↑r~ suc n  
↑-shifted-n {𝕔 x} m≤n+1 sd = sd-c
↑-shifted-n {` x} {m} m≤n+1 (sd-var x₁) with m ≤? x
... | yes p = sd-var λ n+1≡x+1 → x₁ (cong pred n+1≡x+1)
... | no ¬p = sd-var (≢-sym (<⇒≢ (<-transˡ (m≰n⇒n<m ¬p) m≤n+1)))
↑-shifted-n {ƛ e} m≤n+1 (sd-lam sd) = sd-lam (↑-shifted-n (s≤s m≤n+1) sd)
↑-shifted-n {e · e₁} m≤n+1 (sd-app sd sd₁) = sd-app (↑-shifted-n m≤n+1 sd) (↑-shifted-n m≤n+1 sd₁)
↑-shifted-n {e ⦂ x} m≤n+1 (sd-ann sd) = sd-ann (↑-shifted-n m≤n+1 sd)
↑-shifted-n {𝕣 rs} m≤n+1 (sd-rcd x) = sd-rcd (↑r-shifted-n m≤n+1 x)
↑-shifted-n {e 𝕡 l} m≤n+1 (sd-prj sd) = sd-prj (↑-shifted-n m≤n+1 sd)
↑r-shifted-n {rnil} m≤n+1 sdr-nil = sdr-nil
↑r-shifted-n {r⟦ l ↦ e ⟧ rs} m≤n+1 (sdr-cons x₂ sd) = sdr-cons (↑-shifted-n m≤n+1 x₂) (↑r-shifted-n m≤n+1 sd)
