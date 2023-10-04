module STLC.Test where

open import STLC.Prelude

data Type : Set where
  Int : Type
  Top : Type
  _⇒_ : Type → Type → Type
  _&_ : Type → Type → Type

-- a isomorphic relation between types --

data _⇠_⇢_ : Type → Type → Type → Set where

  sp-and : ∀ {A B}
    → A ⇠ (A & B) ⇢ B

  sp-arr : ∀ {A B B₁ B₂}
    → B₁ ⇠ B ⇢ B₂
    → (A ⇒ B₁) ⇠ (A ⇒ B) ⇢ (A ⇒ B₂)

data _≲_ : Type → Type → Set where

  ≲-refl : ∀ {A}
    → A ≲ A

  ≲-and : ∀ {A₁ A₂ B B₁ B₂}
    → B₁ ⇠ B ⇢ B₂
    → A₁ ≲ B₁
    → A₂ ≲ B₂
    → (A₁ & A₂) ≲ B

size : Type → ℕ
size Int = 1
size Top = 1
size (A ⇒ B) = 1 + size A + size B
size (A & B) = 1 + size A + size B

size>0 : ∀ A
  → size A > 0
size>0 Int = s≤s z≤n
size>0 Top = s≤s z≤n
size>0 (A ⇒ A₁) = s≤s z≤n
size>0 (A & A₁) = s≤s z≤n

≲-trans-k : ∀ {A B C k}
  → size B < k
  → A ≲ B
  → B ≲ C
  → A ≲ C
≲-trans-k {B = Int} {k = suc k} (s≤s sz) ≲-refl BC = BC
≲-trans-k {B = Top} {k = suc k} sz ≲-refl BC = BC
≲-trans-k {B = B₁ ⇒ B₂} {k = suc k} (s≤s sz) AB ≲-refl = AB
≲-trans-k {B = B₁ & B₂} {k = suc k} (s≤s sz) AB ≲-refl = AB
≲-trans-k {B = B₁ & B₂} {k = suc k} (s≤s sz) ≲-refl (≲-and x BC BC₁) = ≲-and x BC BC₁
≲-trans-k {B = B₁ & B₂} {k = suc k} (s≤s sz) (≲-and sp-and AB AB₁) (≲-and x BC BC₁) =
  ≲-and x
    (≲-trans-k {k = k} (<-trans (m<m+n (size B₁) (size>0 B₂)) sz) AB BC)
    (≲-trans-k {k = k} (<-trans (m<n+m (size B₂) (size>0 B₁)) sz) AB₁ BC₁)

≲-trans : ∀ {A B C}
  → A ≲ B
  → B ≲ C
  → A ≲ C
≲-trans {B = B} = ≲-trans-k (n<1+n (size B))
