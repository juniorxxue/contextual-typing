module Poly.Decl.Subst where

open import Poly.Common
open import Poly.Decl
open import Poly.Decl.Properties

----------------------------------------------------------------------
--+                              Roll                              +--
----------------------------------------------------------------------

data Apps : ℕ → ℕ → Set where
  nil : Apps n m
  _∷a_ : Term n m → Apps n m → Apps n m
  _∷t_ : Type m → Apps n m → Apps n m

data AppsType : ℕ → Set where
  nil : AppsType m
  _∷a_ : Type m → AppsType m → AppsType m
  _∷t_ : Type m → AppsType m → AppsType m

_▻_ : Term n m → Apps n m → Term n m
e ▻ nil = e
e ▻ (e' ∷a es) = (e · e') ▻ es
e ▻ (A  ∷t es) = (e [ A ]) ▻ es

up : Fin (1 + n) → Apps n m → Apps (1 + n) m
up n nil = nil
up n (e ∷a as) = (↑tm n e) ∷a (up n as)
up n (A ∷t as) = A ∷t (up n as)

up0 : Apps n m → Apps (1 + n) m
up0 = up #0

size-apps : Apps n m → ℕ
size-apps nil = 0
size-apps (_ ∷a as) = 1 + size-apps as
size-apps (_ ∷t as) = 1 + size-apps as

size-counter : Counter → ℕ
size-counter Z = 0
size-counter ∞ = 1
size-counter (S j) = 1 + size-counter j
size-counter (Sτ j) = 1 + size-counter j

size-counter≥0 : ∀ j
  → 0 ≤ size-counter j
size-counter≥0 Z = z≤n
size-counter≥0 ∞ = z≤n
size-counter≥0 (S j) = z≤n
size-counter≥0 (Sτ j) = z≤n

size-type : Type m → ℕ
size-type Int = 0
size-type (‶ X) = 0
size-type (A `→ B) = 1 + size-type A + size-type B
size-type (`∀ A) = 1 + size-type A

-- a bunch of rewriting lemmas
_+++_ : Apps n m → Apps n m → Apps n m
nil +++ as₂ = as₂
(e ∷a as₁) +++ as₂ = e ∷a (as₁ +++ as₂)
(A ∷t as₁) +++ as₂ = A ∷t (as₁ +++ as₂)

data AppsDes (as : Apps n m) : Set where

  des-app : ∀ x x̅
    → as ≡ x̅ +++ (x ∷a nil)
    → AppsDes as

  des-tapp : ∀ A x̅
    → as ≡ x̅ +++ (A ∷t nil)
    → AppsDes as

apps-destruct : ∀ (as : Apps n m)
  → 0 < size-apps as
  → AppsDes as
apps-destruct (x ∷a nil) (s≤s sz) = des-app x nil refl
apps-destruct (x ∷a (y ∷a as)) (s≤s sz) with apps-destruct (y ∷a as) (s≤s z≤n)
... | des-app x' x̅ eq rewrite eq = des-app x' (x ∷a x̅) refl
... | des-tapp l x̅ eq rewrite eq = des-tapp l (x ∷a x̅) refl
apps-destruct (x ∷a (y ∷t as)) (s≤s sz) with apps-destruct (y ∷t as) (s≤s z≤n)
... | des-app x' x̅ eq rewrite eq = des-app x' (x ∷a x̅) refl
... | des-tapp l x̅ eq rewrite eq = des-tapp l (x ∷a x̅) refl
apps-destruct (x ∷t nil) sz = des-tapp x nil refl
apps-destruct (x ∷t (y ∷a as)) (s≤s sz) with apps-destruct (y ∷a as) (s≤s z≤n)
... | des-app x' x̅ eq rewrite eq = des-app x' (x ∷t x̅) refl
... | des-tapp l x̅ eq rewrite eq = des-tapp l (x ∷t x̅) refl
apps-destruct (x ∷t (y ∷t as)) (s≤s sz) with apps-destruct (y ∷t as) (s≤s z≤n)
... | des-app x' x̅ eq rewrite eq = des-app x' (x ∷t x̅) refl
... | des-tapp l x̅ eq rewrite eq = des-tapp l (x ∷t x̅) refl

pattern ⟦_⟧a z = z ∷a nil
pattern ⟦_⟧t z = z ∷t nil

rw-apps-gen : ∀ (es : Apps n m) {e es'}
  → e ▻ (es +++ es') ≡ (e ▻ es) ▻ es'
rw-apps-gen nil = refl
rw-apps-gen (x ∷a es) = rw-apps-gen es
rw-apps-gen (A ∷t es) = rw-apps-gen es

rw-apps-a : ∀ (es : Apps n m) e x
  → e ▻ (es +++ ⟦ x ⟧a) ≡ (e ▻ es) · x
rw-apps-a es e x = rw-apps-gen es {e = e} {es' = ⟦ x ⟧a}

up-+++-distri-a : ∀ (x̅ : Apps n m) x
  → up0 (x̅ +++ ⟦ x ⟧a) ≡ (up0 x̅) +++ (up0 ⟦ x ⟧a)
up-+++-distri-a nil x = refl
up-+++-distri-a (x₁ ∷a x̅) x rewrite up-+++-distri-a x̅ x = refl
up-+++-distri-a (x₁ ∷t x̅) x rewrite up-+++-distri-a x̅ x = refl

up-+++-distri-l : ∀ (x̅ : Apps n m) A
  → up0 (x̅ +++ ⟦ A ⟧t) ≡ (up0 x̅) +++ (up0 ⟦ A ⟧t)
up-+++-distri-l nil x = refl
up-+++-distri-l (x₁ ∷a x̅) x rewrite up-+++-distri-l x̅ x = refl
up-+++-distri-l (x₁ ∷t x̅) x rewrite up-+++-distri-l x̅ x = refl

size-+++-distri : ∀ (x̅ : Apps n m) ys
  → size-apps (x̅ +++ ys) ≡ size-apps x̅ + size-apps ys
size-+++-distri nil ys = refl
size-+++-distri (x ∷a x̅) ys rewrite size-+++-distri x̅ ys = refl
size-+++-distri (x ∷t x̅) ys rewrite size-+++-distri x̅ ys = refl

size-apps-+++a : ∀ x (x̅ : Apps n m) k
  → suc (size-apps (x̅ +++ ⟦ x ⟧a)) ≤ suc k
  → suc (size-apps x̅) < suc k
size-apps-+++a x x̅ k (s≤s sz) rewrite size-+++-distri x̅ ⟦ x ⟧a | +-comm 1 (size-apps x̅) = s≤s sz

size-apps-+++l : ∀ l (x̅ : Apps n m) k
  → suc (size-apps (x̅ +++ ⟦ l ⟧t)) ≤ suc k
  → suc (size-apps x̅) < suc k
size-apps-+++l l x̅ k (s≤s sz) rewrite size-+++-distri x̅ ⟦ l ⟧t | +-comm 1 (size-apps x̅) = s≤s sz

rw-apps-t : ∀ (es : Apps n m) e x
  → e ▻ (es +++ ⟦ x ⟧t) ≡ (e ▻ es) [ x ]
rw-apps-t es e x = rw-apps-gen es {e = e} {es' = ⟦ x ⟧t}


-- main proof
¬<0→nil : ∀ {es : Apps n m}
  → ¬ 1 ≤ size-apps es
  → es ≡ nil
¬<0→nil {es = nil} sz = refl
¬<0→nil {es = x ∷a es} sz = ⊥-elim (sz (s≤s z≤n))
¬<0→nil {es = x ∷t es} sz = ⊥-elim (sz (s≤s z≤n))

subst-case-0 : ∀ {Γ : Env n m} {A B es j e e₁}
  → ¬ 1 ≤ size-apps es
  → Γ , A ⊢ j # e ▻ up0 es ⦂ B
  → Γ ⊢ Z # e₁ ⦂ A
  → Γ ⊢ j # ((ƛ e) · e₁) ▻ es ⦂ B
subst-case-0 {es = es} sz ⊢1 ⊢2 rewrite ¬<0→nil {es = es} sz = ⊢app₂ (⊢lam₂ ⊢1) ⊢2

subst-3 : ∀ k₁ k₂ k₃ e̅ {Γ : Env n m} {A B e e₁ j}
  → size-apps e̅ < k₁
  → size-counter j < k₂
  → size-type B < k₃
  → Γ , A ⊢ j # e ▻ up0 e̅ ⦂ B
  → Γ ⊢ Z # e₁ ⦂ A
  → Γ ⊢ j # ((ƛ e) · e₁) ▻ e̅ ⦂ B

subst-3-app : ∀ k₁ k₂ k₃ x̅ x {Γ : Env n m} {A B e e₁ j}
  → (1 + size-apps x̅) < k₁
  → size-counter j < k₂
  → size-type B < k₃
  → Γ , A ⊢ j # (e ▻ (up0 x̅)) · (↑tm0 x) ⦂ B
  → Γ ⊢ Z # e₁ ⦂ A
  → Γ ⊢ j #  (((ƛ e) · e₁) ▻ x̅) · x ⦂ B

subst-3-tapp : ∀ k₁ k₂ k₃ x̅ C {Γ : Env n m} {A B e e₁ j}
  → (1 + size-apps x̅) < k₁
  → size-counter j < k₂
  → size-type B < k₃
  → Γ , A ⊢ j # (e ▻ (up0 x̅)) [ C ] ⦂ B
  → Γ ⊢ Z # e₁ ⦂ A
  → Γ ⊢ j #  (((ƛ e) · e₁) ▻ x̅) [ C ] ⦂ B



subst-3-app (suc k₁) (suc k₂) (suc k₃) xs x sz₁ sz₂ sz₃ (⊢app₁ {A = A} {B = B} ⊢1 ⊢3) ⊢2 =
  let ind-e₁ = subst-3 k₁ (suc (suc k₂)) (suc (suc (size-type A) + (size-type B))) xs (≤-pred sz₁) (s≤s z≤n) (s≤s m≤m) ⊢1 ⊢2
  in (⊢app₁ ind-e₁ (strengthen-0 ⊢3))
subst-3-app (suc k₁) (suc k₂) (suc k₃) xs x sz₁ sz₂ sz₃ (⊢app₂ {A = A} {B = B} ⊢1 ⊢3) ⊢2 =
  let ind-e₁ = subst-3 k₁ (suc (suc k₂)) (suc (suc (size-type A) + (size-type B))) xs (≤-pred sz₁) (s≤s sz₂) (s≤s m≤m) ⊢1 ⊢2
  in ⊢app₂ ind-e₁ (strengthen-0 ⊢3)  
subst-3-app (suc k₁) (suc k₂) (suc k₃) xs x {j = Z} sz₁ sz₂ sz₃ (⊢sub ⊢1 s j≢Z) ⊢2 = ⊥-elim (j≢Z refl)
subst-3-app (suc k₁) (suc k₂) (suc k₃) xs x {j = ∞} sz₁ sz₂ sz₃ (⊢sub {B = B} ⊢1 s j≢Z) ⊢2 =
  ⊢sub' (subst-3-app (suc k₁) k₂ (suc (size-type B)) xs x sz₁ (<-pred sz₂) (s≤s m≤m) ⊢1 ⊢2) (s-weaken-tm-0 s)
subst-3-app (suc k₁) (suc k₂) (suc k₃) xs x {j = S j} sz₁ sz₂ sz₃ (⊢sub {B = B} ⊢1 s j≢Z) ⊢2 =
  ⊢sub' (subst-3-app (suc k₁) k₂ (suc (size-type B)) xs x sz₁ sz-proof (s≤s m≤m) ⊢1 ⊢2) (s-weaken-tm-0 s)
    where sz-proof = (≤-<-trans (size-counter≥0 j) (<-pred sz₂))
subst-3-app (suc k₁) (suc k₂) (suc k₃) xs x {j = Sτ j} sz₁ sz₂ sz₃ (⊢sub {B = B} ⊢1 s j≢Z) ⊢2 =
  ⊢sub' (subst-3-app (suc k₁) k₂ (suc (size-type B)) xs x sz₁ sz-proof (s≤s m≤m) ⊢1 ⊢2) (s-weaken-tm-0 s)
    where sz-proof = (≤-<-trans (size-counter≥0 j) (<-pred sz₂))

subst-3-tapp (suc k₁) (suc k₂) (suc k₃) xs x {j = Z} sz₁ sz₂ sz₃ (⊢sub {B = B} ⊢1 s j≢Z) ⊢2 = ⊥-elim (j≢Z refl)
subst-3-tapp (suc k₁) (suc k₂) (suc k₃) xs x {j = ∞} sz₁ sz₂ sz₃ (⊢sub {B = B} ⊢1 s j≢Z) ⊢2 =
  ⊢sub' (subst-3-tapp (suc k₁) k₂ (suc (size-type B)) xs x sz₁ (<-pred sz₂) (s≤s m≤m) ⊢1 ⊢2) (s-weaken-tm-0 s)
subst-3-tapp (suc k₁) (suc k₂) (suc k₃) xs x {j = S j} sz₁ sz₂ sz₃ (⊢sub {B = B} ⊢1 s j≢Z) ⊢2 =
  ⊢sub' (subst-3-tapp (suc k₁) k₂ (suc (size-type B)) xs x sz₁ sz-proof (s≤s m≤m) ⊢1 ⊢2) (s-weaken-tm-0 s)
    where sz-proof = (≤-<-trans (size-counter≥0 j) (<-pred sz₂))
subst-3-tapp (suc k₁) (suc k₂) (suc k₃) xs x {j = Sτ j} sz₁ sz₂ sz₃ (⊢sub {B = B} ⊢1 s j≢Z) ⊢2 =
  ⊢sub' (subst-3-tapp (suc k₁) k₂ (suc (size-type B)) xs x sz₁ sz-proof (s≤s m≤m) ⊢1 ⊢2) (s-weaken-tm-0 s)
    where sz-proof = ≤-<-trans (size-counter≥0 j) (<-pred sz₂)

subst-3-tapp (suc k₁) (suc k₂) (suc k₃) xs x sz₁ sz₂ sz₃ (⊢tapp {B = B} ⊢1) ⊢2 =
  let ind-e = subst-3 k₁ (suc (suc k₂)) (1 + (size-type B)) xs (≤-pred sz₁) (s≤s sz₂) (s≤s m≤m) ⊢1 ⊢2
  in ⊢tapp ind-e

subst-3 (suc k₁) (suc k₂) (suc k₃) es sz₁ sz₂ sz₃ ⊢1 ⊢2 with size-apps es >? 0
subst-3 (suc k₁) (suc k₂) (suc k₃) es {e = e} {e₁ = e₁} sz₁ sz₂ sz₃ ⊢1 ⊢2 | yes p with apps-destruct es p
... | des-app x x̅ eq rewrite eq
                            | rw-apps-a x̅ ((ƛ e) · e₁) x
                            | up-+++-distri-a x̅ x
                            | rw-apps-a (up0 x̅) e (↑tm0 x)
  = subst-3-app (suc k₁) (suc k₂) (suc k₃) x̅ x (size-apps-+++a x x̅ k₁ sz₁) sz₂ sz₃ ⊢1 ⊢2
... | des-tapp l x̅ eq rewrite eq
                            | rw-apps-t x̅ ((ƛ e) · e₁) l
                            | up-+++-distri-l x̅ l
                            | rw-apps-t (up0 x̅) e l
  = subst-3-tapp (suc k₁) (suc k₂) (suc k₃) x̅ l (size-apps-+++l l x̅ k₁ sz₁) sz₂ sz₃ ⊢1 ⊢2
subst-3 (suc k₁) (suc k₂) (suc k₃) es sz₁ sz₂ sz₃ ⊢1 ⊢2 | no ¬p = subst-case-0 {es = es} ¬p ⊢1 ⊢2


subst :  ∀ {Γ A B e e₁ j} (e̅ : Apps n m)
  → Γ , A ⊢ j # e ▻ (up0 e̅) ⦂ B
  → Γ ⊢ Z # e₁ ⦂ A
  → Γ ⊢ j # ((ƛ e) · e₁) ▻ e̅ ⦂ B
subst {B = B} {j = j} es ⊢1 ⊢2 =
  subst-3 (suc (size-apps es)) (suc (size-counter j)) (suc (size-type B)) es (s≤s m≤m) (s≤s m≤m) (s≤s m≤m) ⊢1 ⊢2
