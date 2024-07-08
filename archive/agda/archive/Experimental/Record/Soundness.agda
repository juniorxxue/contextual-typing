module Record.Soundness where

open import Record.Prelude
open import Record.Common
open import Record.Decl
open import Record.Decl.Properties
open import Record.Algo
open import Record.Algo.Properties

infix 5 _⇈
_⇈ : Apps → Apps
_⇈ = up 0

infix 4 _⊩_⇚_
data _⊩_⇚_ : Context → Apps → AppsType → Set where
  ⊩none⇚ : ∀ {Γ}
    → Γ ⊩ [] ⇚ []

  ⊩cons⇚ : ∀ {Γ es As e A}
    → Γ ⊩ es ⇚ As
    → Γ ⊢d ∞ # e ⦂ A
    → Γ ⊩ (e ∷a es) ⇚ (A ∷a As)

  ⊩consl : ∀ {Γ es As l}
    → Γ ⊩ es ⇚ As
    → Γ ⊩ (l ∷l es) ⇚ (l ∷l As)


-- after adding restrictin to s-and₁ and s-and₂, we can have a nice inversion lemma
≤d-z-inv : ∀ {A A'}
  → A ≤d 𝕫 # A'
  → A ≡ A'
≤d-z-inv ≤d-Z = refl
≤d-z-inv (≤d-and₁ A≤A' x) = ⊥-elim (x refl)
≤d-z-inv (≤d-and₂ A≤A' x) = ⊥-elim (x refl)

----------------------------------------------------------------------
--+                                                                +--
--+                             Subst                              +--
--+                                                                +--
----------------------------------------------------------------------

size-apps : Apps → ℕ
size-apps [] = 0
size-apps (_ ∷a as) = 1 + size-apps as
size-apps (_ ∷l as) = 1 + size-apps as

size-ccounter : CCounter → ℕ
size-ccounter Z = 0
size-ccounter (S⇐ j) = 1 + size-ccounter j
size-ccounter (Sl j) = 1 + size-ccounter j

size-icounter : ICounter → ℕ
size-icounter (𝕓 j) = size-ccounter j
size-icounter (S⇒ i) = 1 + size-icounter i

size-counter : Counter → ℕ
size-counter (𝕚 i) = size-icounter i
size-counter ∞ = 1

size-type : Type → ℕ
size-type Int = 0
size-type Float = 0
size-type (* x) = 0
size-type Top = 0
size-type (A ⇒ B) = 1 + size-type A + size-type B
size-type (A & B) = 1 + size-type A + size-type B
size-type τ⟦ l ↦ A ⟧ = 1 + size-type A

size-ccounter>0 : ∀ {k j}
  → size-ccounter j < k
  → 0 < k
size-ccounter>0 {k = k} {j = Z} sz = sz
size-ccounter>0 {k = suc k} {j = S⇐ j} sz = s≤s z≤n
size-ccounter>0 {k = suc k} {j = Sl j} sz = s≤s z≤n

size-counter>0 : ∀ {k i}
  → size-counter i < k
  → 0 < k
size-counter>0 {suc i} {k} sz = s≤s z≤n

size-type-+-l : ∀ {A B k}
  → size-type A + size-type B < k
  → size-type A < k
size-type-+-l sz = m+n<o⇒m<o sz

size-type-+-r : ∀ {A B k}
  → size-type A + size-type B < k
  → size-type B < k
size-type-+-r sz = m+n<o⇒n<o sz

-- a bunch of rewriting lemmas
_+++_ : Apps → Apps → Apps
[] +++ as₂ = as₂
(e ∷a as₁) +++ as₂ = e ∷a (as₁ +++ as₂)
(l ∷l as₁) +++ as₂ = l ∷l (as₁ +++ as₂)

data AppsDes (as : Apps) : Set where

  des-app : ∀ x xs
    → as ≡ xs +++ (x ∷a [])
    → AppsDes as

  des-prj : ∀ l xs
    → as ≡ xs +++ (l ∷l [])
    → AppsDes as  

apps-destruct : ∀ as
  → 0 < size-apps as
  → AppsDes as
apps-destruct (x ∷a []) (s≤s sz) = des-app x [] refl
apps-destruct (x ∷a (y ∷a as)) (s≤s sz) with apps-destruct (y ∷a as) (s≤s z≤n)
... | des-app x' xs eq rewrite eq = des-app x' (x ∷a xs) refl
... | des-prj l xs eq rewrite eq = des-prj l (x ∷a xs) refl
apps-destruct (x ∷a (y ∷l as)) (s≤s sz) with apps-destruct (y ∷l as) (s≤s z≤n)
... | des-app x' xs eq rewrite eq = des-app x' (x ∷a xs) refl
... | des-prj l xs eq rewrite eq = des-prj l (x ∷a xs) refl
apps-destruct (x ∷l []) sz = des-prj x [] refl
apps-destruct (x ∷l (y ∷a as)) (s≤s sz) with apps-destruct (y ∷a as) (s≤s z≤n)
... | des-app x' xs eq rewrite eq = des-app x' (x ∷l xs) refl
... | des-prj l xs eq rewrite eq = des-prj l (x ∷l xs) refl
apps-destruct (x ∷l (y ∷l as)) (s≤s sz) with apps-destruct (y ∷l as) (s≤s z≤n)
... | des-app x' xs eq rewrite eq = des-app x' (x ∷l xs) refl
... | des-prj l xs eq rewrite eq = des-prj l (x ∷l xs) refl

pattern ⟦_⟧a z = z ∷a []
pattern ⟦_⟧l z = z ∷l []

-- tinker with size

size-+++-distri : ∀ xs ys
  → size-apps (xs +++ ys) ≡ size-apps xs + size-apps ys
size-+++-distri [] ys = refl
size-+++-distri (x ∷a xs) ys rewrite size-+++-distri xs ys = refl
size-+++-distri (x ∷l xs) ys rewrite size-+++-distri xs ys = refl

size-apps-+++a : ∀ x xs k
  → suc (size-apps (xs +++ ⟦ x ⟧a)) ≤ suc k
  → suc (size-apps xs) < suc k
size-apps-+++a x xs k (s≤s sz) rewrite size-+++-distri xs ⟦ x ⟧a | +-comm 1 (size-apps xs) = s≤s sz

size-apps-+++l : ∀ l xs k
  → suc (size-apps (xs +++ ⟦ l ⟧l)) ≤ suc k
  → suc (size-apps xs) < suc k
size-apps-+++l l xs k (s≤s sz) rewrite size-+++-distri xs ⟦ l ⟧l | +-comm 1 (size-apps xs) = s≤s sz

rw-apps-gen : ∀ (es) {e es'}
  → e ▻ (es +++ es') ≡ (e ▻ es) ▻ es'
rw-apps-gen [] = refl
rw-apps-gen (x ∷a es) = rw-apps-gen es
rw-apps-gen (x ∷l es) = rw-apps-gen es

rw-apps-a : ∀ es e x
  → e ▻ (es +++ ⟦ x ⟧a) ≡ (e ▻ es) · x
rw-apps-a es e x = rw-apps-gen es {e = e} {es' = ⟦ x ⟧a}

up-+++-distri-a : ∀ xs x
  → up 0 (xs +++ ⟦ x ⟧a) ≡ (up 0 xs) +++ (up 0 ⟦ x ⟧a)
up-+++-distri-a [] x = refl
up-+++-distri-a (x₁ ∷a xs) x rewrite up-+++-distri-a xs x = refl
up-+++-distri-a (x₁ ∷l xs) x rewrite up-+++-distri-a xs x = refl

up-+++-distri-l : ∀ xs l
  → up 0 (xs +++ ⟦ l ⟧l) ≡ (up 0 xs) +++ (up 0 ⟦ l ⟧l)
up-+++-distri-l [] x = refl
up-+++-distri-l (x₁ ∷a xs) x rewrite up-+++-distri-l xs x = refl
up-+++-distri-l (x₁ ∷l xs) x rewrite up-+++-distri-l xs x = refl

rw-apps-l : ∀ es e x
  → e ▻ (es +++ ⟦ x ⟧l) ≡ (e ▻ es) 𝕡 x
rw-apps-l es e x = rw-apps-gen es {e = e} {es' = ⟦ x ⟧l}

-- main proof
¬<0→nil : ∀ {es}
  → ¬ 1 ≤ size-apps es
  → es ≡ []
¬<0→nil {[]} sz = refl
¬<0→nil {x ∷a es} sz = ⊥-elim (sz (s≤s z≤n))
¬<0→nil {x ∷l es} sz = ⊥-elim (sz (s≤s z≤n))

subst-case-0 : ∀ {Γ A B es i e e₁}
  → ¬ 1 ≤ size-apps es
  → Γ , A ⊢d i # e ▻ up 0 es ⦂ B
  → Γ ⊢d 𝕫 # e₁ ⦂ A
  → Γ ⊢d i # ((ƛ e) · e₁) ▻ es ⦂ B
subst-case-0 {es = es} {i = 𝕚 i} sz ⊢1 ⊢2 rewrite ¬<0→nil {es = es} sz = ⊢d-app⇒ (⊢d-lam₂ ⊢1) ⊢2
subst-case-0 {es = es} {i = ∞} sz ⊢1 ⊢2 rewrite ¬<0→nil {es = es} sz = ⊢d-app∞ (⊢d-lam₁ ⊢1) ⊢2

subst-3 : ∀ k₁ k₂ k₃ es {Γ A B e e₁ i}
  → size-apps es < k₁
  → size-counter i < k₂
  → size-type B < k₃
  → Γ , A ⊢d i # e ▻ up 0 es ⦂ B
  → Γ ⊢d 𝕫 # e₁ ⦂ A
  → Γ ⊢d i # ((ƛ e) · e₁) ▻ es ⦂ B
  
subst-3-app : ∀ k₁ k₂ k₃ xs x {Γ A B e e₁ i}
  → (1 + size-apps xs) < k₁
  → size-counter i < k₂
  → size-type B < k₃
  → Γ , A ⊢d i # (e ▻ (xs ⇈)) · (x ↑ 0) ⦂ B
  → Γ ⊢d 𝕫 # e₁ ⦂ A
  → Γ ⊢d i #  (((ƛ e) · e₁) ▻ xs) · x ⦂ B

subst-3-prj : ∀ k₁ k₂ k₃ xs l {Γ A B e e₁ i}
  → (1 + size-apps xs) < k₁
  → size-counter i < k₂
  → size-type B < k₃
  → Γ , A ⊢d i # (e ▻ (xs ⇈)) 𝕡 l ⦂ B
  → Γ ⊢d 𝕫 # e₁ ⦂ A
  → Γ ⊢d i #  (((ƛ e) · e₁) ▻ xs) 𝕡 l ⦂ B

subst-3 (suc k₁) (suc k₂) (suc k₃) es sz₁ sz₂ sz₃ ⊢1 ⊢2 with size-apps es >? 0
subst-3 (suc k₁) (suc k₂) (suc k₃) es {e = e} {e₁ = e₁} sz₁ sz₂ sz₃ ⊢1 ⊢2 | yes p with apps-destruct es p
... | des-app x xs eq rewrite eq
                            | rw-apps-a xs ((ƛ e) · e₁) x
                            | up-+++-distri-a xs x
                            | rw-apps-a (up 0 xs) e (x ↑ 0)
  = subst-3-app (suc k₁) (suc k₂) (suc k₃) xs x (size-apps-+++a x xs k₁ sz₁) sz₂ sz₃ ⊢1 ⊢2
... | des-prj l xs eq rewrite eq
                            | rw-apps-l xs ((ƛ e) · e₁) l
                            | up-+++-distri-l xs l
                            | rw-apps-l (up 0 xs) e l
  = subst-3-prj (suc k₁) (suc k₂) (suc k₃) xs l (size-apps-+++l l xs k₁ sz₁) sz₂ sz₃ ⊢1 ⊢2
subst-3 (suc k₁) (suc k₂) (suc k₃) es sz₁ sz₂ sz₃ ⊢1 ⊢2 | no ¬p = subst-case-0 {es = es} ¬p ⊢1 ⊢2

subst-3-app (suc k₁) (suc k₂) (suc k₃) xs x sz₁ sz₂ sz₃ (⊢d-app⇐ {A = A} {B = B} ⊢1 ⊢3) ⊢2 =
  let ind-e₁ = subst-3 k₁ (suc (suc k₂)) (suc (suc (size-type A) + (size-type B))) xs (≤-pred sz₁) (s≤s sz₂) (s≤s m≤m) ⊢1 ⊢2
  in (⊢d-app⇐ ind-e₁ (⊢d-strengthen-0 ⊢3))
{-  
subst-3-app (suc k₁) (suc k₂) (suc k₃) xs x sz₁ sz₂ sz₃ (⊢d-app∞∞ {A = A} {B = B} ⊢1 ⊢3) ⊢2 = 
  let ind-e₁ = subst-3 k₁ (suc (suc k₂)) (suc (suc (size-type A) + (size-type B))) xs (≤-pred sz₁) (s≤s (s≤s z≤n)) (s≤s m≤m) ⊢1 ⊢2
  in (⊢d-app∞∞ ind-e₁ (⊢d-strengthen-0 ⊢3))
-}  
subst-3-app (suc k₁) (suc k₂) (suc k₃) xs x sz₁ sz₂ sz₃ (⊢d-app∞ {A = A} {B = B} ⊢1 ⊢3) ⊢2 =
  let ind-e₁ = subst-3 k₁ (suc (suc k₂)) (suc (suc (size-type A) + (size-type B))) xs (≤-pred sz₁) (s≤s (s≤s z≤n)) (s≤s m≤m) ⊢1 ⊢2
  in (⊢d-app∞ ind-e₁ (⊢d-strengthen-0 ⊢3))
subst-3-app (suc k₁) (suc k₂) (suc k₃) xs x sz₁ sz₂ sz₃ (⊢d-app⇒ {A = A} {B = B} ⊢1 ⊢3) ⊢2 =
  let ind-e₁ = subst-3 k₁ (suc (suc k₂)) (suc (suc (size-type A) + (size-type B))) xs (≤-pred sz₁) (s≤s sz₂) (s≤s m≤m) ⊢1 ⊢2
  in ⊢d-app⇒ ind-e₁ (⊢d-strengthen-0 ⊢3)
subst-3-app (suc k₁) (suc k₂) (suc k₃) xs x {i = 𝕚 (𝕓 Z)} sz₁ sz₂ sz₃ (⊢d-sub {B = B} ⊢1 A≤B j≢Z) ⊢2 = ⊥-elim (j≢Z refl)
subst-3-app (suc k₁) (suc k₂) (suc k₃) xs x {i = 𝕚 (𝕓 (S⇐ j))} sz₁ sz₂ sz₃ (⊢d-sub {B = B} ⊢1 A≤B j≢Z) ⊢2 =
  ⊢d-sub' (subst-3-app (suc k₁) k₂ (suc (size-type B)) xs x sz₁ (size-ccounter>0 {j = j} (<-pred sz₂)) (s≤s m≤m) ⊢1 ⊢2) A≤B
subst-3-app (suc k₁) (suc k₂) (suc k₃) xs x {i = 𝕚 (𝕓 (Sl j))} sz₁ sz₂ sz₃ (⊢d-sub {B = B} ⊢1 A≤B j≢Z) ⊢2 =
  ⊢d-sub' (subst-3-app (suc k₁) k₂ (suc (size-type B)) xs x sz₁ (size-ccounter>0 {j = j} (<-pred sz₂)) (s≤s m≤m) ⊢1 ⊢2) A≤B
subst-3-app (suc k₁) (suc k₂) (suc k₃) xs x {i = 𝕚 (S⇒ i)} sz₁ sz₂ sz₃ (⊢d-sub {B = B} ⊢1 A≤B j≢Z) ⊢2 =
 ⊢d-sub' (subst-3-app (suc k₁) k₂ (suc (size-type B)) xs x sz₁ (size-counter>0 {i = 𝕚 i} (<-pred sz₂)) (s≤s m≤m) ⊢1 ⊢2) A≤B
subst-3-app (suc k₁) (suc k₂) (suc k₃) xs x {i = ∞} sz₁ sz₂ sz₃ (⊢d-sub {B = B} ⊢1 A≤B j≢Z) ⊢2 = 
  ⊢d-sub' (subst-3-app (suc k₁) k₂ (suc (size-type B)) xs x sz₁ (<-pred sz₂) (s≤s m≤m) ⊢1 ⊢2) A≤B
subst-3-app (suc k₁) (suc k₂) (suc k₃) xs x sz₁ sz₂ sz₃ (⊢d-& {A = A} {B = B} ⊢1 ⊢3) ⊢2 =
  ⊢d-& (subst-3-app (suc k₁) (suc k₂) k₃ xs x sz₁ sz₂ (size-type-+-l {A = A} {B = B} (<-pred sz₃)) ⊢1 ⊢2)
       (subst-3-app (suc k₁) (suc k₂) k₃ xs x sz₁ sz₂ (size-type-+-r {A = A} {B = B} (<-pred sz₃)) ⊢3 ⊢2)

subst-3-prj (suc k₁) (suc k₂) (suc k₃) xs l {i = 𝕚 (𝕓 Z)} sz₁ sz₂ sz₃ (⊢d-sub ⊢1 A≤B i≢Z) ⊢2 = ⊥-elim (i≢Z refl)
subst-3-prj (suc k₁) (suc k₂) (suc k₃) xs l {i = 𝕚 (𝕓 (S⇐ j))} sz₁ sz₂ sz₃ (⊢d-sub {B = B} ⊢1 A≤B i≢Z) ⊢2 =
  ⊢d-sub' (subst-3-prj (suc k₁) k₂ (suc (size-type B)) xs l sz₁ (size-ccounter>0 {j = j} (<-pred sz₂)) (s≤s m≤m) ⊢1 ⊢2) A≤B
subst-3-prj (suc k₁) (suc k₂) (suc k₃) xs l {i = 𝕚 (𝕓 (Sl j))} sz₁ sz₂ sz₃ (⊢d-sub {B = B} ⊢1 A≤B i≢Z) ⊢2 =
  ⊢d-sub' (subst-3-prj (suc k₁) k₂ (suc (size-type B)) xs l sz₁ (size-ccounter>0 {j = j} (<-pred sz₂)) (s≤s m≤m) ⊢1 ⊢2) A≤B
subst-3-prj (suc k₁) (suc k₂) (suc k₃) xs l {i = 𝕚 (S⇒ i)} sz₁ sz₂ sz₃ (⊢d-sub {B = B} ⊢1 A≤B i≢Z) ⊢2 =
  ⊢d-sub' (subst-3-prj (suc k₁) k₂ (suc (size-type B)) xs l sz₁ (size-counter>0 {i = 𝕚 i} (<-pred sz₂)) (s≤s m≤m) ⊢1 ⊢2) A≤B
subst-3-prj (suc k₁) (suc k₂) (suc k₃) xs l {i = ∞} sz₁ sz₂ sz₃ (⊢d-sub {B = B} ⊢1 A≤B i≢Z) ⊢2 =
  ⊢d-sub' (subst-3-prj (suc k₁) k₂ (suc (size-type B)) xs l sz₁ (<-pred sz₂) (s≤s m≤m) ⊢1 ⊢2) A≤B
subst-3-prj (suc k₁) (suc k₂) (suc k₃) xs l sz₁ sz₂ sz₃ (⊢d-& {A = A} {B = B} ⊢1 ⊢3) ⊢2 =
  ⊢d-& (subst-3-prj (suc k₁) (suc k₂) k₃ xs l sz₁ sz₂ (size-type-+-l {A = A} {B = B} (<-pred sz₃)) ⊢1 ⊢2)
       (subst-3-prj (suc k₁) (suc k₂) k₃ xs l sz₁ sz₂ (size-type-+-r {A = A} {B = B} (<-pred sz₃)) ⊢3 ⊢2)
subst-3-prj (suc k₁) (suc k₂) (suc k₃) xs l sz₁ sz₂ sz₃ (⊢d-prj {l = l} {A = A} ⊢1) ⊢2 =
  let ind-e₁ = subst-3 k₁ (suc (suc k₂)) (suc (suc (size-type A))) xs (≤-pred sz₁) (s≤s sz₂) (s≤s m≤m) ⊢1 ⊢2
  in (⊢d-prj ind-e₁)
subst-3-prj (suc k₁) (suc k₂) (suc k₃) xs l sz₁ sz₂ sz₃ (⊢d-prj∞ {l = l} {A = A} ⊢1) ⊢2 =
  let ind-e₁ = subst-3 k₁ (suc (suc k₂)) (suc (suc (size-type A))) xs (≤-pred sz₁) (s≤s (s≤s z≤n)) (s≤s m≤m) ⊢1 ⊢2
  in (⊢d-prj∞ ind-e₁)

subst :  ∀ {Γ A B e e₁ i} (es : Apps)
  → Γ , A ⊢d i # e ▻ up 0 es ⦂ B
  → Γ ⊢d 𝕫 # e₁ ⦂ A
  → Γ ⊢d i # ((ƛ e) · e₁) ▻ es ⦂ B
subst {B = B} {i = i} es ⊢1 ⊢2 =
  subst-3 (suc (size-apps es)) (suc (size-counter i)) (suc (size-type B)) es (s≤s m≤m) (s≤s m≤m) (s≤s m≤m) ⊢1 ⊢2

----------------------------------------------------------------------
--+                                                                +--
--+                           Soundness                            +--
--+                                                                +--
----------------------------------------------------------------------

ⅉ : Apps → CCounter
ⅉ [] = Z
ⅉ (_ ∷a as) = S⇐ (ⅉ as)
ⅉ (_ ∷l as) = Sl (ⅉ as)

H≢□→j≢Z : ∀ {H A' es As A''}
  → H ≢ □
  → ⟦ H , A' ⟧→⟦ es , □ , As , A'' ⟧
  → 𝕚 (𝕓 (ⅉ es)) ≢ 𝕫
H≢□→j≢Z {H = □} H≢□ spl = ⊥-elim (H≢□ refl)
H≢□→j≢Z {H = ⟦ x ⟧⇒ H} H≢□ (have-a spl) = λ ()
H≢□→j≢Z {H = ⌊ x ⌋⇒ H} H≢□ (have-l spl) = λ ()

app-elim : ∀ {Γ e as H A A' As}
  → Γ ⊢d 𝕚 (𝕓 (ⅉ as)) # e ⦂ A
  → ⟦ H , A ⟧→⟦ as , □ , As , A' ⟧
  → Γ ⊩ as ⇚ As
  → Γ ⊢d 𝕫 # e ▻ as ⦂ A'
app-elim ⊢e none-□ ⊩none⇚ = ⊢e
app-elim ⊢e (have-a spl) (⊩cons⇚ ⊢as x) = app-elim (⊢d-app⇐ ⊢e x) spl ⊢as
app-elim ⊢e (have-l spl) (⊩consl ⊢as) = app-elim (⊢d-prj ⊢e) spl ⊢as

app-elim' : ∀ {Γ e as H A A' As T}
  → Γ ⊢d 𝕚 (𝕓 (ⅉ as)) # e ⦂ A
  → ⟦ H , A ⟧→⟦ as , τ T , As , A' ⟧
  → Γ ⊩ as ⇚ As
  → Γ ⊢d ∞ # e ▻ as ⦂ A'
app-elim' ⊢e none-τ ⊩none⇚ = ⊢d-sub' ⊢e ≤d-refl∞
app-elim' ⊢e (have-a spl) (⊩cons⇚ ⊢as x) = app-elim' (⊢d-app⇐ ⊢e x) spl ⊢as
app-elim' ⊢e (have-l spl) (⊩consl ⊢as) = app-elim' (⊢d-prj ⊢e) spl ⊢as
  
sound-inf : ∀ {Γ e H A es As A'}
  → Γ ⊢a H ⇛ e ⇛ A
  → ⟦ H , A ⟧→⟦ es , □ , As , A' ⟧
  → Γ ⊢d 𝕫 # e ▻ es ⦂ A'

sound-chk : ∀ {Γ e H A es T As A'}
  → Γ ⊢a H ⇛ e ⇛ A
  → ⟦ H , A ⟧→⟦ es , τ T , As , A' ⟧
  → Γ ⊢d ∞ # e ▻ es ⦂ T

sound-≤ : ∀ {Γ A H A' A'' es As}
  → Γ ⊢a A ≤ H ⇝ A'
  → ⟦ H , A' ⟧→⟦ es , □ , As , A'' ⟧
  →  A ≤d 𝕚 (𝕓 (ⅉ es)) # A'

sound-≤-chk : ∀ {Γ A H A' A'' es As T}
  → Γ ⊢a A ≤ H ⇝ A'
  → ⟦ H , A' ⟧→⟦ es , τ T , As , A'' ⟧
  → A ≤d 𝕚 (𝕓 (ⅉ es)) # A'

sound-es : ∀ {Γ A₁ H A As A' es H'}
  → Γ ⊢a A₁ ≤ H ⇝ A
  → ⟦ H , A ⟧→⟦ es , H' , As , A' ⟧
  → Γ ⊩ es ⇚ As

sound-inf-0 : ∀ {Γ e A}
  → Γ ⊢a □ ⇛ e ⇛ A
  → Γ ⊢d 𝕫 # e ⦂ A
sound-inf-0 ⊢e = sound-inf ⊢e none-□

sound-chk-0 : ∀ {Γ e A}
  → Γ ⊢a τ A ⇛ e ⇛ A
  → Γ ⊢d ∞ # e ⦂ A
sound-chk-0 ⊢e = sound-chk ⊢e none-τ

sound-r : ∀ {Γ rs A}
  → Γ ⊢r □ ⇛ rs ⇛ A
  → Γ ⊢r 𝕫 # rs ⦂ A
sound-r ⊢a-nil = ⊢r-nil
sound-r (⊢a-one x) = ⊢r-one (sound-inf-0 x)
sound-r (⊢a-cons x ⊢rs) = ⊢r-cons (sound-inf-0 x) (sound-r ⊢rs)

sound-inf ⊢a-c none-□ = ⊢d-c
sound-inf (⊢a-var x) none-□ = ⊢d-var x
sound-inf (⊢a-ann ⊢e) none-□ = ⊢d-ann (sound-chk-0 ⊢e)
sound-inf (⊢a-app ⊢e) spl = sound-inf ⊢e (have-a spl)
sound-inf {es = e ∷a es} (⊢a-lam₂ ⊢e ⊢e₁) (have-a spl) = subst es (sound-inf ⊢e₁ (spl-weaken spl)) (sound-inf-0 ⊢e)
sound-inf (⊢a-sub x ⊢e x₁ H≢□) spl = app-elim (⊢d-sub' (sound-inf-0 ⊢e) (sound-≤ x₁ spl)) spl (sound-es x₁ spl)
sound-inf (⊢a-rcd x) none-□ = ⊢d-rcd (sound-r x)
sound-inf (⊢a-prj ⊢e) spl = sound-inf ⊢e (have-l spl)

sound-chk (⊢a-app ⊢e) spl = sound-chk ⊢e (have-a spl)
sound-chk (⊢a-lam₁ ⊢e) none-τ = ⊢d-lam₁ (sound-chk ⊢e none-τ)
sound-chk {es = e ∷a es} (⊢a-lam₂ ⊢e ⊢e₁) (have-a spl) = subst es (sound-chk ⊢e₁ (spl-weaken spl)) (sound-inf-0 ⊢e)
sound-chk ⊢e'@(⊢a-sub pv-e ⊢e A≤H H≢□) spl rewrite ⊢a-spl-τ ⊢e' spl = app-elim' (⊢d-sub' (sound-inf-0 ⊢e) (sound-≤-chk A≤H spl)) spl (sound-es A≤H spl)
-- app-elim' (⊢d-sub' (sound-inf-0 ⊢e) (sound-≤-chk A≤H spl)) spl (sound-es A≤H spl)
sound-chk (⊢a-& ⊢e ⊢e₁) none-τ = ⊢d-& (sound-chk ⊢e none-τ) (sound-chk ⊢e₁ none-τ)
sound-chk (⊢a-prj ⊢e) spl = sound-chk ⊢e (have-l spl)

sound-≤ ≤a-□ none-□ = ≤d-Z
sound-≤ (≤a-hint x A≤H) (have-a spl) = ≤d-arr-S⇐ ≤d-refl∞ (sound-≤ A≤H spl)
sound-≤ (≤a-hint-l A≤H) (have-l spl) = ≤d-rcd-Sl (sound-≤ A≤H spl)
sound-≤ (≤a-and-l A≤H x) spl = ≤d-and₁ (sound-≤ A≤H spl) (H≢□→j≢Z x spl)
sound-≤ (≤a-and-r A≤H x) spl = ≤d-and₂ (sound-≤ A≤H spl) (H≢□→j≢Z x spl)

sound-≤-chk ≤a-int none-τ = ≤d-Z
sound-≤-chk ≤a-float none-τ = ≤d-Z
sound-≤-chk ≤a-base none-τ = ≤d-Z
sound-≤-chk ≤a-top none-τ = {!!}
sound-≤-chk (≤a-arr A≤H A≤H₁) spl = {!!}
sound-≤-chk (≤a-rcd A≤H) spl = {!!}
sound-≤-chk (≤a-hint x A≤H) spl = {!!}
sound-≤-chk (≤a-hint-l A≤H) spl = {!!}
sound-≤-chk (≤a-and-l A≤H x) spl = {!!}
sound-≤-chk (≤a-and-r A≤H x) spl = {!!}
sound-≤-chk (≤a-and A≤H A≤H₁) spl = {!!}

sound-es ≤a-int none-τ = ⊩none⇚
sound-es ≤a-float none-τ = ⊩none⇚
sound-es ≤a-base none-τ = ⊩none⇚
sound-es ≤a-top none-τ = ⊩none⇚
sound-es ≤a-□ none-□ = ⊩none⇚
sound-es (≤a-arr A≤H A≤H₁) none-τ = ⊩none⇚
sound-es (≤a-rcd A≤H) none-τ = ⊩none⇚
sound-es (≤a-hint x A≤H) (have-a spl) = ⊩cons⇚ (sound-es A≤H spl) (sound-chk-0 x)
sound-es (≤a-hint-l A≤H) (have-l spl) = ⊩consl (sound-es A≤H spl)
sound-es (≤a-and-l A≤H x) spl = sound-es A≤H spl
sound-es (≤a-and-r A≤H x) spl = sound-es A≤H spl
sound-es (≤a-and A≤H A≤H₁) none-τ = ⊩none⇚
