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
    → Γ ⊢d ♭ ∞ # e ⦂ A
    → Γ ⊩ (e ∷a es) ⇚ (A ∷a As)

  ⊩consl : ∀ {Γ es As l}
    → Γ ⊩ es ⇚ As
    → Γ ⊩ (l ∷l es) ⇚ (l ∷l As)


-- after adding restrictin to s-and₁ and s-and₂, we can have a nice inversion lemma
≤d-z-inv : ∀ {A A'}
  → A ≤d ♭ Z # A'
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
size-ccounter ∞ = 1
size-ccounter (S⇐ j) = 1 + size-ccounter j
size-ccounter (Sl j) = 1 + size-ccounter j

size-counter : Counter → ℕ
size-counter (♭ j) = size-ccounter j
size-counter (S⇒ i) = 1 + size-counter i

size-type : Type → ℕ
size-type Int = 0
size-type (* x) = 0
size-type Top = 0
size-type (A ⇒ B) = 1 + size-type A + size-type B
size-type (A & B) = 1 + size-type A + size-type B
size-type τ⟦ l ↦ A ⟧ = 1 + size-type A

size-ccounter>0 : ∀ {k j}
  → size-ccounter j < k
  → 0 < k
size-ccounter>0 {k = k} {j = Z} sz = sz
size-ccounter>0 {k = k} {j = ∞} sz = <-trans (s≤s z≤n) sz
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

apps-consa>0 : ∀ {e as}
  → size-apps (e ∷a as) > 0
apps-consa>0 = s≤s z≤n

apps-consl>0 : ∀ {l as}
  → size-apps (l ∷l as) > 0
apps-consl>0 = s≤s z≤n  

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

cons-+++-size : ∀ {e es xs x}
  → (e ∷a es) ≡ (xs +++ ⟦ x ⟧a)
  → size-apps es ≡ size-apps xs
cons-+++-size = {!!}

size-apps-+++a : ∀ {e es x xs k}
  → suc (suc (size-apps es)) ≤ suc k
  → (e ∷a es) ≡ (xs +++ ⟦ x ⟧a)
  → suc (size-apps xs) < suc k
size-apps-+++a = {!!}  

size-apps-+++l : ∀ {e es x xs k}
  → suc (suc (size-apps es)) ≤ suc k
  → (e ∷l es) ≡ (xs +++ ⟦ x ⟧l)
  → suc (size-apps xs) < suc k
size-apps-+++l = {!!}  

rw-+++-app : ∀ {Γ e₁ e₂ es j B xs x}
  → Γ ⊢d j # e₁ ▻ (xs +++ ⟦ x ⟧a) ⦂ B
  → (e₂ ∷a es) ≡ (xs +++ ⟦ x ⟧a)
  → Γ ⊢d j # (e₁ · e₂) ▻ es ⦂ B
rw-+++-app ⊢e eq rewrite (sym eq) = ⊢e

rw-+++-app' : ∀ {Γ e₁ e₂ es j B xs x}
  → Γ ⊢d j # (e₁ · e₂) ▻ es ⦂ B
  → (e₂ ∷a es) ≡ (xs +++ ⟦ x ⟧a)
  → Γ ⊢d j # e₁ ▻ (xs +++ ⟦ x ⟧a) ⦂ B
rw-+++-app' ⊢e eq rewrite (sym eq) = ⊢e

rw-+++-prj : ∀ {Γ e₁ e₂ es j B xs x}
  → Γ ⊢d j # e₁ ▻ (xs +++ ⟦ x ⟧l) ⦂ B
  → (e₂ ∷l es) ≡ (xs +++ ⟦ x ⟧l)
  → Γ ⊢d j # (e₁ 𝕡 e₂) ▻ es ⦂ B
rw-+++-prj ⊢e eq rewrite (sym eq) = ⊢e

rw-+++-prj' : ∀ {Γ e₁ e₂ es j B xs x}
  → Γ ⊢d j # (e₁ 𝕡 e₂) ▻ es ⦂ B
  → (e₂ ∷l es) ≡ (xs +++ ⟦ x ⟧l)
  → Γ ⊢d j # e₁ ▻ (xs +++ ⟦ x ⟧l) ⦂ B
rw-+++-prj' ⊢e eq rewrite (sym eq) = ⊢e

rw-apps-gen : ∀ (es) {e es'}
  → e ▻ (es +++ es') ≡ (e ▻ es) ▻ es'
rw-apps-gen [] = refl
rw-apps-gen (x ∷a es) = rw-apps-gen es
rw-apps-gen (x ∷l es) = rw-apps-gen es

rw-apps-a : ∀ {es e x}
  → e ▻ (es +++ ⟦ x ⟧a) ≡ (e ▻ es) · x
rw-apps-a {es} {e} {x} = rw-apps-gen es {e = e} {es' = ⟦ x ⟧a}

rw-apps-l : ∀ {es e x}
  → e ▻ (es +++ ⟦ x ⟧l) ≡ (e ▻ es) 𝕡 x
rw-apps-l {es} {e} {x} = rw-apps-gen es {e = e} {es' = ⟦ x ⟧l}

rw-⊢apps-a : ∀ {Γ j es e x A}
  → Γ ⊢d j # e ▻ (es +++ ⟦ x ⟧a) ⦂ A
  → Γ ⊢d j # (e ▻ es) · x ⦂ A
rw-⊢apps-a {es = es} {e = e} {x = x} ⊢e rewrite rw-apps-a {es} {e} {x} = ⊢e

rw-⊢apps-a' : ∀ {Γ j es e x A}
  → Γ ⊢d j # (e ▻ es) · x ⦂ A
  → Γ ⊢d j # e ▻ (es +++ ⟦ x ⟧a) ⦂ A
rw-⊢apps-a' {es = es} {e = e} {x = x} ⊢e rewrite rw-apps-a {es} {e} {x} = ⊢e

rw-⊢apps-l : ∀ {Γ j es e x A}
  → Γ ⊢d j # e ▻ (es +++ ⟦ x ⟧l) ⦂ A
  → Γ ⊢d j # (e ▻ es) 𝕡 x ⦂ A
rw-⊢apps-l {es = es} {e = e} {x = x} ⊢e rewrite rw-apps-l {es} {e} {x} = ⊢e

rw-⊢apps-l' : ∀ {Γ j es e x A}
  → Γ ⊢d j # (e ▻ es) 𝕡 x ⦂ A
  → Γ ⊢d j # e ▻ (es +++ ⟦ x ⟧l) ⦂ A
rw-⊢apps-l' {es = es} {e = e} {x = x} ⊢e rewrite rw-apps-l {es} {e} {x} = ⊢e

eq-consa-↑ : ∀ {e es xs x}
  → e ∷a es ≡ xs +++ ⟦ x ⟧a
  → (e ↑ 0) ∷a up 0 es ≡ (up 0 xs) +++ ⟦ x ↑ 0 ⟧a
eq-consa-↑ {xs = xs} {x = x} eq = {!!}

-- main proof
subst-3 : ∀ k₁ k₂ k₃ es {Γ A B e e₁ i}
  → size-apps es < k₁
  → size-counter i < k₂
  → size-type B < k₃
  → Γ , A ⊢d i # e ▻ up 0 es ⦂ B
  → Γ ⊢d ♭ Z # e₁ ⦂ A
  → Γ ⊢d i # ((ƛ e) · e₁) ▻ es ⦂ B
  
subst-3-app : ∀ k₁ k₂ k₃ xs x {Γ A B e e₁ i}
  → (1 + size-apps xs) < k₁
  → size-counter i < k₂
  → size-type B < k₃
  → Γ , A ⊢d i # (e ▻ (xs ⇈)) · (x ↑ 0) ⦂ B
  → Γ ⊢d ♭ Z # e₁ ⦂ A
  → Γ ⊢d i #  (((ƛ e) · e₁) ▻ xs) · x ⦂ B

subst-3-prj : ∀ k₁ k₂ k₃ xs l {Γ A B e e₁ i}
  → (1 + size-apps xs) < k₁
  → size-counter i < k₂
  → size-type B < k₃
  → Γ , A ⊢d i # (e ▻ (xs ⇈)) 𝕡 l ⦂ B
  → Γ ⊢d ♭ Z # e₁ ⦂ A
  → Γ ⊢d i #  (((ƛ e) · e₁) ▻ xs) 𝕡 l ⦂ B

subst-3 (suc k₁) (suc k₂) (suc k₃) [] sz₁ sz₂ sz₃ ⊢1 ⊢2 = ⊢d-app⇒ (⊢d-lam₂ ⊢1) ⊢2
subst-3 (suc k₁) (suc k₂) (suc k₃) (e ∷a es) {i = i} sz₁ sz₂ sz₃ ⊢1 ⊢2 with (λ x xs eq →
  rw-+++-app (rw-⊢apps-a' {es = xs} (subst-3-app (suc k₁) (suc k₂) (suc k₃) xs x
                                                 (size-apps-+++a sz₁ eq) sz₂ sz₃
                                                   (rw-⊢apps-a {es = xs ⇈} (rw-+++-app' ⊢1 (eq-consa-↑ eq))) ⊢2)) eq)
                                                   | apps-destruct (e ∷a es) (apps-consa>0 {e} {es})
... | rec | des-app x xs eq = rec x xs eq                                                       
... | rec | des-prj l xs eq = {!!}
subst-3 (suc k₁) (suc k₂) (suc k₃) (l ∷l es) sz₁ sz₂ sz₃ ⊢1 ⊢2 with apps-destruct (l ∷l es) (apps-consl>0 {l} {es})
... | des-app x xs eq = {!!}
... | des-prj l' xs eq = {!!}

subst-3-app (suc k₁) (suc k₂) (suc k₃) xs x sz₁ sz₂ sz₃ (⊢d-app⇐ {A = A} {B = B} ⊢1 ⊢3) ⊢2 =
  let ind-e₁ = subst-3 k₁ (suc (suc k₂)) (suc (suc (size-type A) + (size-type B))) xs (≤-pred sz₁) (s≤s sz₂) (s≤s m≤m) ⊢1 ⊢2
  in (⊢d-app⇐ ind-e₁ (⊢d-strengthen-0 ⊢3))
subst-3-app (suc k₁) (suc k₂) (suc k₃) xs x sz₁ sz₂ sz₃ (⊢d-app⇒ {A = A} {B = B} ⊢1 ⊢3) ⊢2 =
  let ind-e₁ = subst-3 k₁ (suc (suc k₂)) (suc (suc (size-type A) + (size-type B))) xs (≤-pred sz₁) (s≤s sz₂) (s≤s m≤m) ⊢1 ⊢2
  in ⊢d-app⇒ ind-e₁ (⊢d-strengthen-0 ⊢3)
subst-3-app (suc k₁) (suc k₂) (suc k₃) xs x {i = ♭ Z} sz₁ sz₂ sz₃ (⊢d-sub ⊢1 A≤B j≢Z) ⊢2 = ⊥-elim (j≢Z refl)
subst-3-app (suc k₁) (suc k₂) (suc k₃) xs x {i = ♭ ∞} sz₁ sz₂ sz₃ (⊢d-sub {B = B} ⊢1 A≤B j≢Z) ⊢2 =
  ⊢d-sub' (subst-3-app (suc k₁) k₂ (suc (size-type B)) xs x sz₁ (<-pred sz₂) (s≤s m≤m) ⊢1 ⊢2) A≤B
subst-3-app (suc k₁) (suc k₂) (suc k₃) xs x {i = ♭ (S⇐ j)} sz₁ sz₂ sz₃ (⊢d-sub {B = B} ⊢1 A≤B j≢Z) ⊢2 =
  ⊢d-sub' (subst-3-app (suc k₁) k₂ (suc (size-type B)) xs x sz₁ (size-ccounter>0 {j = j} (<-pred sz₂)) (s≤s m≤m) ⊢1 ⊢2) A≤B
subst-3-app (suc k₁) (suc k₂) (suc k₃) xs x {i = ♭ (Sl j)} sz₁ sz₂ sz₃ (⊢d-sub {B = B} ⊢1 A≤B j≢Z) ⊢2 =
 ⊢d-sub' (subst-3-app (suc k₁) k₂ (suc (size-type B)) xs x sz₁ (size-ccounter>0 {j = j} (<-pred sz₂)) (s≤s m≤m) ⊢1 ⊢2) A≤B
subst-3-app (suc k₁) (suc k₂) (suc k₃) xs x {i = S⇒ i} sz₁ sz₂ sz₃ (⊢d-sub {B = B} ⊢1 A≤B j≢Z) ⊢2 =
  ⊢d-sub' (subst-3-app (suc k₁) k₂ (suc (size-type B)) xs x sz₁ (size-counter>0 {i = i} (<-pred sz₂)) (s≤s m≤m) ⊢1 ⊢2) A≤B
subst-3-app (suc k₁) (suc k₂) (suc k₃) xs x sz₁ sz₂ sz₃ (⊢d-& {A = A} {B = B} ⊢1 ⊢3) ⊢2 =
  ⊢d-& (subst-3-app (suc k₁) (suc k₂) k₃ xs x sz₁ sz₂ (size-type-+-l {A = A} {B = B} (<-pred sz₃)) ⊢1 ⊢2)
       (subst-3-app (suc k₁) (suc k₂) k₃ xs x sz₁ sz₂ (size-type-+-r {A = A} {B = B} (<-pred sz₃)) ⊢3 ⊢2)

subst-3-prj (suc k₁) (suc k₂) (suc k₃) xs l {i = ♭ Z} sz₁ sz₂ sz₃ (⊢d-sub ⊢1 A≤B i≢Z) ⊢2 = ⊥-elim (i≢Z refl)
subst-3-prj (suc k₁) (suc k₂) (suc k₃) xs l {i = ♭ ∞} sz₁ sz₂ sz₃ (⊢d-sub {B = B} ⊢1 A≤B i≢Z) ⊢2 =
  ⊢d-sub' (subst-3-prj (suc k₁) k₂ (suc (size-type B)) xs l sz₁ (<-pred sz₂) (s≤s m≤m) ⊢1 ⊢2) A≤B
subst-3-prj (suc k₁) (suc k₂) (suc k₃) xs l {i = ♭ (S⇐ j)} sz₁ sz₂ sz₃ (⊢d-sub {B = B} ⊢1 A≤B i≢Z) ⊢2 =
 ⊢d-sub' (subst-3-prj (suc k₁) k₂ (suc (size-type B)) xs l sz₁ (size-ccounter>0 {j = j} (<-pred sz₂)) (s≤s m≤m) ⊢1 ⊢2) A≤B
subst-3-prj (suc k₁) (suc k₂) (suc k₃) xs l {i = ♭ (Sl j)} sz₁ sz₂ sz₃ (⊢d-sub {B = B} ⊢1 A≤B i≢Z) ⊢2 =
 ⊢d-sub' (subst-3-prj (suc k₁) k₂ (suc (size-type B)) xs l sz₁ (size-ccounter>0 {j = j} (<-pred sz₂)) (s≤s m≤m) ⊢1 ⊢2) A≤B
subst-3-prj (suc k₁) (suc k₂) (suc k₃) xs l {i = S⇒ i} sz₁ sz₂ sz₃ (⊢d-sub {B = B} ⊢1 A≤B i≢Z) ⊢2 =
  ⊢d-sub' (subst-3-prj (suc k₁) k₂ (suc (size-type B)) xs l sz₁ (size-counter>0 {i = i} (<-pred sz₂)) (s≤s m≤m) ⊢1 ⊢2) A≤B
subst-3-prj (suc k₁) (suc k₂) (suc k₃) xs l sz₁ sz₂ sz₃ (⊢d-& {A = A} {B = B} ⊢1 ⊢3) ⊢2 =
  ⊢d-& (subst-3-prj (suc k₁) (suc k₂) k₃ xs l sz₁ sz₂ (size-type-+-l {A = A} {B = B} (<-pred sz₃)) ⊢1 ⊢2)
       (subst-3-prj (suc k₁) (suc k₂) k₃ xs l sz₁ sz₂ (size-type-+-r {A = A} {B = B} (<-pred sz₃)) ⊢3 ⊢2)
subst-3-prj (suc k₁) (suc k₂) (suc k₃) xs l sz₁ sz₂ sz₃ (⊢d-prj {l = l} {A = A} ⊢1) ⊢2 =
  let ind-e₁ = subst-3 k₁ (suc (suc k₂)) (suc (suc (size-type A))) xs (≤-pred sz₁) (s≤s sz₂) (s≤s m≤m) ⊢1 ⊢2
  in (⊢d-prj ind-e₁)

subst :  ∀ {Γ A B e e₁ i} (es : Apps)
  → Γ , A ⊢d i # e ▻ up 0 es ⦂ B
  → Γ ⊢d ♭ Z # e₁ ⦂ A
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

ⅉ' : Apps → CCounter
ⅉ' [] = ∞
ⅉ' (_ ∷a as) = S⇐ (ⅉ' as)
ⅉ' (_ ∷l as) = Sl (ⅉ' as)

app-elim : ∀ {Γ e as H A A' As}
  → Γ ⊢d ♭ (ⅉ as) # e ⦂ A
  → ⟦ H , A ⟧→⟦ as , □ , As , A' ⟧
  → Γ ⊩ as ⇚ As
  → Γ ⊢d ♭ Z # e ▻ as ⦂ A'
app-elim ⊢e none-□ ⊩none⇚ = ⊢e
app-elim ⊢e (have-a spl) (⊩cons⇚ ⊢as x) = app-elim (⊢d-app⇐ ⊢e x) spl ⊢as
app-elim ⊢e (have-l spl) (⊩consl ⊢as) = app-elim (⊢d-prj ⊢e) spl ⊢as

app-elim' : ∀ {Γ e as H A A' As T}
  → Γ ⊢d ♭ (ⅉ' as) # e ⦂ A
  → ⟦ H , A ⟧→⟦ as , τ T , As , A' ⟧
  → Γ ⊩ as ⇚ As
  → Γ ⊢d ♭ ∞ # e ▻ as ⦂ A'
app-elim' ⊢e none-τ ⊩none⇚ = ⊢e
app-elim' ⊢e (have-a spl) (⊩cons⇚ ⊢as x) = app-elim' (⊢d-app⇐ ⊢e x) spl ⊢as
app-elim' ⊢e (have-l spl) (⊩consl ⊢as) = app-elim' (⊢d-prj ⊢e) spl ⊢as
  
sound-inf : ∀ {Γ e H A es As A'}
  → Γ ⊢a H ⇛ e ⇛ A
  → ⟦ H , A ⟧→⟦ es , □ , As , A' ⟧
  → Γ ⊢d ♭ Z # e ▻ es ⦂ A'

sound-chk : ∀ {Γ e H A es T As A'}
  → Γ ⊢a H ⇛ e ⇛ A
  → ⟦ H , A ⟧→⟦ es , τ T , As , A' ⟧
  → Γ ⊢d ♭ ∞ # e ▻ es ⦂ T

sound-≤ : ∀ {Γ A H A' A'' es As}
  → Γ ⊢a A ≤ H ⇝ A'
  → ⟦ H , A' ⟧→⟦ es , □ , As , A'' ⟧
  →  A ≤d ♭ (ⅉ es) # A'

sound-≤-chk : ∀ {Γ A H A' A'' es As T}
  → Γ ⊢a A ≤ H ⇝ A'
  → ⟦ H , A' ⟧→⟦ es , τ T , As , A'' ⟧
  →  A ≤d ♭ (ⅉ' es) # A'

sound-es : ∀ {Γ A₁ H A As A' es H'}
  → Γ ⊢a A₁ ≤ H ⇝ A
  → ⟦ H , A ⟧→⟦ es , H' , As , A' ⟧
  → Γ ⊩ es ⇚ As

sound-inf-0 : ∀ {Γ e A}
  → Γ ⊢a □ ⇛ e ⇛ A
  → Γ ⊢d ♭ Z # e ⦂ A
sound-inf-0 ⊢e = sound-inf ⊢e none-□

sound-chk-0 : ∀ {Γ e A}
  → Γ ⊢a τ A ⇛ e ⇛ A
  → Γ ⊢d ♭ ∞ # e ⦂ A
sound-chk-0 ⊢e = sound-chk ⊢e none-τ

sound-r : ∀ {Γ rs A}
  → Γ ⊢r □ ⇛ rs ⇛ A
  → Γ ⊢r ♭ Z # rs ⦂ A
sound-r ⊢a-nil = ⊢r-nil
sound-r (⊢a-one x) = ⊢r-one (sound-inf-0 x)
sound-r (⊢a-cons x ⊢rs) = ⊢r-cons (sound-inf-0 x) (sound-r ⊢rs)

sound-inf ⊢a-lit none-□ = ⊢d-int
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
sound-chk (⊢a-& ⊢e ⊢e₁) none-τ = ⊢d-& (sound-chk ⊢e none-τ) (sound-chk ⊢e₁ none-τ)
sound-chk (⊢a-prj ⊢e) spl = sound-chk ⊢e (have-l spl)

sound-≤ ≤a-□ none-□ = ≤d-Z
sound-≤ (≤a-hint x A≤H) (have-a spl) = ≤d-arr-S⇐ ≤d-refl∞ (sound-≤ A≤H spl)
sound-≤ (≤a-hint-l A≤H) (have-l spl) = ≤d-rcd-Sl (sound-≤ A≤H spl)
sound-≤ (≤a-and-l A≤H x) spl = ≤d-and₁ (sound-≤ A≤H spl) {!!}
sound-≤ (≤a-and-r A≤H x) spl = ≤d-and₂ (sound-≤ A≤H spl) {!!}

sound-≤-chk ≤a-int none-τ = ≤d-int∞
sound-≤-chk ≤a-base none-τ = ≤d-base∞
sound-≤-chk ≤a-top none-τ = ≤d-top
sound-≤-chk (≤a-arr A≤H A≤H₁) none-τ = ≤d-arr-∞ (sound-≤-chk A≤H none-τ) (sound-≤-chk A≤H₁ none-τ)
sound-≤-chk (≤a-rcd A≤H) none-τ = ≤d-rcd∞ (sound-≤-chk A≤H none-τ)
sound-≤-chk (≤a-hint x A≤H) (have-a spl) = ≤d-arr-S⇐ ≤d-refl∞ (sound-≤-chk A≤H spl)
sound-≤-chk (≤a-hint-l A≤H) (have-l spl) = ≤d-rcd-Sl (sound-≤-chk A≤H spl)
sound-≤-chk (≤a-and-l A≤H x) spl = ≤d-and₁ (sound-≤-chk A≤H spl) {!!}
sound-≤-chk (≤a-and-r A≤H x) spl = ≤d-and₂ (sound-≤-chk A≤H spl) {!!}
sound-≤-chk (≤a-and A≤H A≤H₁) none-τ = ≤d-and (sound-≤-chk A≤H none-τ) (sound-≤-chk A≤H₁ none-τ)

sound-es ≤a-int none-τ = ⊩none⇚
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
