module Record.Soundness where

open import Record.Prelude
open import Record.Common
open import Record.Decl
open import Record.Decl.Properties renaming (⊢strengthen-0 to ⊢d-strengthen-0)
open import Record.Algo
open import Record.Algo.Properties renaming (⊢strengthen-0 to ⊢a-strengthen-0)

infix 5 _⇈
_⇈ : Apps → Apps
_⇈ = up 0

infix 4 _⊩_⇚_
data _⊩_⇚_ : Env → Apps → AppsType → Set where
  ⊩none⇚ : ∀ {Γ}
    → Γ ⊩ [] ⇚ []

  ⊩cons⇚ : ∀ {Γ es As e A}
    → Γ ⊩ es ⇚ As
    → Γ ⊢ ♭ ∞ # e ⦂ A
    → Γ ⊩ (e ∷a es) ⇚ (A ∷a As)

  ⊩consl : ∀ {Γ es As l}
    → Γ ⊩ es ⇚ As
    → Γ ⊩ (l ∷l es) ⇚ (l ∷l As)


-- after adding restrictin to s-and₁ and s-and₂, we can have a nice inversion lemma
≤z-inv : ∀ {A A'}
  → A ≤ ♭ Z # A'
  → A ≡ A'
≤z-inv ≤Z = refl
≤z-inv (≤and₁ A≤A' x) = ⊥-elim (x refl)
≤z-inv (≤and₂ A≤A' x) = ⊥-elim (x refl)

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
size-type Float = 0
size-type Top = 0
size-type (A `→ B) = 1 + size-type A + size-type B
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
  → Γ , A ⊢ i # e ▻ up 0 es ⦂ B
  → Γ ⊢ ♭ Z # e₁ ⦂ A
  → Γ ⊢ i # ((ƛ e) · e₁) ▻ es ⦂ B
subst-case-0 {es = es} sz ⊢1 ⊢2 rewrite ¬<0→nil {es = es} sz = ⊢app⇒ (⊢lam₂ ⊢1) ⊢2  

subst-3 : ∀ k₁ k₂ k₃ es {Γ A B e e₁ i}
  → size-apps es < k₁
  → size-counter i < k₂
  → size-type B < k₃
  → Γ , A ⊢ i # e ▻ up 0 es ⦂ B
  → Γ ⊢ ♭ Z # e₁ ⦂ A
  → Γ ⊢ i # ((ƛ e) · e₁) ▻ es ⦂ B
  
subst-3-app : ∀ k₁ k₂ k₃ xs x {Γ A B e e₁ i}
  → (1 + size-apps xs) < k₁
  → size-counter i < k₂
  → size-type B < k₃
  → Γ , A ⊢ i # (e ▻ (xs ⇈)) · (x ↑ 0) ⦂ B
  → Γ ⊢ ♭ Z # e₁ ⦂ A
  → Γ ⊢ i #  (((ƛ e) · e₁) ▻ xs) · x ⦂ B

subst-3-prj : ∀ k₁ k₂ k₃ xs l {Γ A B e e₁ i}
  → (1 + size-apps xs) < k₁
  → size-counter i < k₂
  → size-type B < k₃
  → Γ , A ⊢ i # (e ▻ (xs ⇈)) 𝕡 l ⦂ B
  → Γ ⊢ ♭ Z # e₁ ⦂ A
  → Γ ⊢ i #  (((ƛ e) · e₁) ▻ xs) 𝕡 l ⦂ B

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

subst-3-app (suc k₁) (suc k₂) (suc k₃) xs x sz₁ sz₂ sz₃ (⊢app⇐ {A = A} {B = B} ⊢1 ⊢3) ⊢2 =
  let ind-e₁ = subst-3 k₁ (suc (suc k₂)) (suc (suc (size-type A) + (size-type B))) xs (≤-pred sz₁) (s≤s sz₂) (s≤s m≤m) ⊢1 ⊢2
  in (⊢app⇐ ind-e₁ (⊢d-strengthen-0 ⊢3))
subst-3-app (suc k₁) (suc k₂) (suc k₃) xs x sz₁ sz₂ sz₃ (⊢app⇒ {A = A} {B = B} ⊢1 ⊢3) ⊢2 =
  let ind-e₁ = subst-3 k₁ (suc (suc k₂)) (suc (suc (size-type A) + (size-type B))) xs (≤-pred sz₁) (s≤s sz₂) (s≤s m≤m) ⊢1 ⊢2
  in ⊢app⇒ ind-e₁ (⊢d-strengthen-0 ⊢3)
subst-3-app (suc k₁) (suc k₂) (suc k₃) xs x {i = ♭ Z} sz₁ sz₂ sz₃ (⊢sub ⊢1 A≤B j≢Z) ⊢2 = ⊥-elim (j≢Z refl)
subst-3-app (suc k₁) (suc k₂) (suc k₃) xs x {i = ♭ ∞} sz₁ sz₂ sz₃ (⊢sub {B = B} ⊢1 A≤B j≢Z) ⊢2 =
  ⊢sub' (subst-3-app (suc k₁) k₂ (suc (size-type B)) xs x sz₁ (<-pred sz₂) (s≤s m≤m) ⊢1 ⊢2) A≤B
subst-3-app (suc k₁) (suc k₂) (suc k₃) xs x {i = ♭ (S⇐ j)} sz₁ sz₂ sz₃ (⊢sub {B = B} ⊢1 A≤B j≢Z) ⊢2 =
  ⊢sub' (subst-3-app (suc k₁) k₂ (suc (size-type B)) xs x sz₁ (size-ccounter>0 {j = j} (<-pred sz₂)) (s≤s m≤m) ⊢1 ⊢2) A≤B
subst-3-app (suc k₁) (suc k₂) (suc k₃) xs x {i = ♭ (Sl j)} sz₁ sz₂ sz₃ (⊢sub {B = B} ⊢1 A≤B j≢Z) ⊢2 =
 ⊢sub' (subst-3-app (suc k₁) k₂ (suc (size-type B)) xs x sz₁ (size-ccounter>0 {j = j} (<-pred sz₂)) (s≤s m≤m) ⊢1 ⊢2) A≤B
subst-3-app (suc k₁) (suc k₂) (suc k₃) xs x {i = S⇒ i} sz₁ sz₂ sz₃ (⊢sub {B = B} ⊢1 A≤B j≢Z) ⊢2 =
  ⊢sub' (subst-3-app (suc k₁) k₂ (suc (size-type B)) xs x sz₁ (size-counter>0 {i = i} (<-pred sz₂)) (s≤s m≤m) ⊢1 ⊢2) A≤B

subst-3-prj (suc k₁) (suc k₂) (suc k₃) xs l {i = ♭ Z} sz₁ sz₂ sz₃ (⊢sub ⊢1 A≤B i≢Z) ⊢2 = ⊥-elim (i≢Z refl)
subst-3-prj (suc k₁) (suc k₂) (suc k₃) xs l {i = ♭ ∞} sz₁ sz₂ sz₃ (⊢sub {B = B} ⊢1 A≤B i≢Z) ⊢2 =
  ⊢sub' (subst-3-prj (suc k₁) k₂ (suc (size-type B)) xs l sz₁ (<-pred sz₂) (s≤s m≤m) ⊢1 ⊢2) A≤B
subst-3-prj (suc k₁) (suc k₂) (suc k₃) xs l {i = ♭ (S⇐ j)} sz₁ sz₂ sz₃ (⊢sub {B = B} ⊢1 A≤B i≢Z) ⊢2 =
 ⊢sub' (subst-3-prj (suc k₁) k₂ (suc (size-type B)) xs l sz₁ (size-ccounter>0 {j = j} (<-pred sz₂)) (s≤s m≤m) ⊢1 ⊢2) A≤B
subst-3-prj (suc k₁) (suc k₂) (suc k₃) xs l {i = ♭ (Sl j)} sz₁ sz₂ sz₃ (⊢sub {B = B} ⊢1 A≤B i≢Z) ⊢2 =
 ⊢sub' (subst-3-prj (suc k₁) k₂ (suc (size-type B)) xs l sz₁ (size-ccounter>0 {j = j} (<-pred sz₂)) (s≤s m≤m) ⊢1 ⊢2) A≤B
subst-3-prj (suc k₁) (suc k₂) (suc k₃) xs l {i = S⇒ i} sz₁ sz₂ sz₃ (⊢sub {B = B} ⊢1 A≤B i≢Z) ⊢2 =
  ⊢sub' (subst-3-prj (suc k₁) k₂ (suc (size-type B)) xs l sz₁ (size-counter>0 {i = i} (<-pred sz₂)) (s≤s m≤m) ⊢1 ⊢2) A≤B
subst-3-prj (suc k₁) (suc k₂) (suc k₃) xs l sz₁ sz₂ sz₃ (⊢prj {l = l} {A = A} ⊢1) ⊢2 =
  let ind-e₁ = subst-3 k₁ (suc (suc k₂)) (suc (suc (size-type A))) xs (≤-pred sz₁) (s≤s sz₂) (s≤s m≤m) ⊢1 ⊢2
  in (⊢prj ind-e₁)

subst :  ∀ {Γ A B e e₁ i} (es : Apps)
  → Γ , A ⊢ i # e ▻ up 0 es ⦂ B
  → Γ ⊢ ♭ Z # e₁ ⦂ A
  → Γ ⊢ i # ((ƛ e) · e₁) ▻ es ⦂ B
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

Σ≢□→j≢Z : ∀ {Σ A' es As A''}
  → Σ ≢ □
  → ⟦ Σ , A' ⟧→⟦ es , □ , As , A'' ⟧
  → ♭ (ⅉ es) ≢ ♭ Z
Σ≢□→j≢Z {Σ = □} Σ≢□ spl = ⊥-elim (Σ≢□ refl)
Σ≢□→j≢Z {Σ = ⟦ x ⟧⇒ Σ} Σ≢□ (have-a spl) = λ ()
Σ≢□→j≢Z {Σ = ⌊ x ⌋⇒ Σ} Σ≢□ (have-l spl) = λ ()

Σ≢□→j≢Z' : ∀ {Σ A' es As A'' T}
  → Σ ≢ □
  → ⟦ Σ , A' ⟧→⟦ es , τ T , As , A'' ⟧
  → ♭ (ⅉ' es) ≢ ♭ Z
Σ≢□→j≢Z' {Σ = τ x} Σ≢□ none-τ = λ ()
Σ≢□→j≢Z' {Σ = ⟦ x ⟧⇒ Σ} Σ≢□ (have-a spl) = λ ()
Σ≢□→j≢Z' {Σ = ⌊ x ⌋⇒ Σ} Σ≢□ (have-l spl) = λ ()

app-elim : ∀ {Γ e as Σ A A' As}
  → Γ ⊢ ♭ (ⅉ as) # e ⦂ A
  → ⟦ Σ , A ⟧→⟦ as , □ , As , A' ⟧
  → Γ ⊩ as ⇚ As
  → Γ ⊢ ♭ Z # e ▻ as ⦂ A'
app-elim ⊢e none-□ ⊩none⇚ = ⊢e
app-elim ⊢e (have-a spl) (⊩cons⇚ ⊢s x) = app-elim (⊢app⇐ ⊢e x) spl ⊢s
app-elim ⊢e (have-l spl) (⊩consl ⊢s) = app-elim (⊢prj ⊢e) spl ⊢s

app-elim' : ∀ {Γ e as Σ A A' As T}
  → Γ ⊢ ♭ (ⅉ' as) # e ⦂ A
  → ⟦ Σ , A ⟧→⟦ as , τ T , As , A' ⟧
  → Γ ⊩ as ⇚ As
  → Γ ⊢ ♭ ∞ # e ▻ as ⦂ A'
app-elim' ⊢e none-τ ⊩none⇚ = ⊢e
app-elim' ⊢e (have-a spl) (⊩cons⇚ ⊢s x) = app-elim' (⊢app⇐ ⊢e x) spl ⊢s
app-elim' ⊢e (have-l spl) (⊩consl ⊢s) = app-elim' (⊢prj ⊢e) spl ⊢s
  
sound-inf : ∀ {Γ e Σ A es As A'}
  → Γ ⊢ Σ ⇒ e ⇒ A
  → ⟦ Σ , A ⟧→⟦ es , □ , As , A' ⟧
  → Γ ⊢ ♭ Z # e ▻ es ⦂ A'

sound-chk : ∀ {Γ e Σ A es T As A'}
  → Γ ⊢ Σ ⇒ e ⇒ A
  → ⟦ Σ , A ⟧→⟦ es , τ T , As , A' ⟧
  → Γ ⊢ ♭ ∞ # e ▻ es ⦂ T

sound-≤ : ∀ {Γ A Σ A' A'' es As}
  → Γ ⊢ A ≤ Σ ⇝ A'
  → ⟦ Σ , A' ⟧→⟦ es , □ , As , A'' ⟧
  →  A ≤ ♭ (ⅉ es) # A'

sound-≤chk : ∀ {Γ A Σ A' A'' es As T}
  → Γ ⊢ A ≤ Σ ⇝ A'
  → ⟦ Σ , A' ⟧→⟦ es , τ T , As , A'' ⟧
  →  A ≤ ♭ (ⅉ' es) # A'

sound-es : ∀ {Γ A₁ Σ A As A' es Σ'}
  → Γ ⊢ A₁ ≤ Σ ⇝ A
  → ⟦ Σ , A ⟧→⟦ es , Σ' , As , A' ⟧
  → Γ ⊩ es ⇚ As

-- two corollaries
sound-inf-0 : ∀ {Γ e A}
  → Γ ⊢ □ ⇒ e ⇒ A
  → Γ ⊢ ♭ Z # e ⦂ A
sound-inf-0 ⊢e = sound-inf ⊢e none-□

sound-chk-0 : ∀ {Γ e A B}
  → Γ ⊢ τ A ⇒ e ⇒ B
  → Γ ⊢ ♭ ∞ # e ⦂ A
sound-chk-0 ⊢e = sound-chk ⊢e none-τ

sound-r : ∀ {Γ rs A}
  → Γ ⊢r □ ⇒ rs ⇒ A
  → Γ ⊢r ♭ Z # rs ⦂ A
sound-r ⊢nil = ⊢r-nil
sound-r (⊢one x) = ⊢r-one (sound-inf-0 x)
sound-r (⊢cons x ⊢rs neq) = ⊢r-cons (sound-inf-0 x) (sound-r ⊢rs) neq

sound-inf ⊢c none-□ = ⊢c
sound-inf (⊢var x) none-□ = ⊢var x
sound-inf (⊢ann ⊢e) none-□ = ⊢ann (sound-chk-0 ⊢e)
sound-inf (⊢app ⊢e) spl = sound-inf ⊢e (have-a spl)
sound-inf {es = e ∷a es} (⊢lam₂ ⊢e ⊢e₁) (have-a spl) = subst es (sound-inf ⊢e₁ (spl-weaken spl)) (sound-inf-0 ⊢e)
sound-inf (⊢sub x ⊢e x₁ Σ≢□) spl = app-elim (⊢sub' (sound-inf-0 ⊢e) (sound-≤ x₁ spl)) spl (sound-es x₁ spl)
sound-inf (⊢rcd x) none-□ = ⊢rcd (sound-r x)
sound-inf (⊢prj ⊢e) spl = sound-inf ⊢e (have-l spl)

sound-chk (⊢app ⊢e) spl = sound-chk ⊢e (have-a spl)
sound-chk (⊢lam₁ ⊢e) none-τ = ⊢lam₁ (sound-chk ⊢e none-τ)
sound-chk {es = e ∷a es} (⊢lam₂ ⊢e ⊢e₁) (have-a spl) = subst es (sound-chk ⊢e₁ (spl-weaken spl)) (sound-inf-0 ⊢e)
sound-chk ⊢e'@(⊢sub pv-e ⊢e A≤Σ Σ≢□) spl rewrite ⊢spl-τ ⊢e' spl = app-elim' (⊢sub' (sound-inf-0 ⊢e) (sound-≤chk A≤Σ spl)) spl (sound-es A≤Σ spl)
sound-chk (⊢prj ⊢e) spl = sound-chk ⊢e (have-l spl)

sound-≤ ≤□ none-□ = ≤Z
sound-≤ (≤hint x A≤Σ) (have-a spl) = ≤arr-S⇐ ≤refl∞ (sound-≤ A≤Σ spl)
sound-≤ (≤hint-l A≤Σ) (have-l spl) = ≤rcd-Sl (sound-≤ A≤Σ spl)
sound-≤ (≤and-l A≤Σ x) spl = ≤and₁ (sound-≤ A≤Σ spl) (Σ≢□→j≢Z x spl)
sound-≤ (≤and-r A≤Σ x) spl = ≤and₂ (sound-≤ A≤Σ spl) (Σ≢□→j≢Z x spl)

sound-≤chk ≤int none-τ = ≤int∞
sound-≤chk ≤float none-τ = ≤float∞
sound-≤chk ≤top none-τ = ≤top
sound-≤chk (≤arr A≤Σ A≤Σ₁) none-τ rewrite sym (≤id-0 A≤Σ) | sym (≤id-0 A≤Σ₁) = ≤arr-∞ (sound-≤chk A≤Σ none-τ) (sound-≤chk A≤Σ₁ none-τ)
sound-≤chk (≤rcd A≤Σ) none-τ = ≤rcd∞ (sound-≤chk A≤Σ none-τ)
sound-≤chk (≤hint x A≤Σ) (have-a spl) = ≤arr-S⇐ ≤refl∞ (sound-≤chk A≤Σ spl)
sound-≤chk (≤hint-l A≤Σ) (have-l spl) = ≤rcd-Sl (sound-≤chk A≤Σ spl)
sound-≤chk (≤and-l A≤Σ x) spl = ≤and₁ (sound-≤chk A≤Σ spl) (Σ≢□→j≢Z' x spl)
sound-≤chk (≤and-r A≤Σ x) spl = ≤and₂ (sound-≤chk A≤Σ spl) (Σ≢□→j≢Z' x spl)
sound-≤chk (≤and A≤Σ A≤Σ₁) none-τ = ≤and (sound-≤chk A≤Σ none-τ) (sound-≤chk A≤Σ₁ none-τ)

sound-es ≤int none-τ = ⊩none⇚
sound-es ≤float none-τ = ⊩none⇚
sound-es ≤top none-τ = ⊩none⇚
sound-es ≤□ none-□ = ⊩none⇚
sound-es (≤arr A≤Σ A≤Σ₁) none-τ = ⊩none⇚
sound-es (≤rcd A≤Σ) none-τ = ⊩none⇚
sound-es (≤hint x A≤Σ) (have-a spl) = ⊩cons⇚ (sound-es A≤Σ spl) (sound-chk-0 x)
sound-es (≤hint-l A≤Σ) (have-l spl) = ⊩consl (sound-es A≤Σ spl)
sound-es (≤and-l A≤Σ x) spl = sound-es A≤Σ spl
sound-es (≤and-r A≤Σ x) spl = sound-es A≤Σ spl
sound-es (≤and A≤Σ A≤Σ₁) none-τ = ⊩none⇚
