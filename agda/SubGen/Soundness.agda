module SubGen.Soundness where

open import SubGen.Prelude
open import SubGen.Common
open import SubGen.Decl
open import SubGen.Decl.Properties
open import SubGen.Algo
open import SubGen.Algo.Properties

infix 5 _⇈
_⇈ : List Term → List Term
_⇈ = map (_↑ 0)

infix 4 _⊩_⇚_
data _⊩_⇚_ : Context → List Term → List Type → Set where
  ⊩none⇚ : ∀ {Γ}
    → Γ ⊩ [] ⇚ []

  ⊩cons⇚ : ∀ {Γ es As e A}
    → Γ ⊩ es ⇚ As
    → Γ ⊢d ♭ ∞ # e ⦂ A
    → Γ ⊩ (e ∷ es) ⇚ (A ∷ As)

build-j-Z : ℕ → Counter
build-j-Z n = ♭ (build-j-Z' n)
  where build-j-Z' : ℕ → CCounter
        build-j-Z' 0 = Z
        build-j-Z' (suc n) = S⇐ (build-j-Z' n)

data build-iZ : List Term → Counter → Set where
  bj-none :
      build-iZ [] (♭ Z)

--  bj-none-∞ :
--    build-iZ [] (♭ ∞)

  bj-cons : ∀ {e es j}
    → build-iZ es (♭ j)
    → build-iZ (e ∷ es) (♭ (S⇐ j))


data build-i∞ : List Term → Counter → Set where
  bj-none∞ :
      build-i∞ [] (♭ ∞)

  bj-cons∞ : ∀ {e es j}
    → build-i∞ es (♭ j)
    → build-i∞ (e ∷ es) (♭ (S⇐ j))


H≢□→j≢Z : ∀ {H A es As A' j}
  → H ≢ □
  → ❪ H , A ❫↣❪ es , □ , As , A' ❫
  → build-iZ es (♭ j)
  → ♭ j ≢ ♭ Z
H≢□→j≢Z {□} H≢□ spl newj = ⊥-elim (H≢□ refl)
H≢□→j≢Z {⟦ x ⟧⇒ H} H≢□ (have spl) (bj-cons newj) = λ ()

bi-↑ : ∀ {es j}
  → build-iZ es (♭ j)
  → build-iZ (es ⇈) (♭ j)
bi-↑ bj-none = bj-none
bi-↑ (bj-cons newi) = bj-cons (bi-↑ newi)

bi-↑∞ : ∀ {es j}
  → build-i∞ es (♭ j)
  → build-i∞ (es ⇈) (♭ j)
bi-↑∞ bj-none∞ = bj-none∞
bi-↑∞ (bj-cons∞ newi) = bj-cons∞ (bi-↑∞ newi)

≤d-j-z : ∀ {A B C j}
  → A ≤d ♭ (S⇐ j) # B ⇒ C
  → ∃[ C' ] (A ≤d ♭ (S⇐ Z) # B ⇒ C') × (C' ≤d (♭ j) # C)
≤d-j-z (≤d-arr-S⇐ {B = B} A≤B A≤B₁) = ⟨ B , ⟨ (≤d-arr-S⇐ A≤B ≤d-Z) , A≤B₁ ⟩ ⟩
≤d-j-z (≤d-and₁ A≤B neq) with ≤d-j-z A≤B
... | ⟨ fst , ⟨ fst₁ , snd ⟩ ⟩ = ⟨ fst , ⟨ ≤d-and₁ fst₁ (λ ()) , snd ⟩ ⟩
≤d-j-z (≤d-and₂ A≤B neq) with ≤d-j-z A≤B
... | ⟨ fst , ⟨ fst₁ , snd ⟩ ⟩ = ⟨ fst , ⟨ ≤d-and₂ fst₁ (λ ()) , snd ⟩ ⟩

≤d-j-∞ : ∀ {A B C j}
  → A ≤d ♭ (S⇐ j) # B ⇒ C
  → ∃[ C' ] (A ≤d ♭ (S⇐ ∞) # B ⇒ C') × (C' ≤d (♭ j) # C)
≤d-j-∞ (≤d-arr-S⇐ {B = B} A≤B A≤B₁) = ⟨ B , ⟨ (≤d-arr-S⇐ A≤B ≤d-refl∞) , A≤B₁ ⟩ ⟩
≤d-j-∞ (≤d-and₁ A≤B neq) with ≤d-j-∞ A≤B
... | ⟨ fst , ⟨ fst₁ , snd ⟩ ⟩ = ⟨ fst , ⟨ ≤d-and₁ fst₁ (λ ()) , snd ⟩ ⟩
≤d-j-∞ (≤d-and₂ A≤B neq) with ≤d-j-∞ A≤B
... | ⟨ fst , ⟨ fst₁ , snd ⟩ ⟩ = ⟨ fst , ⟨ ≤d-and₂ fst₁ (λ ()) , snd ⟩ ⟩

-- after adding restrictin to s-and₁ and s-and₂, we can have a nice inversion lemma
≤d-z-inv : ∀ {A A'}
  → A ≤d ♭ Z # A'
  → A ≡ A'
≤d-z-inv ≤d-Z = refl
≤d-z-inv (≤d-and₁ A≤A' x) = ⊥-elim (x refl)
≤d-z-inv (≤d-and₂ A≤A' x) = ⊥-elim (x refl)

⊩-elim : ∀ {Γ e H A es As A' A'' i T}
  → Γ ⊢d ♭ Z # e ⦂ A
  → Γ ⊩ es ⇚ As
  → build-iZ es i
  → A ≤d i # A'
  → ❪ H , A' ❫↣❪ es , T , As , A'' ❫ 
  → Γ ⊢d ♭ Z # e ▻ es ⦂ A''
⊩-elim ⊢e ⊩none⇚ bj-none A≤A' none-□ rewrite ≤d-z-inv A≤A' = ⊢e
⊩-elim ⊢e ⊩none⇚ bj-none A≤A' none-τ rewrite ≤d-z-inv A≤A' = ⊢e
⊩-elim ⊢e (⊩cons⇚ ⊢es x) (bj-cons bi) A≤A' (have spl) with ≤d-j-z A≤A'
... | ⟨ E , ⟨ fst , snd ⟩ ⟩ = ⊩-elim ((⊢d-app⇐ (⊢d-sub ⊢e fst λ ()) x)) ⊢es bi snd spl

≤d-rebase : ∀ {A B C j}
  → A ≤d ♭ (S⇐ j) # B ⇒ C
  → A ≤d ♭ (S⇐ Z) # B ⇒ C
≤d-rebase (≤d-arr-S⇐ A≤BC A≤BC₁) = ≤d-arr-S⇐ A≤BC {!!}
≤d-rebase (≤d-and₁ A≤BC x) = ≤d-and₁ (≤d-rebase A≤BC) (λ ())
≤d-rebase (≤d-and₂ A≤BC x) = ≤d-and₂ (≤d-rebase A≤BC) (λ ())

⊩-elim∞ : ∀ {Γ e H A es As A' A'' i T}
  → Γ ⊢d ♭ Z # e ⦂ A
  → Γ ⊩ es ⇚ As
  → build-i∞ es i
  → A ≤d i # A'
  → ❪ H , A' ❫↣❪ es , τ T , As , A'' ❫
  → A'' ≤d ♭ ∞ # T
  → Γ ⊢d ♭ ∞ # e ▻ es ⦂ T
⊩-elim∞ ⊢e ⊩none⇚ bj-none∞ A≤A' none-τ A'≤T = ⊢d-sub' ⊢e (≤d-trans A≤A' A'≤T)
⊩-elim∞ ⊢e (⊩cons⇚ ⊢es x) (bj-cons∞ newj) (≤d-arr-S⇐ A≤A' A≤A'') (have spl) A'≤T = ⊩-elim∞ (⊢d-app⇐ (⊢d-sub' ⊢e (≤d-arr-S⇐ ≤d-refl∞ ≤d-Z)) x) ⊢es newj A≤A'' spl A'≤T
⊩-elim∞ ⊢e (⊩cons⇚ ⊢es x) (bj-cons∞ newj) (≤d-and₁ A≤A' x₁) (have spl) A'≤T = ⊩-elim∞ (⊢d-app⇐ (⊢d-sub' ⊢e (≤d-and₁ {!!} (λ ()))) x) ⊢es newj (≤d-refl {!!}) spl A'≤T
⊩-elim∞ ⊢e (⊩cons⇚ ⊢es x) (bj-cons∞ newj) (≤d-and₂ A≤A' x₁) (have spl) A'≤T = {!!}

{-
⊩-elim∞ ⊢d-int ⊩none⇚ bj-none∞ A≤A' none-τ A'≤T = ⊢d-sub' ⊢d-int (≤d-trans A≤A' A'≤T)
⊩-elim∞ (⊢d-var x) ⊢es newi A≤A' spl = {!!}
⊩-elim∞ (⊢d-ann ⊢e) ⊢es newi A≤A' spl = {!!}
⊩-elim∞ (⊢d-app⇐ ⊢e ⊢e₁) ⊢es newi A≤A' spl = {!!}
⊩-elim∞ (⊢d-app⇒ ⊢e ⊢e₁) ⊢es newi A≤A' spl = {!!}
⊩-elim∞ (⊢d-sub ⊢e x x₁) ⊢es newi A≤A' spl = {!!}
-}

-- ⊩-elim ⊢e (⊩cons⇚ ⊢es x) A≤A' (have spl) = ⊩-elim (⊢d-app⇐ (⊢d-sub ⊢e {!!} λ ()) x) ⊢es {!!} spl

size-c : CCounter → ℕ
size-c Z = 0
size-c ∞ = 1
size-c (S⇐ j) = suc (size-c j)

size : Counter → ℕ
size (♭ j) = size-c j
size (S⇒ i) = 1 + size i

size-t : Type → ℕ
size-t Int = 0
size-t (* x) = 0
size-t Top = 0
size-t (A ⇒ B) = 1 + size-t A + size-t B
size-t (A & B) = 1 + size-t A + size-t B

lst-destruct-rev : ∀ (l : List Term)
  → 0 < len l
  → ∃[ x ] (∃[ xs ] (l ≡ (xs ++ x ∷ [])))
lst-destruct-rev (x ∷ []) (s≤s z≤n) = ⟨ x , ⟨ [] , refl ⟩ ⟩
lst-destruct-rev (x ∷ y ∷ l) (s≤s z≤n) with lst-destruct-rev (y ∷ l) (s≤s z≤n)
... | ⟨ x' , ⟨ xs' , eq ⟩ ⟩ rewrite eq = ⟨ x' , ⟨ x ∷ xs' , refl ⟩ ⟩

ees>0 : ∀ {e} {es : List Term}
  → len (e ∷ es) > 0
ees>0 {e} {es} = s≤s z≤n

rw-try' : ∀ {Γ e₁ e₂ es j B xs x}
  → Γ ⊢d j # e₁ ▻ (xs ++ ⟦ x ⟧) ⦂ B
  → (e₂ ∷ es) ≡ (xs ++ ⟦ x ⟧)
  → Γ ⊢d j # (e₁ · e₂) ▻ es ⦂ B
rw-try' ⊢e eq rewrite (sym eq) = ⊢e

rw-try : ∀ {Γ e₁ e₂ es j B xs x}
  → Γ ⊢d j # (e₁ · e₂) ▻ es ⦂ B
  → (e₂ ∷ es) ≡ (xs ++ ⟦ x ⟧)
  → Γ ⊢d j # e₁ ▻ (xs ++ ⟦ x ⟧) ⦂ B
rw-try ⊢e eq rewrite (sym eq) = ⊢e

rw-apps-gen : ∀ (es) {e es'}
  → e ▻ (es ++ es') ≡ (e ▻ es) ▻ es'
rw-apps-gen [] = refl
rw-apps-gen (x ∷ es) = rw-apps-gen es

rw-apps : ∀ {es e x}
  → e ▻ (es ++ ⟦ x ⟧) ≡ (e ▻ es) · x
rw-apps {es} {e} {x} = rw-apps-gen es {e = e} {es' = ⟦ x ⟧}

rw-apps→ : ∀ {Γ j es e x A}
  → Γ ⊢d j # e ▻ (es ++ ⟦ x ⟧) ⦂ A
  → Γ ⊢d j # (e ▻ es) · x ⦂ A
rw-apps→ {es = es} {e = e} {x = x} ⊢e rewrite rw-apps {es} {e} {x} = ⊢e

rw-apps← : ∀ {Γ j es e x A}
  → Γ ⊢d j # (e ▻ es) · x ⦂ A
  → Γ ⊢d j # e ▻ (es ++ ⟦ x ⟧) ⦂ A
rw-apps← {es = es} {e = e} {x = x} ⊢e rewrite rw-apps {es} {e} {x} = ⊢e


eq-cons-↑ : ∀ {e es xs x}
  → e ∷ es ≡ xs ++ ⟦ x ⟧
  → (e ↑ 0) ∷ map (_↑ 0) es ≡ (map (_↑ 0) xs) ++ ⟦ x ↑ 0 ⟧
eq-cons-↑ {xs = xs} {x = x} eq rewrite sym (map-++ (_↑ 0) xs ⟦ x ⟧) = cong (map (_↑ 0)) eq

rw-map : ∀ {Γ e xs x A j}
  → Γ ⊢d j # e ▻ (map (_↑ 0) xs ++ ⟦ x ↑ 0 ⟧) ⦂ A
  → Γ ⊢d j # e ▻ map (_↑ 0) (xs ++ ⟦ x ⟧) ⦂ A
rw-map {xs = xs} {x = x} ⊢e rewrite sym (map-++ (_↑ 0) xs ⟦ x ⟧) = ⊢e

len-append : ∀ {xs} {x : Term}
  → len (xs ++ ⟦ x ⟧) ≡ 1 + len xs
len-append {[]} = refl
len-append {x ∷ xs} = cong suc (len-append {xs})

cons-++-len : ∀ {e : Term} {es xs x}
  → e ∷ es ≡ xs ++ ⟦ x ⟧
  → len es ≡ len xs
cons-++-len {xs = xs} {x = x} eq with cong len eq
... | r rewrite len-append {xs} {x} = suc-injective r

sz-case₁ : ∀ {e : Term} {k₁ es x xs}
  → len (e ∷ es) < suc k₁
  → e ∷ es ≡ xs ++ ⟦ x ⟧
  → len (xs ++ ⟦ x ⟧) < suc k₁
sz-case₁ sz eq rewrite sym eq = sz

m+n<o⇒m<o : ∀ {m n o}
  → m + n < o
  → m < o
m+n<o⇒m<o {n = n} m+n<0 = {!!}

m+n<o⇒n<o : ∀ {m n o}
  → m + n < o
  → n < o
m+n<o⇒n<o {n = n} m+n<o = {!!}

sz-case' : ∀ {e : Term} {es x xs k}
  → suc (suc (len es)) ≤ suc k
  → e ∷ es ≡ xs ++ ⟦ x ⟧
  → suc (len xs) < suc k
sz-case' (s≤s sz) eq rewrite cons-++-len eq = s≤s sz

subst-3m' : ∀ k₁ k₂ k₃ xs x {Γ A B e e₁ i}
  → 1 + len xs < k₁
  → size i < k₂
  → size-t B < k₃
  → Γ , A ⊢d i # (e ▻ (xs ⇈)) · (x ↑ 0) ⦂ B
  → Γ ⊢d ♭ Z # e₁ ⦂ A
  → Γ ⊢d i #  (((ƛ e) · e₁) ▻ xs) · x ⦂ B

size-c>0 : ∀ {k j}
  → size-c j < k
  → 0 < k
size-c>0 {k} {Z} sz = sz
size-c>0 {k} {∞} sz = <-trans (s≤s z≤n) sz
size-c>0 {.(suc _)} {S⇐ j} (s≤s sz) = s≤s z≤n

size>0 : ∀ {k i}
  → size i < k
  → 0 < k
size>0 {suc i} {k} sz = s≤s z≤n

size-t-+-l : ∀ {A B k}
  → size-t A + size-t B < k
  → size-t A < k
size-t-+-l sz = m+n<o⇒m<o sz

size-t-+-r : ∀ {A B k}
  → size-t A + size-t B < k
  → size-t B < k
size-t-+-r sz = m+n<o⇒n<o sz  

subst-3 : ∀ k₁ k₂ k₃ es {Γ A B e e₁ j}
  → len es < k₁
  → size j < k₂
  → size-t B < k₃
  → Γ , A ⊢d j # e ▻ (es ⇈) ⦂ B
  → Γ ⊢d ♭ Z # e₁ ⦂ A
  → Γ ⊢d j # ((ƛ e) · e₁) ▻ es ⦂ B
subst-3 (suc k₁) (suc k₂) (suc k₃) [] sz₁ sz₂ sz₃ ⊢1 ⊢2 = ⊢d-app⇒ (⊢d-lam₂ ⊢1) ⊢2
subst-3 (suc k₁) (suc k₂) (suc k₃) (e ∷ es) {j = j} sz₁ sz₂ sz₃ ⊢1 ⊢2 with (λ x xs eq → (rw-try' (rw-apps← {es = xs} (subst-3m' (suc k₁) (suc k₂) (suc k₃) xs x (sz-case' sz₁ eq) sz₂ sz₃ (rw-apps→ {es = xs ⇈} (rw-try ⊢1 (eq-cons-↑ eq))) ⊢2)) eq)) | lst-destruct-rev (e ∷ es) (ees>0 {e} {es})
... | rec | ⟨ x , ⟨ xs , eq ⟩ ⟩ = rec x xs eq
  
subst-3m' (suc k₁) (suc k₂) (suc k₃) xs x sz₁ sz₂ sz₃ (⊢d-app⇐ {A = A} {B = B} ⊢1 ⊢3) ⊢2 = let ind-e₁ = subst-3 k₁ (suc (suc k₂)) (suc (suc (size-t A) + (size-t B))) xs (≤-pred sz₁) (s≤s sz₂) (s≤s m≤m) ⊢1 ⊢2
                                                                                           in (⊢d-app⇐ ind-e₁ (⊢d-strengthen-0 ⊢3))
subst-3m' (suc k₁) (suc k₂) (suc k₃) xs x sz₁ sz₂ sz₃ (⊢d-app⇒ {A = A} {B = B} ⊢1 ⊢3) ⊢2 = let ind-e₁ = subst-3 k₁ (suc (suc k₂)) (suc (suc (size-t A) + (size-t B))) xs (≤-pred sz₁) (s≤s sz₂) (s≤s m≤m) ⊢1 ⊢2
                                                                                           in ⊢d-app⇒ ind-e₁ (⊢d-strengthen-0 ⊢3)
subst-3m' (suc k₁) (suc k₂) (suc k₃) xs x {i = ♭ Z} sz₁ sz₂ sz₃ (⊢d-sub ⊢1 A≤B j≢Z) ⊢2 = ⊥-elim (j≢Z refl)
subst-3m' (suc k₁) (suc k₂) (suc k₃) xs x {i = ♭ ∞} sz₁ sz₂ sz₃ (⊢d-sub {B = B} ⊢1 A≤B j≢Z) ⊢2 = ⊢d-sub' (subst-3m' (suc k₁) k₂ (suc (size-t B)) xs x sz₁ (<-pred sz₂) (s≤s m≤m) ⊢1 ⊢2) A≤B
subst-3m' (suc k₁) (suc k₂) (suc k₃) xs x {i = ♭ (S⇐ j)} sz₁ sz₂ sz₃ (⊢d-sub {B = B} ⊢1 A≤B j≢Z) ⊢2 = ⊢d-sub' (subst-3m' (suc k₁) k₂ (suc (size-t B)) xs x sz₁ (size-c>0 (<-pred sz₂)) (s≤s m≤m) ⊢1 ⊢2) A≤B
subst-3m' (suc k₁) (suc k₂) (suc k₃) xs x {i = S⇒ i} sz₁ sz₂ sz₃ (⊢d-sub {B = B} ⊢1 A≤B j≢Z) ⊢2 = ⊢d-sub' (subst-3m' (suc k₁) k₂ (suc (size-t B)) xs x sz₁ (size>0 {i = i} (<-pred sz₂)) (s≤s m≤m) ⊢1 ⊢2) A≤B
subst-3m' (suc k₁) (suc k₂) (suc k₃) xs x sz₁ sz₂ sz₃ (⊢d-& {A = A} {B = B} ⊢1 ⊢3) ⊢2 = ⊢d-& (subst-3m' (suc k₁) (suc k₂) k₃ xs x sz₁ sz₂ (size-t-+-l {A = A} {B = B} (<-pred sz₃)) ⊢1 ⊢2)
                                                                                             (subst-3m' (suc k₁) (suc k₂) k₃ xs x sz₁ sz₂ (size-t-+-r {A = A} {B = B} (<-pred sz₃)) ⊢3 ⊢2)

  
subst :  ∀ {Γ A B e e₁ i} (es : List Term)
  → Γ , A ⊢d i # e ▻ map (_↑ 0) es ⦂ B
  → Γ ⊢d ♭ Z # e₁ ⦂ A
  → Γ ⊢d i # ((ƛ e) · e₁) ▻ es ⦂ B
subst {B = B} {i = i} es ⊢1 ⊢2 = subst-3 (suc (len es)) (suc (size i)) (suc (size-t B)) es (s≤s m≤m) (s≤s m≤m) (s≤s m≤m) ⊢1 ⊢2


----------------------------------------------------------------------
--+                                                                +--
--+                           Soundness                            +--
--+                                                                +--
----------------------------------------------------------------------


sound-inf : ∀ {Γ e H A es As A' j}
  → Γ ⊢a H ⇛ e ⇛ A
  → ❪ H , A ❫↣❪ es , □ , As , A' ❫
  → build-iZ es (♭ j)
  → Γ ⊢d ♭ Z # e ▻ es ⦂ A'

sound-chk : ∀ {Γ e H A es T As A' j}
  → Γ ⊢a H ⇛ e ⇛ A
  → ❪ H , A ❫↣❪ es , τ T , As , A' ❫
  → build-i∞ es (♭ j)
  → Γ ⊢d ♭ ∞ # e ▻ es ⦂ T

sound-inf-0 : ∀ {Γ e A}
  → Γ ⊢a □ ⇛ e ⇛ A
  → Γ ⊢d ♭ Z # e ⦂ A
sound-inf-0 ⊢e = sound-inf ⊢e none-□ bj-none

sound-chk-0 : ∀ {Γ e A}
  → Γ ⊢a τ A ⇛ e ⇛ A
  → Γ ⊢d ♭ ∞ # e ⦂ A
sound-chk-0 ⊢e = sound-chk ⊢e none-τ bj-none∞
sound-≤-es : ∀ {Γ A H A' A₁ As es}
  → Γ ⊢a A ≤ H ⇝ A₁
  → ❪ H , A₁ ❫↣❪ es , □ , As , A' ❫
  → Γ ⊩ es ⇚ As

sound-≤ : ∀ {Γ A H A' A₁ As es j}
  → Γ ⊢a A ≤ H ⇝ A₁
  → ❪ H , A₁ ❫↣❪ es , □ , As , A' ❫
  → build-iZ es (♭ j)
  → A ≤d ♭ j # A₁

sound-≤-spl : ∀ {Γ A₁ H A es T As A'}
  → Γ ⊢a A₁ ≤ H ⇝ A
  → ❪ H , A ❫↣❪ es , τ T , As , A' ❫
  → A' ≤d ♭ ∞ # T

sound-≤-spl ≤a-int none-τ = ≤d-int∞
sound-≤-spl ≤a-base none-τ = ≤d-base∞
sound-≤-spl ≤a-top none-τ = ≤d-top
sound-≤-spl (≤a-arr A≤H A≤H₁) none-τ = ≤d-arr-∞ ≤d-refl∞ ≤d-refl∞
sound-≤-spl (≤a-hint x A≤H) (have spl) = sound-≤-spl A≤H spl
sound-≤-spl (≤a-and-l A≤H x) spl = sound-≤-spl A≤H spl
sound-≤-spl (≤a-and-r A≤H x) spl = sound-≤-spl A≤H spl
sound-≤-spl (≤a-and A≤H A≤H₁) none-τ = ≤d-and (≤d-and₁ (sound-≤-spl A≤H none-τ) (λ ()))
                                              (≤d-and₂ (sound-≤-spl A≤H₁ none-τ) (λ ()))

sound-≤-es-chk : ∀ {Γ A H A' A₁ As es T}
  → Γ ⊢a A ≤ H ⇝ A₁
  → ❪ H , A₁ ❫↣❪ es , τ T , As , A' ❫
  → Γ ⊩ es ⇚ As

sound-≤-chk : ∀ {Γ A H A' A₁ As es j T}
  → Γ ⊢a A ≤ H ⇝ A₁
  → ❪ H , A₁ ❫↣❪ es , τ T , As , A' ❫
  → build-i∞ es (♭ j)
  → A ≤d ♭ j # A₁

sound-≤-es-chk ≤a-int none-τ = ⊩none⇚
sound-≤-es-chk ≤a-base none-τ = ⊩none⇚
sound-≤-es-chk ≤a-top none-τ = ⊩none⇚
sound-≤-es-chk (≤a-arr A≤H A≤H₁) none-τ = ⊩none⇚
sound-≤-es-chk (≤a-hint x A≤H) (have spl) = ⊩cons⇚ (sound-≤-es-chk A≤H spl) (sound-chk-0 x)
sound-≤-es-chk (≤a-and-l A≤H x) spl = sound-≤-es-chk A≤H spl
sound-≤-es-chk (≤a-and-r A≤H x) spl = sound-≤-es-chk A≤H spl
sound-≤-es-chk (≤a-and A≤H A≤H₁) none-τ = ⊩none⇚

sound-≤-chk ≤a-int none-τ bj-none∞ = ≤d-int∞
sound-≤-chk ≤a-base none-τ bj-none∞ = ≤d-base∞
sound-≤-chk ≤a-top none-τ bj-none∞ = ≤d-top
sound-≤-chk (≤a-arr A≤H A≤H₁) none-τ bj-none∞ = ≤d-arr-∞ (sound-≤-chk A≤H none-τ bj-none∞) (sound-≤-chk A≤H₁ none-τ bj-none∞)
sound-≤-chk (≤a-hint x A≤H) (have spl) (bj-cons∞ bj) = ≤d-arr-S⇐ ≤d-refl∞ (sound-≤-chk A≤H spl bj)
sound-≤-chk (≤a-and-l A≤H x) spl bj = ≤d-and₁ (sound-≤-chk A≤H spl bj) {!!} -- correct
sound-≤-chk (≤a-and-r A≤H x) spl bj = {!!} -- correct
sound-≤-chk (≤a-and A≤H A≤H₁) none-τ bj-none∞ = ≤d-and (sound-≤-chk A≤H none-τ bj-none∞)
                                                       (sound-≤-chk A≤H₁ none-τ bj-none∞)

sound-≤-es ≤a-□ none-□ = ⊩none⇚
sound-≤-es (≤a-hint ⊢e A≤H) (have spl) = ⊩cons⇚ (sound-≤-es A≤H spl) (sound-chk-0 ⊢e)
sound-≤-es (≤a-and-l A≤H H≢□) spl = sound-≤-es A≤H spl
sound-≤-es (≤a-and-r A≤H H≢□) spl = sound-≤-es A≤H spl
sound-≤ ≤a-□ none-□ bj-none = ≤d-refl wf-0
sound-≤ (≤a-hint x A≤H) (have spl) (bj-cons bi) = ≤d-arr-S⇐ ≤d-refl∞ (sound-≤ A≤H spl bi)
sound-≤ (≤a-and-l A≤H H≢□) spl bi = ≤d-and₁ (sound-≤ A≤H spl bi) (H≢□→j≢Z H≢□ spl bi)
sound-≤ (≤a-and-r A≤H H≢□) spl bi = ≤d-and₂ (sound-≤ A≤H spl bi) (H≢□→j≢Z H≢□ spl bi)

sound-inf ⊢a-lit none-□ bi = ⊢d-int
sound-inf (⊢a-var x) none-□ bi = ⊢d-var x
sound-inf (⊢a-ann ⊢e) none-□ bi = ⊢d-ann (sound-chk-0 ⊢e)
sound-inf (⊢a-app ⊢e) spl bi = sound-inf ⊢e (have spl) (bj-cons bi)
sound-inf {es = e ∷ es} (⊢a-lam₂ ⊢e ⊢f) (have spl) (bj-cons bi) = subst es (sound-inf ⊢f (spl-weaken spl) (bi-↑ bi)) (sound-inf-0 ⊢e)
sound-inf (⊢a-sub pv-e ⊢e A≤H) spl bi = ⊩-elim (sound-inf-0 ⊢e) (sound-≤-es A≤H spl) bi (sound-≤ A≤H spl bi) spl

sound-chk (⊢a-app ⊢e) spl bi = sound-chk ⊢e (have spl) (bj-cons∞ bi)
sound-chk (⊢a-lam₁ ⊢e) none-τ bi = ⊢d-lam₁ (sound-chk-0 ⊢e)
sound-chk {es = e ∷ es} (⊢a-lam₂ ⊢e ⊢f) (have spl) (bj-cons∞ bi) = subst es (sound-chk ⊢f (spl-weaken spl) (bi-↑∞ bi)) (sound-inf-0 ⊢e)
sound-chk (⊢a-sub pv-e ⊢e A≤H) spl bi = {!!}
-- ⊩-elim∞ (sound-inf-0 ⊢e) (sound-≤-es-chk A≤H spl) bi (sound-≤-chk A≤H spl bi) spl
-- ⊢d-sub (⊩-elim∞ (sound-inf-0 ⊢e) (sound-≤-es-chk A≤H spl) bi (sound-≤-chk A≤H spl bi) spl) (sound-≤-spl A≤H spl) λ ()
sound-chk (⊢a-& ⊢e ⊢e₁) none-τ bi = ⊢d-& (sound-chk-0 ⊢e) (sound-chk-0 ⊢e₁)
