module SubGen.Soundness where

open import SubGen.Prelude
open import SubGen.Common
open import SubGen.Decl
open import SubGen.Decl.Properties
open import SubGen.Algo
open import SubGen.Algo.Properties

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

  bj-cons : ∀ {e es j}
    → build-iZ es (♭ j)
    → build-iZ (e ∷ es) (♭ (S⇐ j))
  
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

infix 5 _⇈
_⇈ : List Term → List Term
_⇈ = map (_↑ 0)

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
m+n<o⇒m<o {n = n} m+n<o = {!!}

m+n<o⇒n<o : ∀ {m n o}
  → m + n < o
  → n < o
m+n<o⇒n<o {n = n} m+n<o = {!!}

sz-case₂ : ∀ {A B k₃}
  → suc (size-t A + size-t B) < suc k₃
  → size-t A < k₃
sz-case₂ {A = A} (s≤s sz) = m+n≤o⇒m≤o (suc (size-t A)) sz

sz-case₃ : ∀ {A B k₃}
  → suc (size-t A + size-t B) < suc k₃
  → size-t B < k₃
sz-case₃ {A = A} {B = B} (s≤s sz) = m+n≤o⇒n≤o {!!} {!!}

sz-case₄ : ∀ {j k₂}
  → j ≡ ♭ ∞
  → size j < suc k₂
  → 0 < k₂
sz-case₄ j≡∞ j<1+k₂ rewrite j≡∞ = <-pred j<1+k₂

subst-3m' : ∀ k₁ k₂ k₃ xs x {Γ A B e e₁ i}
  → 1 + len xs < k₁
  → size i < k₂
  → size-t B < k₃
  → Γ , A ⊢d i # (e₁ ▻ (xs ⇈)) · (x ↑ 0) ⦂ B
  → Γ ⊢d ♭ Z # e₁ ⦂ A
  → Γ ⊢d i #  (((ƛ e) · e₁) ▻ xs) · x ⦂ B

subst-3 : ∀ k₁ k₂ k₃ es {Γ A B e e₁ j}
  → len es < k₁
  → size j < k₂
  → size-t B < k₃
  → Γ , A ⊢d j # e ▻ (es ⇈) ⦂ B
  → Γ ⊢d ♭ Z # e₁ ⦂ A
  → Γ ⊢d j # ((ƛ e) · e₁) ▻ es ⦂ B
subst-3 (suc k₁) (suc k₂) (suc k₃) [] sz₁ sz₂ sz₃ ⊢1 ⊢2 = ⊢d-app⇒ (⊢d-lam₂ ⊢1) ⊢2
subst-3 (suc k₁) (suc k₂) (suc k₃) (e ∷ es) {j = j} sz₁ sz₂ sz₃ ⊢1 ⊢2 =
  case lst-destruct-rev (e ∷ es) (ees>0 {e} {es}) of λ where
    ⟨ x , ⟨ xs , eq ⟩ ⟩ → rw-try' (rw-apps← {es = xs} (subst-3m' (suc k₁) (suc k₂) (suc k₃) xs x {!!} {!!} {!!} {!!} ⊢2)) eq
  
subst-3m' (suc k₁) (suc k₂) (suc k₃) xs x sz₁ sz₂ sz₃ (⊢d-app⇐ ⊢1 ⊢3) ⊢2 = let ind-e₁ = subst-3 k₁ {!!} {!!} {!!} {!!} {!!} {!!} ⊢1 ⊢2
                                                                           in ⊢d-app⇐ ind-e₁ (⊢d-strengthen-0 ⊢3)
subst-3m' (suc k₁) (suc k₂) (suc k₃) xs x sz₁ sz₂ sz₃ (⊢d-app⇒ ⊢1 ⊢3) ⊢2 = let ind-e₁ = subst-3 k₁ {!!} {!!} {!!} {!!} {!!} {!!} ⊢1 ⊢2
                                                                           in ⊢d-app⇒ ind-e₁ (⊢d-strengthen-0 ⊢3)
subst-3m' (suc k₁) (suc k₂) (suc k₃) xs x {i = ♭ Z} sz₁ sz₂ sz₃ (⊢d-sub ⊢1 A≤B j≢Z) ⊢2 = ⊥-elim (j≢Z refl)
subst-3m' (suc k₁) (suc k₂) (suc k₃) xs x {i = ♭ ∞} sz₁ sz₂ sz₃ (⊢d-sub {B = B} ⊢1 A≤B j≢Z) ⊢2 = ⊢d-sub' (subst-3m' (suc k₁) k₂ (suc (size-t B)) xs x sz₁ (<-pred sz₂) (s≤s m≤m) ⊢1 ⊢2) A≤B
subst-3m' (suc k₁) (suc k₂) (suc k₃) xs x {i = ♭ (S⇐ j)} sz₁ sz₂ sz₃ (⊢d-sub {B = B} ⊢1 A≤B j≢Z) ⊢2 = ⊢d-sub' (subst-3m' (suc k₁) k₂ (suc (size-t B)) xs x sz₁ {!!} (s≤s m≤m) ⊢1 ⊢2) A≤B
subst-3m' (suc k₁) (suc k₂) (suc k₃) xs x {i = S⇒ i} sz₁ sz₂ sz₃ (⊢d-sub {B = B} ⊢1 A≤B j≢Z) ⊢2 = ⊢d-sub' (subst-3m' (suc k₁) k₂ (suc (size-t B)) xs x sz₁ {!!} (s≤s m≤m) ⊢1 ⊢2) A≤B
subst-3m' (suc k₁) (suc k₂) (suc k₃) xs x sz₁ sz₂ sz₃ (⊢d-& ⊢1 ⊢3) ⊢2 = ⊢d-& (subst-3m' (suc k₁) (suc k₂) k₃ xs x sz₁ sz₂ {!!} ⊢1 ⊢2)
                                                                             (subst-3m' (suc k₁) (suc k₂) k₃ xs x sz₁ sz₂ {!!} ⊢3 ⊢2)

subst-3m : ∀ k₁ k₂ k₃ es {Γ A B e e₁ j}
  → len es < k₁
  → size j < k₂
  → size-t B < k₃
  → Γ , A ⊢d j # e ▻ (es ⇈) ⦂ B
  → Γ ⊢d ♭ Z # e₁ ⦂ A
  → Γ ⊢d j # ((ƛ e) · e₁) ▻ es ⦂ B
subst-3m (suc k₁) (suc k₂) (suc k₃) [] sz₁ sz₂ sz₃ ⊢1 ⊢2 = ⊢d-app⇒ (⊢d-lam₂ ⊢1) ⊢2
subst-3m (suc k₁) (suc k₂) (suc k₃) (e ∷ es) {j = j} sz₁ sz₂ sz₃ ⊢1 ⊢2 =
  case lst-destruct-rev (e ∷ es) (ees>0 {e} {es}) of λ where
    ⟨ x , ⟨ xs , eq ⟩ ⟩ → case rw-apps→ {es = xs ⇈} (rw-try ⊢1 (eq-cons-↑ eq)) of λ where
                            (⊢d-app⇐ r r₁) → {! !}
                            (⊢d-app⇒ r r₁) → {!!}
                            (⊢d-sub {A = A} {B = B} ⊢e A≤B j≢Z) → case inspect j of λ where
                                                    (♭ Z with≡ j≡Z) → ⊥-elim (j≢Z j≡Z)
                                                    (♭ ∞ with≡ j≡∞) →
                                                          -- problematic function calls
                                                      let ind-e = subst-3m (suc k₁) k₂ ((suc (size-t B))) (xs ++ ⟦ x ⟧)
                                                                                       (sz-case₁ sz₁ eq) (sz-case₄ j≡∞ sz₂) {!!}
                                                                           ((rw-map {xs = xs} (rw-apps← {es = xs ⇈} ⊢e))) ⊢2
                                                      in ⊢d-sub' (rw-try' {!!} eq) A≤B
                                                    (♭ (S⇐ j') with≡ j≡Sj') → {!!}
                                                    (S⇒ i with≡ j≡Si) → {!!}
                            (⊢d-& {A = A} {B = B} ⊢e₁ ⊢e₂) →
                              let ind-e₁ = subst-3m (suc k₁) (suc k₂) k₃ (xs ++ ⟦ x ⟧) (sz-case₁ sz₁ eq) sz₂ (sz-case₂ {A = A} {B = B} sz₃)
                                                                   (rw-map {xs = xs} (rw-apps← {es = xs ⇈} ⊢e₁)) ⊢2
                                  ind-e₂ = subst-3m (suc k₁) (suc k₂) k₃ (xs ++ ⟦ x ⟧) (sz-case₁ sz₁ eq) sz₂ (sz-case₃ {A = A} {B = B} sz₃)
                                                                   (rw-map {xs = xs} (rw-apps← {es = xs ⇈} ⊢e₂)) ⊢2
                              in rw-try' (⊢d-& ind-e₁ ind-e₂) eq



subst' : ∀ k g {Γ A B e e₁ j es}
  → (2 * len es + size j) < k
  → size-t B < g
  → Γ , A ⊢d j # e ▻ map (_↑ 0) es ⦂ B
  → Γ ⊢d ♭ Z # e₁ ⦂ A
  → Γ ⊢d j # ((ƛ e) · e₁) ▻ es ⦂ B
subst' (suc k) (suc g) {es = []} sz-k sz-g ⊢1 ⊢2 = ⊢d-app⇒ (⊢d-lam₂ ⊢1) ⊢2
subst' (suc k) (suc g) {j = j} {es = e ∷ es} sz-k sz-g ⊢1 ⊢2 =
  case lst-destruct-rev (e ∷ es) (ees>0 {e} {es}) of λ where
    ⟨ x , ⟨ xs , eq ⟩ ⟩ → case rw-apps→ {es = xs ⇈} (rw-try ⊢1 (eq-cons-↑ eq)) of λ where
                            (⊢d-app⇐ r r₁) → {!!}
                            (⊢d-app⇒ r r₁) → {!!}
                            (⊢d-sub {A = A} {B = B} ⊢e A≤B j≢Z) → case inspect j of λ where
                                                    (♭ Z with≡ j≡Z) → ⊥-elim (j≢Z j≡Z)
                                                    (♭ ∞ with≡ j≡∞) →
                                                      let ind-e = subst' k (suc (size-t B)) {!!} (s≤s m≤m)
                                                                           ((rw-map {xs = xs} (rw-apps← {es = xs ⇈} ⊢e))) ⊢2
                                                      in ⊢d-sub' (rw-try' ind-e eq) A≤B
                                                    (♭ (S⇐ j') with≡ j≡Sj') → {!!}
                                                    (S⇒ i with≡ j≡Si) → {!!}
                            (⊢d-& ⊢e₁ ⊢e₂) → let ind-e₁ = subst' (suc k) g {es = xs ++ ⟦ x ⟧} {!sz-k!} {!!} (rw-apps← ⊢e₁) ⊢2
                                                 ind-e₂ = subst' (suc k) g sz-k {!!} ⊢e₂ ⊢2
                                             in rw-try' (rw-apps← {es = xs} (⊢d-& {!ind-e₁!}
                                                                                  ind-e₂)) eq 
  
subst :  ∀ {Γ A B e e₁ i} (es : List Term)
  → Γ , A ⊢d i # e ▻ map (_↑ 0) es ⦂ B
  → Γ ⊢d ♭ Z # e₁ ⦂ A
  → Γ ⊢d i # ((ƛ e) · e₁) ▻ es ⦂ B
subst {B = B} {i = i} es ⊢1 ⊢2 = subst' (suc (2 * len es + size i)) (suc (size-t B)) {es = es} (s≤s m≤m) (s≤s m≤m) ⊢1 ⊢2   

sound-inf : ∀ {Γ e H A es As A'}
  → Γ ⊢a H ⇛ e ⇛ A
  → ❪ H , A ❫↣❪ es , □ , As , A' ❫
  → Γ ⊢d ♭ Z # e ▻ es ⦂ A'

sound-chk : ∀ {Γ e H A es T As A'}
  → Γ ⊢a H ⇛ e ⇛ A
  → ❪ H , A ❫↣❪ es , τ T , As , A' ❫
  → Γ ⊢d ♭ ∞ # e ▻ es ⦂ T

sound-inf-0 : ∀ {Γ e A}
  → Γ ⊢a □ ⇛ e ⇛ A
  → Γ ⊢d ♭ Z # e ⦂ A
sound-inf-0 ⊢e = sound-inf ⊢e none-□

sound-chk-0 : ∀ {Γ e A}
  → Γ ⊢a τ A ⇛ e ⇛ A
  → Γ ⊢d ♭ ∞ # e ⦂ A
sound-chk-0 ⊢e = sound-chk ⊢e none-τ

sound-inf ⊢a-lit none-□ = ⊢d-int
sound-inf (⊢a-var x) none-□ = ⊢d-var x
sound-inf (⊢a-ann ⊢e) none-□ = ⊢d-ann (sound-chk-0 ⊢e)
sound-inf (⊢a-app ⊢e) spl = sound-inf ⊢e (have spl)
sound-inf {es = e ∷ es} (⊢a-lam₂ ⊢e ⊢f) (have spl) = subst es (sound-inf ⊢f (spl-weaken spl)) (sound-inf ⊢e none-□)
sound-inf (⊢a-sub pv-e ⊢e A≤H) spl = ⊩-elim (sound-inf-0 ⊢e) {!!} {!!} {!!} spl -- correct

sound-chk (⊢a-app ⊢e) spl = sound-chk ⊢e (have spl)
sound-chk (⊢a-lam₁ ⊢e) none-τ = ⊢d-lam₁ (sound-chk-0 ⊢e)
sound-chk {es = e ∷ es} (⊢a-lam₂ ⊢e ⊢f) (have spl)  = subst es (sound-chk ⊢f (spl-weaken spl)) (sound-inf ⊢e none-□)
sound-chk (⊢a-sub x ⊢e x₁) spl = ⊢d-sub (⊩-elim (sound-inf-0 ⊢e) {!!} {!!} {!!} spl) {!!} λ ()
sound-chk (⊢a-& ⊢e ⊢e₁) none-τ = ⊢d-& (sound-chk ⊢e none-τ) (sound-chk ⊢e₁ none-τ)

{-

app-elim : ∀ {Γ e A}
  → Γ ⊢d ♭ Z # e ▻ es ⦂ A
  → i ~ es ~ A' ~ A
  → Γ ⊢d i # e ⦂ A'
-}
