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

subst' : ∀ k g {Γ A B e e₁ j es}
  → (2 * len es + size j) < k
  → size-t B < g
  → Γ , A ⊢d j # e ▻ map (_↑ 0) es ⦂ B
  → Γ ⊢d ♭ Z # e₁ ⦂ A
  → Γ ⊢d j # ((ƛ e) · e₁) ▻ es ⦂ B
subst' (suc k) (suc g) {es = es} sz-k sz-g ⊢1 ⊢2 = {!!}
  
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
