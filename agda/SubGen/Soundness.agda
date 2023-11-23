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
≤d-j-z (≤d-and₁ A≤B) with ≤d-j-z A≤B
... | ⟨ fst , ⟨ fst₁ , snd ⟩ ⟩ = ⟨ fst , ⟨ ≤d-and₁ fst₁ , snd ⟩ ⟩
≤d-j-z (≤d-and₂ A≤B) with ≤d-j-z A≤B
... | ⟨ fst , ⟨ fst₁ , snd ⟩ ⟩ = ⟨ fst , ⟨ ≤d-and₂ fst₁ , snd ⟩ ⟩

≤d-j-∞ : ∀ {A B C j}
  → A ≤d ♭ (S⇐ j) # B ⇒ C
  → ∃[ C' ] (A ≤d ♭ (S⇐ ∞) # B ⇒ C') × (C' ≤d (♭ j) # C)
≤d-j-∞ (≤d-arr-S⇐ {B = B} A≤B A≤B₁) = ⟨ B , ⟨ (≤d-arr-S⇐ A≤B ≤d-refl∞) , A≤B₁ ⟩ ⟩
≤d-j-∞ (≤d-and₁ A≤B) with ≤d-j-∞ A≤B
... | ⟨ fst , ⟨ fst₁ , snd ⟩ ⟩ = ⟨ fst , ⟨ ≤d-and₁ fst₁ , snd ⟩ ⟩
≤d-j-∞ (≤d-and₂ A≤B) with ≤d-j-∞ A≤B
... | ⟨ fst , ⟨ fst₁ , snd ⟩ ⟩ = ⟨ fst , ⟨ ≤d-and₂ fst₁ , snd ⟩ ⟩

⊩-elim : ∀ {Γ e H A es As A' A'' i T}
  → Γ ⊢d ♭ Z # e ⦂ A
  → Γ ⊩ es ⇚ As
  → build-iZ es i
  → A ≤d i # A'
  → ❪ H , A' ❫↣❪ es , T , As , A'' ❫ 
  → Γ ⊢d ♭ Z # e ▻ es ⦂ A''
⊩-elim ⊢e ⊩none⇚ bj-none A≤A' none-□ = {!!}
⊩-elim ⊢e ⊩none⇚ bj-none A≤A' none-τ = {!!}
⊩-elim ⊢e (⊩cons⇚ ⊢es x) (bj-cons bi) A≤A' (have spl) with ≤d-j-z A≤A'
... | ⟨ E , ⟨ fst , snd ⟩ ⟩ = ⊩-elim ((⊢d-app⇐ (⊢d-sub ⊢e fst λ ()) x)) ⊢es bi snd spl

-- ⊩-elim ⊢e (⊩cons⇚ ⊢es x) A≤A' (have spl) = ⊩-elim (⊢d-app⇐ (⊢d-sub ⊢e {!!} λ ()) x) ⊢es {!!} spl

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
sound-inf (⊢a-lam₂ ⊢e ⊢e₁) (have spl) = {!!}
sound-inf (⊢a-sub pv-e ⊢e A≤H) spl = ⊩-elim (sound-inf-0 ⊢e) {!!} {!!} {!!} spl -- correct

sound-chk (⊢a-app ⊢e) spl = sound-chk ⊢e (have spl)
sound-chk (⊢a-lam₁ ⊢e) none-τ = ⊢d-lam₁ (sound-chk-0 ⊢e)
sound-chk (⊢a-lam₂ ⊢e ⊢e₁) spl = {!!}
sound-chk (⊢a-sub x ⊢e x₁) spl = ⊢d-sub (⊩-elim (sound-inf-0 ⊢e) {!!} {!!} {!!} spl) {!!} λ ()
sound-chk (⊢a-& ⊢e ⊢e₁) none-τ = ⊢d-& (sound-chk ⊢e none-τ) (sound-chk ⊢e₁ none-τ)

{-

app-elim : ∀ {Γ e A}
  → Γ ⊢d ♭ Z # e ▻ es ⦂ A
  → i ~ es ~ A' ~ A
  → Γ ⊢d i # e ⦂ A'
-}


