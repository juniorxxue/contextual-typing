module Record.Soundness where

open import Record.Prelude
open import Record.Common
open import Record.Decl
open import Record.Decl.Properties
open import Record.Algo
open import Record.Algo.Properties

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

subst :  ∀ {Γ A B e e₁ i} (es : Apps)
  → Γ , A ⊢d i # e ▻ up 0 es ⦂ B
  → Γ ⊢d ♭ Z # e₁ ⦂ A
  → Γ ⊢d i # ((ƛ e) · e₁) ▻ es ⦂ B
subst {B = B} {i = i} es ⊢1 ⊢2 = {!!}

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
sound-inf (⊢a-sub x ⊢e x₁) spl = app-elim (⊢d-sub' (sound-inf-0 ⊢e) (sound-≤ x₁ spl)) spl (sound-es x₁ spl)
sound-inf (⊢a-rcd x) none-□ = ⊢d-rcd (sound-r x)
sound-inf (⊢a-prj ⊢e) spl = sound-inf ⊢e (have-l spl)

sound-chk (⊢a-app ⊢e) spl = sound-chk ⊢e (have-a spl)
sound-chk (⊢a-lam₁ ⊢e) none-τ = ⊢d-lam₁ (sound-chk ⊢e none-τ)
sound-chk {es = e ∷a es} (⊢a-lam₂ ⊢e ⊢e₁) (have-a spl) = subst es (sound-chk ⊢e₁ (spl-weaken spl)) (sound-inf-0 ⊢e)
sound-chk ⊢e'@(⊢a-sub pv-e ⊢e A≤H) spl rewrite ⊢a-spl-τ ⊢e' spl = app-elim' (⊢d-sub' (sound-inf-0 ⊢e) (sound-≤-chk A≤H spl)) spl (sound-es A≤H spl)
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
