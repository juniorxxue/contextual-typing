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
  

sound-inf : ∀ {Γ e H A es As A'}
  → Γ ⊢a H ⇛ e ⇛ A
  → ⟦ H , A ⟧→⟦ es , □ , As , A' ⟧
  → Γ ⊢d ♭ Z # e ▻ es ⦂ A'

sound-chk : ∀ {Γ e H A es T As A'}
  → Γ ⊢a H ⇛ e ⇛ A
  → ⟦ H , A ⟧→⟦ es , τ T , As , A' ⟧
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
sound-inf (⊢a-app ⊢e) spl = sound-inf ⊢e (have-a spl)
sound-inf {es = e ∷a es} (⊢a-lam₂ ⊢e ⊢e₁) (have-a spl) = subst es (sound-inf ⊢e₁ (spl-weaken spl)) (sound-inf-0 ⊢e)
sound-inf (⊢a-sub x ⊢e x₁) spl = app-elim (⊢d-sub' (sound-inf-0 ⊢e) {!!}) spl {!!}
sound-inf (⊢a-rcd x) none-□ = {!!} -- trivial
sound-inf (⊢a-prj ⊢e) spl = sound-inf ⊢e (have-l spl)

sound-chk (⊢a-app ⊢e) spl = sound-chk ⊢e (have-a spl)
sound-chk (⊢a-lam₁ ⊢e) none-τ = ⊢d-lam₁ (sound-chk ⊢e none-τ)
sound-chk {es = e ∷a es} (⊢a-lam₂ ⊢e ⊢e₁) (have-a spl) = subst es (sound-chk ⊢e₁ (spl-weaken spl)) (sound-inf-0 ⊢e)
sound-chk (⊢a-sub x ⊢e x₁) spl = {!!}
sound-chk (⊢a-& ⊢e ⊢e₁) none-τ = ⊢d-& (sound-chk ⊢e none-τ) (sound-chk ⊢e₁ none-τ)
sound-chk (⊢a-prj ⊢e) spl = sound-chk ⊢e (have-l spl)
