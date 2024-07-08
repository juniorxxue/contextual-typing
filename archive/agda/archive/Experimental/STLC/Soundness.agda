module STLC.Soundness where

open import STLC.Prelude
open import STLC.Common
open import STLC.Decl
open import STLC.Decl.Properties
open import STLC.Algo
open import STLC.Algo.Properties

infix 4 _⊩_⇚_
data _⊩_⇚_ : Context → List Term → List Type → Set where
  ⊩none⇚ : ∀ {Γ}
    → Γ ⊩ [] ⇚ []

  ⊩cons⇚ : ∀ {Γ es As e A j}
    → Γ ⊩ es ⇚ As
    → Γ ⊢d j # e ⦂ A
    → Γ ⊩ (e ∷ es) ⇚ (A ∷ As)

----------------------------------------------------------------------
--+                                                                +--
--+                             Subst                              +--
--+                                                                +--
----------------------------------------------------------------------

Apps : Set
Apps = List Term

AppsType : Set
AppsType = List Type

infix 5 _↑s
_↑s : Apps → Apps
_↑s = map (_↑ 0)

data AppsDes (as : Apps) : Set where

  des-app : ∀ x xs
    → (eq : as ≡ xs ++ (x ∷ []))
    → AppsDes as

apps-destruct : ∀ as
  → 0 < len as
  → AppsDes as
apps-destruct ⟦ x ⟧ (s≤s sz) = des-app x [] refl
apps-destruct (x ∷ y ∷ as) (s≤s sz) with apps-destruct (y ∷ as) (s≤s z≤n)
... | des-app x' xs eq rewrite eq = des-app x' (x ∷ xs) refl

len-++-distri : ∀ (xs ys : Apps)
  → len (xs ++ ys) ≡ len xs + len ys
len-++-distri [] ys = refl
len-++-distri (x ∷ xs) ys rewrite len-++-distri xs ys = refl

len-++-suc : ∀ (x : Term) xs k
  → suc (len (xs ++ ⟦ x ⟧)) ≤ suc k
  → suc (len xs) < suc k
len-++-suc x xs k (s≤s sz) rewrite len-++-distri xs ⟦ x ⟧ | +-comm 1 (len xs) = s≤s sz

rw-apps-gen : ∀ (es) {e es'}
  → e ▻ (es ++ es') ≡ (e ▻ es) ▻ es'
rw-apps-gen [] = refl
rw-apps-gen (x ∷ es) = rw-apps-gen es

rw-apps : ∀ es e x
  → e ▻ (es ++ ⟦ x ⟧) ≡ (e ▻ es) · x
rw-apps es e x = rw-apps-gen es {e = e} {es' = ⟦ x ⟧}

↑s-++-distri : ∀ xs x
  → (xs ++ ⟦ x ⟧) ↑s ≡ (xs ↑s) ++ (⟦ x ⟧ ↑s)
↑s-++-distri [] x = refl
↑s-++-distri (x₁ ∷ xs) x rewrite ↑s-++-distri xs x = refl

¬<0→nil : ∀ {es : Apps}
  → ¬ 1 ≤ len es
  → es ≡ []
¬<0→nil {[]} sz = refl
¬<0→nil {x ∷ es} sz = ⊥-elim (sz (s≤s z≤n))

subst-case-0 : ∀ {Γ A B es j e e₁}
  → ¬ 1 ≤ len es
  → Γ , A ⊢d j # e ▻ map (_↑ 0) es ⦂ B
  → Γ ⊢d 0 # e₁ ⦂ A
  → Γ ⊢d j # ((ƛ e) · e₁) ▻ es ⦂ B
subst-case-0 {es = es} sz ⊢1 ⊢2 rewrite ¬<0→nil {es = es} sz = ⊢d-app₂ (⊢d-lam ⊢1) ⊢2

subst-2 : ∀ k₁ k₂ es {Γ A B e e₁ j}
  → len es < k₁
  → j < k₂
  → Γ , A ⊢d j # e ▻ (es ↑s) ⦂ B
  → Γ ⊢d 0 # e₁ ⦂ A
  → Γ ⊢d j # ((ƛ e) · e₁) ▻ es ⦂ B

subst-2-app : ∀ k₁ k₂ xs x {Γ A B e e₁ j}
  → (1 + len xs) < k₁
  → j < k₂
  → Γ , A ⊢d j # (e ▻ (xs ↑s)) · (x ↑ 0) ⦂ B
  → Γ ⊢d 0 # e₁ ⦂ A
  → Γ ⊢d j #  (((ƛ e) · e₁) ▻ xs) · x ⦂ B

subst-2 (suc k₁) (suc k₂) es (s≤s sz₁) (s≤s sz₂) ⊢1 ⊢2 with len es >? 0
subst-2 (suc k₁) (suc k₂) es {e = e} {e₁ = e₁} (s≤s sz₁) (s≤s sz₂) ⊢1 ⊢2 | yes p with apps-destruct es p
... | des-app x xs eq rewrite eq
                            | rw-apps xs ((ƛ e) · e₁) x
                            | ↑s-++-distri xs x
                            | rw-apps (xs ↑s) e (x ↑ 0)
                            = subst-2-app (suc k₁) (suc k₂) xs x (len-++-suc x xs k₁ (s≤s sz₁)) (s≤s sz₂) ⊢1 ⊢2
subst-2 (suc k₁) (suc k₂) es (s≤s sz₁) (s≤s sz₂) ⊢1 ⊢2 | no ¬p = subst-case-0 {es = es} ¬p ⊢1 ⊢2

subst-2-app (suc k₁) (suc k₂) xs x (s≤s sz₁) (s≤s sz₂) (⊢d-app₁ ⊢1 ⊢3) ⊢2 =
  let ind-e₁ = subst-2 k₁ (suc (suc k₂)) xs sz₁ (s≤s z≤n) ⊢1 ⊢2
  in (⊢d-app₁ ind-e₁ (⊢d-strengthen-0 ⊢3))
subst-2-app (suc k₁) (suc k₂) xs x (s≤s sz₁) (s≤s sz₂) (⊢d-app₂ ⊢1 ⊢3) ⊢2 =
  let ind-e₁ = subst-2 k₁ (suc (suc k₂)) xs sz₁ (s≤s (s≤s sz₂)) ⊢1 ⊢2
  in (⊢d-app₂ ind-e₁ (⊢d-strengthen-0 ⊢3))
subst-2-app (suc k₁) (suc k₂) xs x (s≤s sz₁) (s≤s sz₂) (⊢d-sub ⊢1) ⊢2 =
  ⊢d-sub' (subst-2-app (suc k₁) k₂ xs x (s≤s sz₁) (m<n⇒0<n sz₂) ⊢1 ⊢2)

subst :  ∀ {Γ A B e e₁ j} (es : List Term)
  → Γ , A ⊢d j # e ▻ (es ↑s) ⦂ B
  → Γ ⊢d 0 # e₁ ⦂ A
  → Γ ⊢d j # ((ƛ e) · e₁) ▻ es ⦂ B
subst {j = j} es ⊢1 ⊢2 = subst-2 (suc (len es)) (suc j) es (s≤s m≤m) (s≤s m≤m) ⊢1 ⊢2

----------------------------------------------------------------------
--+                                                                +--
--+                           Soundness                            +--
--+                                                                +--
----------------------------------------------------------------------


app-elim : ∀ {Γ e H es A A' As}
  → Γ ⊢d 0 # e ⦂ A
  → ❪ H , A ❫↣❪ es , □ , As , A' ❫
  → Γ ⊩ es ⇚ As
  → Γ ⊢d 0 # e ▻ es ⦂ A'
app-elim ⊢e none-□ ⊩none⇚ = ⊢e
app-elim ⊢e (have spl) (⊩cons⇚ ⊢es x) = app-elim (⊢d-app₁ ⊢e x) spl ⊢es

app-elim' : ∀ {Γ e H es A A' As T}
  → Γ ⊢d 0 # e ⦂ A
  → ❪ H , A ❫↣❪ es , τ T , As , A' ❫
  → Γ ⊩ es ⇚ As
  → Γ ⊢d 0 # e ▻ es ⦂ A'
app-elim' ⊢e none-τ ⊩none⇚ = ⊢e
app-elim' ⊢e (have spl) (⊩cons⇚ ⊢es x) = app-elim' (⊢d-app₁ ⊢e x) spl ⊢es

sound-inf : ∀ {Γ e H A es As A'}
  → Γ ⊢a H ⇛ e ⇛ A
  → ❪ H , A ❫↣❪ es , □ , As , A' ❫
  → Γ ⊢d 0 # e ▻ es ⦂ A'

sound-chk : ∀ {Γ e H A es T As A'}
  → Γ ⊢a H ⇛ e ⇛ A
  → ❪ H , A ❫↣❪ es , τ T , As , A' ❫
  → ∃[ j ](Γ ⊢d j # e ▻ es ⦂ T)

sound-≈ : ∀ {Γ H A es T As A'}
  → Γ ⊢a A ≈ H
  → ❪ H , A ❫↣❪ es , T , As , A' ❫
  → Γ ⊩ es ⇚ As

sound-≈ ≈□ none-□ = ⊩none⇚
sound-≈ ≈τ none-τ = ⊩none⇚
sound-≈ (≈hole ⊢e A≈H) (have spl) with sound-chk ⊢e none-τ
... | ⟨ _ , ⊢e' ⟩ = ⊩cons⇚ (sound-≈ A≈H spl) ⊢e'

sound-inf ⊢a-lit none-□ = ⊢d-int
sound-inf (⊢a-var x) none-□ = ⊢d-var x
sound-inf (⊢a-ann ⊢e) none-□ with sound-chk ⊢e none-τ
... | ⟨ j , ⊢e' ⟩ = ⊢d-ann ⊢e'
sound-inf (⊢a-app ⊢e) spl = sound-inf ⊢e (have spl)
sound-inf {es = e ∷ es} (⊢a-lam₂ ⊢e ⊢e₁) (have spl) = subst es (sound-inf ⊢e₁ (spl-weaken spl)) (sound-inf ⊢e none-□)
sound-inf (⊢a-sub ⊢e x x₁) spl = app-elim (sound-inf ⊢e none-□) spl (sound-≈ x spl)

sound-chk (⊢a-app ⊢e) spl = sound-chk ⊢e (have spl)
sound-chk (⊢a-lam₁ ⊢e) none-τ with sound-chk ⊢e none-τ
... | ⟨ j , ⊢e' ⟩ = ⟨ suc j , ⊢d-lam ⊢e' ⟩
sound-chk {es = e ∷ es} (⊢a-lam₂ ⊢e ⊢e₁) (have spl) with sound-chk ⊢e₁ (spl-weaken spl)
... | ⟨ j , ⊢e' ⟩ = ⟨ j , subst es ⊢e' (sound-inf ⊢e none-□) ⟩
sound-chk ⊢sub@(⊢a-sub ⊢e x x₁) spl with sound-inf ⊢e none-□
... | ⊢e' rewrite ⊢a-spl-eq ⊢sub spl = ⟨ 0 , app-elim' (sound-inf ⊢e none-□) spl (sound-≈ x spl) ⟩
