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

  ⊩cons⇚ : ∀ {Γ es As e A}
    → Γ ⊩ es ⇚ As
    → Γ ⊢d ∞ # e ⦂ A
    → Γ ⊩ (e ∷ es) ⇚ (A ∷ As)

⊩-elim : ∀ {Γ e H A es T As A'}
  → Γ ⊢d ‶ 0 # e ⦂ A
  → Γ ⊩ es ⇚ As
  → ❪ H , A ❫↣❪ es , T , As , A' ❫ 
  → Γ ⊢d ‶ 0 # e ▻ es ⦂ A'
⊩-elim ⊢d ⊩none⇚ none-□ = ⊢d
⊩-elim ⊢d ⊩none⇚ none-τ = ⊢d
⊩-elim ⊢d (⊩cons⇚ ⊩es x) (have spl) = ⊩-elim (⊢d-app₁ ⊢d x) ⊩es spl

size-counter : Counter → ℕ
size-counter ∞ = 1
size-counter (‶ n) = n

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

size-counter>0 : ∀ {j}
  → j ≢ ‶ 0
  → size-counter j > 0
size-counter>0 {∞} neq = s≤s z≤n
size-counter>0 {‶ zero} neq = ⊥-elim (neq refl)
size-counter>0 {‶ suc x} neq = s≤s z≤n

subst-case-0 : ∀ {Γ A B es j e e₁}
  → ¬ 1 ≤ len es
  → Γ , A ⊢d j # e ▻ map (_↑ 0) es ⦂ B
  → Γ ⊢d ‶ 0 # e₁ ⦂ A
  → Γ ⊢d j # ((ƛ e) · e₁) ▻ es ⦂ B
subst-case-0 {es = es} {j = ∞} sz ⊢1 ⊢2 rewrite ¬<0→nil {es = es} sz = ⊢d-app₃ (⊢d-lam-∞ ⊢1) ⊢2
subst-case-0 {es = es} {j = ‶ n} sz ⊢1 ⊢2 rewrite ¬<0→nil {es = es} sz = ⊢d-app₂ (⊢d-lam-n ⊢1) ⊢2

subst-2 : ∀ k₁ k₂ es {Γ A B e e₁ j}
  → len es < k₁
  → size-counter j < k₂
  → Γ , A ⊢d j # e ▻ (es ↑s) ⦂ B
  → Γ ⊢d ‶ 0 # e₁ ⦂ A
  → Γ ⊢d j # ((ƛ e) · e₁) ▻ es ⦂ B

subst-2-app : ∀ k₁ k₂ xs x {Γ A B e e₁ j}
  → (1 + len xs) < k₁
  → size-counter j < k₂
  → Γ , A ⊢d j # (e ▻ (xs ↑s)) · (x ↑ 0) ⦂ B
  → Γ ⊢d ‶ 0 # e₁ ⦂ A
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
subst-2-app (suc k₁) (suc k₂) xs x (s≤s sz₁) (s≤s sz₂) (⊢d-app₃ ⊢1 ⊢3) ⊢2 =
  let ind-e₁ = subst-2 k₁ (suc (suc k₂)) xs sz₁ (s≤s (s≤s z≤n)) ⊢1 ⊢2
  in (⊢d-app₃ ind-e₁ (⊢d-strengthen-0 ⊢3))  
subst-2-app (suc k₁) (suc k₂) xs x (s≤s sz₁) (s≤s sz₂) (⊢d-sub ⊢1 j≢0) ⊢2 =
  ⊢d-sub' (subst-2-app (suc k₁) k₂ xs x (s≤s sz₁) (≤-trans (size-counter>0 j≢0) sz₂) ⊢1 ⊢2)

subst :  ∀ {Γ A B e e₁ j} (es : List Term)
  → Γ , A ⊢d j # e ▻ map (_↑ 0) es ⦂ B
  → Γ ⊢d ‶ 0 # e₁ ⦂ A
  → Γ ⊢d j # ((ƛ e) · e₁) ▻ es ⦂ B
subst {j = j} es ⊢1 ⊢2 = subst-2 (suc (len es)) (suc (size-counter j)) es (s≤s m≤m) (s≤s m≤m) ⊢1 ⊢2

⊢a-spl-eq : ∀ {Γ H A e es T As A'}
  → Γ ⊢a H ⇛ e ⇛ A
  → ❪ H , A ❫↣❪ es , τ T , As , A' ❫
  → T ≡ A'
⊢a-spl-eq ⊢e none-τ = ⊢a-hint-self ⊢e
⊢a-spl-eq ⊢e (have spl) = ⊢a-spl-eq (⊢a-app ⊢e) spl

sound-≈ : ∀ {Γ H A es T As A'}
  → Γ ⊢a A ≈ H
  → ❪ H , A ❫↣❪ es , T , As , A' ❫
  → Γ ⊩ es ⇚ As

sound-inf : ∀ {Γ e H A es As A'}
  → Γ ⊢a H ⇛ e ⇛ A
  → ❪ H , A ❫↣❪ es , □ , As , A' ❫
  → Γ ⊢d ‶ 0 # e ▻ es ⦂ A'

sound-chk : ∀ {Γ e H A es T As A'}
  → Γ ⊢a H ⇛ e ⇛ A
  → ❪ H , A ❫↣❪ es , τ T , As , A' ❫
  → Γ ⊢d ∞ # e ▻ es ⦂ T

sound-≈ ≈□ none-□ = ⊩none⇚
sound-≈ ≈τ none-τ = ⊩none⇚
sound-≈ (≈hole ⊢e A≈H) (have spl) = ⊩cons⇚ (sound-≈ A≈H spl) (sound-chk ⊢e none-τ)

sound-inf ⊢a-lit none-□ = ⊢d-int
sound-inf (⊢a-var x) none-□ = ⊢d-var x
sound-inf (⊢a-ann ⊢e) none-□ = ⊢d-ann (sound-chk ⊢e none-τ)
sound-inf (⊢a-app ⊢e) spl = sound-inf ⊢e (have spl)
sound-inf {es = e ∷ es} (⊢a-lam₂ ⊢e ⊢f) (have spl) = subst es (sound-inf ⊢f (spl-weaken spl)) (sound-inf ⊢e none-□)
sound-inf (⊢a-sub ⊢e A≈H p H≢□) spl = ⊢d-sub' (⊩-elim (sound-inf ⊢e none-□) (sound-≈ A≈H spl) spl)

sound-chk (⊢a-app ⊢e) spl = sound-chk ⊢e (have spl)
sound-chk (⊢a-lam₁ ⊢e) none-τ = ⊢d-lam-∞ (sound-chk ⊢e none-τ)
sound-chk {es = e ∷ es} (⊢a-lam₂ ⊢e ⊢f) (have spl)  = subst es (sound-chk ⊢f (spl-weaken spl)) (sound-inf ⊢e none-□)
sound-chk ty@(⊢a-sub ⊢e A≈H p H≢□) spl rewrite ⊢a-spl-eq ty spl = ⊢d-sub' (⊩-elim (sound-inf ⊢e none-□) (sound-≈ A≈H spl) spl)
