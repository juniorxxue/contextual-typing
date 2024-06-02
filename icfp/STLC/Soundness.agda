module STLC.Soundness where

open import STLC.Prelude
open import STLC.Common
open import STLC.Decl
open import STLC.Decl.Properties
open import STLC.Algo
open import STLC.Algo.Properties

_▻_ : Term → List Term → Term
e ▻ [] = e
e₁ ▻ (e₂ ∷ es) = (e₁ · e₂) ▻ es

infix 4 _⊩_⇐_
data _⊩_⇐_ : Env → List Term → List Type → Set where
  ⊩none : ∀ {Γ}
    → Γ ⊩ [] ⇐ []

  ⊩cons : ∀ {Γ es As e A}
    → Γ ⊩ es ⇐ As
    → Γ ⊢ ∞ # e ⦂ A
    → Γ ⊩ (e ∷ es) ⇐ (A ∷ As)

⊩-elim : ∀ {Γ e Σ A es T As A'}
  → Γ ⊢ Z # e ⦂ A
  → Γ ⊩ es ⇐ As
  → ⟦ Σ , A ⟧→⟦ es , T , As , A' ⟧
  → Γ ⊢ Z # e ▻ es ⦂ A'
⊩-elim ⊢d ⊩none none-□ = ⊢d
⊩-elim ⊢d ⊩none none-τ = ⊢d
⊩-elim ⊢d (⊩cons ⊩es x) (have spl) = ⊩-elim (⊢app₁ ⊢d x) ⊩es spl

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
  → Γ , A ⊢ j # e ▻ map (_↑ 0) es ⦂ B
  → Γ ⊢ Z # e₁ ⦂ A
  → Γ ⊢ j # ((ƛ e) · e₁) ▻ es ⦂ B
subst-case-0 {es = es} sz ⊢1 ⊢2 rewrite ¬<0→nil {es = es} sz = ⊢app₂ (⊢lam-n ⊢1) ⊢2

size-counter : Counter → ℕ
size-counter ∞ = 1
size-counter Z = 0
size-counter (S j) = 1 + size-counter j

¬Zsize-counter>0 : ∀ {k j}
  → ¬Z j
  → size-counter j ≤ k
  → 0 < k
¬Zsize-counter>0 ¬Z-∞ sz = sz
¬Zsize-counter>0 ¬Z-S (s≤s sz) = s≤s z≤n

subst-2 : ∀ k₁ k₂ es {Γ A B e e₁ j}
  → len es < k₁
  → size-counter j < k₂
  → Γ , A ⊢ j # e ▻ (es ↑s) ⦂ B
  → Γ ⊢ Z # e₁ ⦂ A
  → Γ ⊢ j # ((ƛ e) · e₁) ▻ es ⦂ B

subst-2-app : ∀ k₁ k₂ xs x {Γ A B e e₁ j}
  → (1 + len xs) < k₁
  → size-counter j < k₂
  → Γ , A ⊢ j # (e ▻ (xs ↑s)) · (x ↑ 0) ⦂ B
  → Γ ⊢ Z # e₁ ⦂ A
  → Γ ⊢ j # (((ƛ e) · e₁) ▻ xs) · x ⦂ B

subst-2 (suc k₁) (suc k₂) es (s≤s sz₁) (s≤s sz₂) ⊢1 ⊢2 with len es >? 0
subst-2 (suc k₁) (suc k₂) es {e = e} {e₁ = e₁} (s≤s sz₁) (s≤s sz₂) ⊢1 ⊢2 | yes p with apps-destruct es p
... | des-app x xs eq rewrite eq
                            | rw-apps xs ((ƛ e) · e₁) x
                            | ↑s-++-distri xs x
                            | rw-apps (xs ↑s) e (x ↑ 0)
                            = subst-2-app (suc k₁) (suc k₂) xs x (len-++-suc x xs k₁ (s≤s sz₁)) (s≤s sz₂) ⊢1 ⊢2
subst-2 (suc k₁) (suc k₂) es (s≤s sz₁) (s≤s sz₂) ⊢1 ⊢2 | no ¬p = subst-case-0 {es = es} ¬p ⊢1 ⊢2

subst-2-app (suc k₁) (suc k₂) xs x (s≤s sz₁) (s≤s sz₂) (⊢app₁ ⊢1 ⊢3) ⊢2 =
  let ind-e₁ = subst-2 k₁ (suc (suc k₂)) xs sz₁ (s≤s z≤n) ⊢1 ⊢2
  in (⊢app₁ ind-e₁ (⊢strengthen-0 ⊢3))
subst-2-app (suc k₁) (suc k₂) xs x (s≤s sz₁) (s≤s sz₂) (⊢app₂ ⊢1 ⊢3) ⊢2 =
  let ind-e₁ = subst-2 k₁ (suc (suc k₂)) xs sz₁ (s≤s (s≤s sz₂)) ⊢1 ⊢2
  in (⊢app₂ ind-e₁ (⊢strengthen-0 ⊢3))
subst-2-app (suc k₁) (suc k₂) xs x (s≤s sz₁) (s≤s sz₂) (⊢sub ⊢1 neq) ⊢2 =
  ⊢sub' (subst-2-app (suc k₁) k₂ xs x (s≤s sz₁) (¬Zsize-counter>0 neq sz₂) ⊢1 ⊢2)

subst :  ∀ {Γ A B e e₁ j} (es : List Term)
  → Γ , A ⊢ j # e ▻ map (_↑ 0) es ⦂ B
  → Γ ⊢ Z # e₁ ⦂ A
  → Γ ⊢ j # ((ƛ e) · e₁) ▻ es ⦂ B
subst {j = j} es ⊢1 ⊢2 = subst-2 (suc (len es)) (suc (size-counter j)) es (s≤s m≤m) (s≤s m≤m) ⊢1 ⊢2

⊢spl-eq : ∀ {Γ Σ A e es T As A'}
  → Γ ⊢ Σ ⇒ e ⇒ A
  → ⟦ Σ , A ⟧→⟦ es , τ T , As , A' ⟧
  → T ≡ A'
⊢spl-eq ⊢e none-τ = ⊢context-full-type ⊢e
⊢spl-eq ⊢e (have spl) = ⊢spl-eq (⊢app ⊢e) spl

sound-≈ : ∀ {Γ Σ A es T As A'}
  → Γ ⊢ A ≈ Σ
  → ⟦ Σ , A ⟧→⟦ es , T , As , A' ⟧
  → Γ ⊩ es ⇐ As

sound-inf : ∀ {Γ e Σ A es As A'}
  → Γ ⊢ Σ ⇒ e ⇒ A
  → ⟦ Σ , A ⟧→⟦ es , □ , As , A' ⟧
  → Γ ⊢ Z # e ▻ es ⦂ A'

sound-chk : ∀ {Γ e Σ A es T As A'}
  → Γ ⊢ Σ ⇒ e ⇒ A
  → ⟦ Σ , A ⟧→⟦ es , τ T , As , A' ⟧
  → Γ ⊢ ∞ # e ▻ es ⦂ T

sound-inf0 : ∀ {Γ e A}
  → Γ ⊢ □ ⇒ e ⇒ A
  → Γ ⊢ Z # e ⦂ A
sound-inf0 ⊢e = sound-inf ⊢e none-□

sound-chk0 : ∀ {Γ e A B}
  → Γ ⊢ τ B ⇒ e ⇒ A
  → Γ ⊢ ∞ # e ⦂ B
sound-chk0 ⊢e = sound-chk ⊢e none-τ

sound-≈ ≈□ none-□ = ⊩none
sound-≈ ≈τ none-τ = ⊩none
sound-≈ (≈term ⊢e A≈Σ) (have spl) = ⊩cons (sound-≈ A≈Σ spl) (sound-chk ⊢e none-τ)

sound-inf ⊢lit none-□ = ⊢int
sound-inf (⊢var x) none-□ = ⊢var x
sound-inf (⊢ann ⊢e) none-□ = ⊢ann (sound-chk ⊢e none-τ)
sound-inf (⊢app ⊢e) spl = sound-inf ⊢e (have spl)
sound-inf {es = e ∷ es} (⊢lam₂ ⊢e ⊢f) (have spl) = subst es (sound-inf ⊢f (spl-weaken spl)) (sound-inf ⊢e none-□)
sound-inf (⊢sub ⊢e A≈Σ p Σ≢□) spl = ⊢sub' (⊩-elim (sound-inf ⊢e none-□) (sound-≈ A≈Σ spl) spl)

sound-chk (⊢app ⊢e) spl = sound-chk ⊢e (have spl)
sound-chk (⊢lam₁ ⊢e) none-τ = ⊢lam-∞ (sound-chk ⊢e none-τ)
sound-chk {es = e ∷ es} (⊢lam₂ ⊢e ⊢f) (have spl)  = subst es (sound-chk ⊢f (spl-weaken spl)) (sound-inf ⊢e none-□)
sound-chk ty@(⊢sub ⊢e A≈Σ p Σ≢□) spl rewrite ⊢spl-eq ty spl = ⊢sub' (⊩-elim (sound-inf ⊢e none-□) (sound-≈ A≈Σ spl) spl)
