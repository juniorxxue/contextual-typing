module STLC.Soundness where

open import STLC.Prelude
open import STLC.Common
open import STLC.Decl
open import STLC.Decl.Properties
open import STLC.Algo
open import STLC.Algo.Properties

open import Data.Nat
open import Data.Nat.Properties


infix 4 _⊩_⇚_
data _⊩_⇚_ : Context → List Term → List Type → Set where
  ⊩none⇚ : ∀ {Γ}
    → Γ ⊩ [] ⇚ []

  ⊩cons⇚ : ∀ {Γ es As e A}
    → Γ ⊩ es ⇚ As
    → Γ ⊢d ∞ # e ⦂ A
    → Γ ⊩ (e ∷ es) ⇚ (A ∷ As)

⊩-elim : ∀ {Γ e H A es T As A'}
  → Γ ⊢d Z # e ⦂ A
  → Γ ⊩ es ⇚ As
  → ❪ H , A ❫↣❪ es , T , As , A' ❫ 
  → Γ ⊢d Z # e ▻ es ⦂ A'
⊩-elim ⊢d ⊩none⇚ none-□ = ⊢d
⊩-elim ⊢d ⊩none⇚ none-τ = ⊢d
⊩-elim ⊢d (⊩cons⇚ ⊩es x) (have spl) = ⊩-elim (⊢d-app₁ ⊢d x) ⊩es spl

size : Counter → ℕ
size ∞ = 1
size Z = 0
size (S j) = 1 + size j

lst-destruct-rev : ∀ (l : List Term)
  → 0 < len l
  → ∃[ x ] (∃[ xs ] (l ≡ (xs ++ x ∷ [])))
lst-destruct-rev (x ∷ []) (s≤s z≤n) = ⟨ x , ⟨ [] , refl ⟩ ⟩
lst-destruct-rev (x ∷ y ∷ l) (s≤s z≤n) with lst-destruct-rev (y ∷ l) (s≤s z≤n)
... | ⟨ x' , ⟨ xs' , eq ⟩ ⟩ rewrite eq = ⟨ x' , ⟨ x ∷ xs' , refl ⟩ ⟩

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

ees>0 : ∀ {e} {es : List Term}
  → len (e ∷ es) > 0
ees>0 {e} {es} = s≤s z≤n

rewrite-test : ∀ {e₁ e₂ es}
  → (e₁ · e₂) ▻ es ≡ e₁ ▻ (e₂ ∷ es)
rewrite-test = refl

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

{-
subst' : ∀ (k) {Γ A B e e₁ j es}
  → 2 * len es + size j < k
  → Γ , A ⊢d j # e ▻ map (_↑ 0) es ⦂ B
  → Γ ⊢d Z # e₁ ⦂ A
  → Γ ⊢d j # ((ƛ e) · e₁) ▻ es ⦂ B
subst' (suc k) {es = []} sz ⊢1 ⊢2 = ⊢d-app₂ (⊢d-lam-n ⊢1) ⊢2
subst' (suc k) {es = e ∷ es} sz ⊢1 ⊢2 with lst-destruct-rev ((e ↑ 0) ∷ map (_↑ 0) es) (ees>0 {e ↑ 0} {map (_↑ 0) es})
subst' (suc k) {e = e₁} {e₂} {j = _} {e ∷ es} sz ⊢1 ⊢2 | ⟨ x , ⟨ xs , eq ⟩ ⟩ with rw-apps→ {es = xs} (rw-try ⊢1 eq)
... | ⊢d-app₁ r r₁ = {!!}
... | ⊢d-app₂ r r₁ = {!!}
... | ⊢d-sub r x₁ = {!!}
-}


eq-cons-↑ : ∀ {e es xs x}
  → e ∷ es ≡ xs ++ ⟦ x ⟧
  → (e ↑ 0) ∷ map (_↑ 0) es ≡ (map (_↑ 0) xs) ++ ⟦ x ↑ 0 ⟧
eq-cons-↑ {xs = xs} {x = x} eq rewrite sym (map-++-commute (_↑ 0) xs ⟦ x ⟧) = cong (map (_↑ 0)) eq


len-append : ∀ {xs} {x : Term}
  → len (xs ++ ⟦ x ⟧) ≡ 1 + len xs
len-append {[]} = refl
len-append {x ∷ xs} = cong suc (len-append {xs})

cons-++-len : ∀ {e : Term} {es xs x}
  → e ∷ es ≡ xs ++ ⟦ x ⟧
  → len es ≡ len xs
cons-++-len {xs = xs} {x = x} eq with cong len eq
... | r rewrite len-append {xs} {x} = suc-injective r

sz-case₁ : ∀ {es : List Term} {k xs e x}
--  → suc (suc (2 * len es + 0)) ≤ suc k
  → (suc
       (len es + suc (len es + 0) + 0))
      < suc k
  → e ∷ es ≡ xs ++ ⟦ x ⟧
  → 2 * len xs + 0 < k
sz-case₁ (s≤s (s≤s sz)) eq rewrite cons-++-len eq = s≤s (tent-lemma sz)
  where tent-lemma : ∀ {m n} → m + suc (m + 0) + 0 ≤ n
                             → m + (m + 0) + 0 ≤ n
        tent-lemma {m} {n} m+1+m+0≤n rewrite m+0≡m m
                                     rewrite m+0≡m (m + m)
                                     rewrite m+0≡m (m + suc m)
                                     rewrite +-comm m (suc m) = m+1≤n→m≤n m+1+m+0≤n


                             
sz-case₂ : ∀ {es : List Term} {k xs e x j}
  → suc
      (suc
       (len es + suc (len es + 0) +
        size j))
      ≤ suc k
  → e ∷ es ≡ xs ++ ⟦ x ⟧
  → 2 * len xs + suc (size j) < k
sz-case₂ (s≤s (s≤s sz)) eq rewrite cons-++-len eq = s≤s (tent-lemma sz)
  where tent-lemma : ∀ {m n k} → m + suc (m + 0) + k ≤ n
                               → m + (m + 0) + suc k ≤ n
        tent-lemma {m} {n} {k} 2m+k+1≤n rewrite m+0≡m m
                                        rewrite +-suc m m
                                        rewrite +-suc (m + m) k = 2m+k+1≤n

subst' : ∀ (k) {Γ A B e e₁ j es}
  → (2 * len es + size j) < k
  → Γ , A ⊢d j # e ▻ map (_↑ 0) es ⦂ B
  → Γ ⊢d Z # e₁ ⦂ A
  → Γ ⊢d j # ((ƛ e) · e₁) ▻ es ⦂ B
subst' (suc k) {es = []} sz ⊢1 ⊢2 = ⊢d-app₂ (⊢d-lam-n ⊢1) ⊢2
subst' (suc k) {es = e ∷ es} sz ⊢1 ⊢2 with lst-destruct-rev (e ∷ es) (ees>0 {e} {es})
subst' (suc k) {e = e₁} {e₂} {j = j} {e ∷ es} sz ⊢1 ⊢2 | ⟨ x , ⟨ xs , eq ⟩ ⟩ with rw-apps→ {es = map (_↑ 0) xs} (rw-try ⊢1 (eq-cons-↑ eq))
... | ⊢d-app₁ ⊢e₁ ⊢e₂ = rw-try' (rw-apps← {es = xs} (⊢d-app₁ ind-e₁ (⊢d-strengthen-0 ⊢e₂ ))) eq
  where ind-e₁ = subst' k {es = xs} (sz-case₁ sz eq) ⊢e₁ ⊢2
... | ⊢d-app₂ ⊢e₁ ⊢e₂ = rw-try' (rw-apps← {es = xs} (⊢d-app₂ ind-e₁ (⊢d-strengthen-0 ⊢e₂))) eq
  where ind-e₁ = subst' k {es = xs} (sz-case₂ {j = j} sz eq) ⊢e₁ ⊢2
... | ⊢d-sub ⊢e B~j j≢Z = {!!}

-- rewrite in the middle of applications

subst :  ∀ {Γ A B e e₁ j} (es : List Term)
  → Γ , A ⊢d j # e ▻ map (_↑ 0) es ⦂ B
  → Γ ⊢d Z # e₁ ⦂ A
  → Γ ⊢d j # ((ƛ e) · e₁) ▻ es ⦂ B
subst {j = j} es ⊢1 ⊢2 = subst' (suc (2 * len es + size j)) {es = es} (s≤s m≤m) ⊢1 ⊢2

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
  → Γ ⊢d Z # e ▻ es ⦂ A'

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
-- sound-inf (⊢a-lam₂ ⊢e ⊢e₁) (have spl) = {!!}
sound-inf {es = e ∷ es} (⊢a-lam₂ ⊢e ⊢f) (have spl) = subst es (sound-inf ⊢f (spl-weaken spl)) (sound-inf ⊢e none-□)
sound-inf (⊢a-sub ⊢e A≈H p) spl = ⊢d-sub' (⊩-elim (sound-inf ⊢e none-□) (sound-≈ A≈H spl) spl) ~0

sound-chk (⊢a-app ⊢e) spl = sound-chk ⊢e (have spl)
sound-chk (⊢a-lam₁ ⊢e) none-τ = ⊢d-lam-∞ (sound-chk ⊢e none-τ)
-- sound-chk (⊢a-lam₂ ⊢e ⊢e₁) (have spl) = {!!}
sound-chk {es = e ∷ es} (⊢a-lam₂ ⊢e ⊢f) (have spl)  = subst es (sound-chk ⊢f (spl-weaken spl)) (sound-inf ⊢e none-□)
sound-chk ty@(⊢a-sub ⊢e A≈H p) spl rewrite ⊢a-spl-eq ty spl = ⊢d-sub' (⊩-elim (sound-inf ⊢e none-□) (sound-≈ A≈H spl) spl) ~∞
