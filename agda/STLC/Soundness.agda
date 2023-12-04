module STLC.Soundness where

open import STLC.Prelude
open import STLC.Common
open import STLC.Decl
open import STLC.Decl.Properties
open import STLC.Algo
open import STLC.Algo.Properties

postulate

  rev : ∀ {A : Set} (P : List A → Set)
      → P []
      → (∀ (x : A) (l : List A) → P l → P (l ++ (x ∷ [])))
      → (∀ (l : List A) → P l)

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

▻snoc₁ : ∀ e e' es
  → e ▻ map (_↑ 0) (es ++ e' ∷ []) ≡ (e ▻ map (_↑ 0) es) · (e' ↑ 0)
▻snoc₁ e e' [] = refl
▻snoc₁ e e' (e₁ ∷ es) = ▻snoc₁ (e · (e₁ ↑ 0)) e' es

rewrite-snoc₁ : ∀ {Γ e e' es' A cc}
  → Γ ⊢d cc # e ▻ map (_↑ 0) (es' ++ e' ∷ []) ⦂ A
  → Γ ⊢d cc # (e ▻ map (_↑ 0) es') · (e' ↑ 0) ⦂ A
rewrite-snoc₁ {e = e} {e' = e'} {es' = es'} ⊢e rewrite ▻snoc₁ e e' es' = ⊢e

rewrite-snoc₄ : ∀ {Γ e e' es' A cc}
              → Γ ⊢d cc # (e ▻ map (_↑ 0) es') · (e' ↑ 0) ⦂ A
  → Γ ⊢d cc # e ▻ map (_↑ 0) (es' ++ e' ∷ []) ⦂ A
rewrite-snoc₄ {e = e} {e' = e'} {es' = es'} ⊢e rewrite ▻snoc₁ e e' es' = ⊢e

▻snoc₂ : ∀ e es' e'
  → e ▻ (es' ++ e' ∷ []) ≡  (e ▻ es') · e'
▻snoc₂ e [] e' = refl
▻snoc₂ e (x ∷ es') e' = ▻snoc₂ (e · x) es' e'

rewrite-snoc₂ : ∀ {Γ e e₁ es' e' cc B}
  → Γ ⊢d cc # (((ƛ e) · e₁) ▻ es') · e' ⦂ B
  → Γ ⊢d cc # ((ƛ e) · e₁) ▻ (es' ++ e' ∷ []) ⦂ B
rewrite-snoc₂ {e = e} {e₁ = e₁} {es' = es'} {e' = e'} ⊢e rewrite ▻snoc₂ ((ƛ e) · e₁) es' e' = ⊢e

rewrite-snoc₃ : ∀ {Γ e e₁ es' e' cc B}
  → Γ ⊢d cc # ((ƛ e) · e₁) ▻ (es' ++ e' ∷ []) ⦂ B
  → Γ ⊢d cc # (((ƛ e) · e₁) ▻ es') · e' ⦂ B
rewrite-snoc₃ {e = e} {e₁ = e₁} {es' = es'} {e' = e'} ⊢e rewrite ▻snoc₂ ((ƛ e) · e₁) es' e' = ⊢e  

subst :  ∀ {Γ A B e e₁ j} (es : List Term)
  → Γ , A ⊢d j # e ▻ map (_↑ 0) es ⦂ B
  → Γ ⊢d Z # e₁ ⦂ A
  → Γ ⊢d j # ((ƛ e) · e₁) ▻ es ⦂ B
subst es =  rev (λ es → ∀ {Γ} {A} {B} {e} {e₁} {j}
                   → Γ , A ⊢d j # e ▻ map (_↑ 0) es ⦂ B
                   → Γ ⊢d Z # e₁ ⦂ A
                   → Γ ⊢d j # ((ƛ e) · e₁) ▻ es ⦂ B)
                     (λ ⊢e₁ ⊢e₂ → ⊢d-app₂ (⊢d-lam-n ⊢e₁) ⊢e₂)
                     (λ e' es' IH ⊢e₁ ⊢e₂ → rewrite-snoc₂ {es' = es'} (case (rewrite-snoc₁ {es' = es'} ⊢e₁) of λ
                     {(⊢d-app₁ ⊢1 ⊢2) → ⊢d-app₁ (IH ⊢1 ⊢e₂) (⊢d-strengthen-0 ⊢2)
                     ;(⊢d-app₂ ⊢1 ⊢2) → ⊢d-app₂ (IH ⊢1 ⊢e₂) (⊢d-strengthen-0 ⊢2)
                     ;(⊢d-sub ⊢e sub) → ⊢d-sub {!!} sub
                     })) -- ind
                     es

size : Counter → ℕ
size ∞ = 1
size Z = 0
size (S j) = 1 + size j

postulate

  lst-destruct-rev : ∀ (l : List Term)
    → len l > 0
    → ∃[ x ] (∃[ xs ] (l ≡ (xs ++ x ∷ [])))


ees>0 : ∀ {e} {es : List Term}
  → len (e ∷ es) > 0
ees>0 {e} {es} = s≤s z≤n

rewrite-test : ∀ {e₁ e₂ es}
  → (e₁ · e₂) ▻ es ≡ e₁ ▻ (e₂ ∷ es)
rewrite-test = refl

rewrite-test' : ∀ {Γ e₁ e₂ es j B xs x}
  → Γ ⊢d j # e₁ ▻ (xs ++ x ∷ []) ⦂ B
  → (e₂ ∷ es) ≡ (xs ++ x ∷ [])
  → Γ ⊢d j # (e₁ · e₂) ▻ es ⦂ B
rewrite-test' ⊢e eq rewrite (sym eq) = ⊢e

rw-try : ∀ {Γ e₁ e₂ es j B xs x}
  → Γ ⊢d j # (e₁ · e₂) ▻ es ⦂ B
  → (e₂ ∷ es) ≡ (xs ++ x ∷ [])
  → Γ ⊢d j # e₁ ▻ (xs ++ x ∷ []) ⦂ B
rw-try ⊢e eq rewrite (sym eq) = ⊢e

subst' : ∀ (k) {Γ A B e e₁ j es}
  → 2 * len es + size j < k
  → Γ , A ⊢d j # e ▻ map (_↑ 0) es ⦂ B
  → Γ ⊢d Z # e₁ ⦂ A
  → Γ ⊢d j # ((ƛ e) · e₁) ▻ es ⦂ B
subst' (suc k) {es = []} sz ⊢1 ⊢2 = ⊢d-app₂ (⊢d-lam-n ⊢1) ⊢2
subst' (suc k) {es = e ∷ es} sz ⊢1 ⊢2 with lst-destruct-rev (e ∷ es) (ees>0 {e} {es})
subst' (suc k) {e = e₁} {e₂} {j = _} {e ∷ es} sz ⊢1 ⊢2 | ⟨ x , ⟨ xs , eq ⟩ ⟩ = rewrite-test' {!rw-try ⊢1 ?!} eq
-- rewrite-test {e₁ = (ƛ e₁) · e₂} {e₂ = e} {es = es} = {!eq!} 

-- rewrite eq = {!eq!}



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
sound-inf (⊢a-sub ⊢e A≈H p) spl = ⊢d-sub (⊩-elim (sound-inf ⊢e none-□) (sound-≈ A≈H spl) spl) ~0

sound-chk (⊢a-app ⊢e) spl = sound-chk ⊢e (have spl)
sound-chk (⊢a-lam₁ ⊢e) none-τ = ⊢d-lam-∞ (sound-chk ⊢e none-τ)
-- sound-chk (⊢a-lam₂ ⊢e ⊢e₁) (have spl) = {!!}
sound-chk {es = e ∷ es} (⊢a-lam₂ ⊢e ⊢f) (have spl) = subst es (sound-chk ⊢f (spl-weaken spl)) (sound-inf ⊢e none-□)
sound-chk ty@(⊢a-sub ⊢e A≈H p) spl rewrite ⊢a-spl-eq ty spl = ⊢d-sub (⊩-elim (sound-inf ⊢e none-□) (sound-≈ A≈H spl) spl) ~∞
