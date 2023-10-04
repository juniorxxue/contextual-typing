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


subst' :  ∀ {Γ A B e e₁ j} (es : List Term)
  → Γ , A ⊢d j # e ▻ map (_↑ 0) (reverse es) ⦂ B
  → Γ ⊢d Z # e₁ ⦂ A
  → Γ ⊢d j # ((ƛ e) · e₁) ▻ (reverse es) ⦂ B
subst' [] ⊢1 ⊢2 = ⊢d-app₂ (⊢d-lam-n ⊢1) ⊢2
subst' (e' ∷ es) ⊢1 ⊢2 = {!!}

subst'' :  ∀ {Γ A B e e₁ j k es}
  → len es < k
  → Γ , A ⊢d j # e ▻ map (_↑ 0) es ⦂ B
  → Γ ⊢d Z # e₁ ⦂ A
  → Γ ⊢d j # ((ƛ e) · e₁) ▻ es ⦂ B
subst'' {k = suc k} {es = []} (s≤s sz) ⊢1 ⊢2 = {!!}
subst'' {k = suc k} {es = x ∷ es} sz ⊢1 ⊢2 = {!!}

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
sound-inf (⊢a-lam₂ ⊢e ⊢e₁) (have spl) = {!!}
sound-inf (⊢a-sub ⊢e A≈H p) spl = ⊢d-sub (⊩-elim (sound-inf ⊢e none-□) (sound-≈ A≈H spl) spl) ~0

sound-chk (⊢a-app ⊢e) spl = sound-chk ⊢e (have spl)
sound-chk (⊢a-lam₁ ⊢e) none-τ = ⊢d-lam-∞ (sound-chk ⊢e none-τ)
sound-chk (⊢a-lam₂ ⊢e ⊢e₁) (have spl) = {!!}
sound-chk (⊢a-sub ⊢e x x₁) spl = {!!}

++-head : ∀ {x} (l₁ l₂ : List ℕ)
  → (x ∷ l₁ ++ l₂) ≡ x ∷ (l₁ ++ l₂)
++-head [] l₂ = refl
++-head (x ∷ l₁) l₂ = refl

len-s : ∀ x (l : List ℕ)
  → len (x ∷ l) ≡ suc (len l)
len-s x [] = refl
len-s x (x₁ ∷ l) = refl

app-length : ∀ {l₁ l₂ : List ℕ} k
  → len l₁ < k
  → len (l₁ ++ l₂) ≡ len l₁ + len l₂
app-length {[]} (suc k) (s≤s z≤n) = refl
app-length {x ∷ l₁} (suc k) (s≤s sz) rewrite len-s x l₁ = cong suc (app-length {l₁ = l₁} k sz)
