module Soundness where

open import Prelude
open import Common
open import Dec
open import Algo
open import Algo.Properties

infix 4 _⊩_⇚_
data _⊩_⇚_ : Context → List Term → List Type → Set where
  ⊩none⇚ : ∀ {Γ}
    → Γ ⊩ [] ⇚ []

  ⊩cons⇚ : ∀ {Γ es As e A}
    → Γ ⊩ es ⇚ As
    → Γ ⊢d ∞ ╏ e ⦂ A
    → Γ ⊩ (e ∷ es) ⇚ (A ∷ As)

⊩-elim : ∀ {Γ e H A es T As A'}
  → Γ ⊢d c 0 ╏ e ⦂ A
  → Γ ⊩ es ⇚ As
  → ❪ H , A ❫↣❪ es , T , As , A' ❫ 
  → Γ ⊢d c 0 ╏ e ▻ es ⦂ A'
⊩-elim ⊢d ⊩empty⇚ none = ⊢d
⊩-elim ⊢d (⊩cons⇚ ⊩es ⊢e) (have spl) = ⊩-elim (⊢d-app₁ ⊢d ⊢e) ⊩es spl

infix 4 _⊩_⇛_
data _⊩_⇛_ : Context → List Term → List Type → Set where
  ⊩none⇛ : ∀ {Γ}
    → Γ ⊩ [] ⇛ []

  ⊩cons⇛ : ∀ {Γ es As e A}
    → Γ ⊩ es ⇛ As
    → Γ ⊢d c 0 ╏ e ⦂ A
    → Γ ⊩ (e ∷ es) ⇛ (A ∷ As)


postulate

  rev : ∀ {A : Set} (P : List A → Set)
    → P []
    → (∀ (x : A) (l : List A) → P l → P (l ++ (x ∷ [])))
    → (∀ (l : List A) → P l)

▻snoc₁ : ∀ e e' es
  → e ▻ map (_↑ 0) (es ++ e' ∷ []) ≡ (e ▻ map (_↑ 0) es) · (e' ↑ 0)
▻snoc₁ e e' [] = refl
▻snoc₁ e e' (e₁ ∷ es) = ▻snoc₁ (e · (e₁ ↑ 0)) e' es

rewrite-snoc₁ : ∀ {Γ e e' es' A cc}
  → Γ ⊢d cc ╏ e ▻ map (_↑ 0) (es' ++ e' ∷ []) ⦂ A
  → Γ ⊢d cc ╏ (e ▻ map (_↑ 0) es') · (e' ↑ 0) ⦂ A
rewrite-snoc₁ {e = e} {e' = e'} {es' = es'} ⊢e rewrite ▻snoc₁ e e' es' = ⊢e

▻snoc₂ : ∀ e es' e'
  → e ▻ (es' ++ e' ∷ []) ≡  (e ▻ es') · e'
▻snoc₂ e [] e' = refl
▻snoc₂ e (x ∷ es') e' = ▻snoc₂ (e · x) es' e'

rewrite-snoc₂ : ∀ {Γ e e₁ es' e' B}
  → Γ ⊢d c 0 ╏ (((ƛ e) · e₁) ▻ es') · e' ⦂ B
  → Γ ⊢d c 0 ╏ ((ƛ e) · e₁) ▻ (es' ++ e' ∷ []) ⦂ B
rewrite-snoc₂ {e = e} {e₁ = e₁} {es' = es'} {e' = e'} ⊢e rewrite ▻snoc₂ ((ƛ e) · e₁) es' e' = ⊢e  

subst :  ∀ {Γ A B e e₁} (es : List Term)
  → Γ , A ⊢d c 0 ╏ e ▻ map (_↑ 0) es ⦂ B
  → Γ ⊢d c 0 ╏ e₁ ⦂ A
  → Γ ⊢d c 0 ╏ ((ƛ e) · e₁) ▻ es ⦂ B
subst es = rev (λ es → ∀ {Γ} {A} {B} {e} {e₁}
                     → Γ , A ⊢d c 0 ╏ e ▻ map (_↑ 0) es ⦂ B
                     → Γ ⊢d c 0 ╏ e₁ ⦂ A
                     → Γ ⊢d c 0 ╏ ((ƛ e) · e₁) ▻ es ⦂ B)
                     (λ ⊢e₁ ⊢e₂ → ⊢d-app₂ (⊢d-lam₂ ⊢e₁) ⊢e₂) -- base
                     (λ e' es' IH ⊢e₁ ⊢e₂ → rewrite-snoc₂ {es' = es'} (case (rewrite-snoc₁ {es' = es'} ⊢e₁) of λ
                     {(⊢d-app₁ ⊢1 ⊢2) → ⊢d-app₁ (IH ⊢1 ⊢e₂) {!!}
                     ;(⊢d-app₂ ⊢1 ⊢2) → ⊢d-app₂ {!!} {!!}
                     })) -- ind
                     es

-- rewrite-snoc₁ {es' = es'} ⊢e₁
                     


sound-≤ : ∀ {Γ H A es T As A'}
  → Γ ⊢a A ≤ H
  → ❪ H , A ❫↣❪ es , T , As , A' ❫
  → (A' ≤d T) × (Γ ⊩ es ⇚ As)

sound-inf : ∀ {Γ e H A es As A'}
  → Γ ⊢a H ⇛ e ⇛ A
  → ❪ H , A ❫↣❪ es , Top , As , A' ❫
  → Γ ⊢d c 0 ╏ e ▻ es ⦂ A'

sound-chk : ∀ {Γ e H A es T As A'}
  → Γ ⊢a H ⇛ e ⇛ A
  → ❪ H , A ❫↣❪ es , T , As , A' ❫
  → Γ ⊢d ∞ ╏ e ▻ es ⦂ T

sound-≤ ≤a-int none = ⟨ ≤d-int , ⊩none⇚ ⟩
sound-≤ ≤a-top none = ⟨ ≤d-top , ⊩none⇚ ⟩
sound-≤ (≤a-arr C≤A B≤D) none = ⟨ (≤d-arr ΓC≤A ΓB≤D) , ⊩none⇚ ⟩
  where ΓB≤D = proj₁ (sound-≤ B≤D none)
        ΓC≤A = proj₁ (sound-≤ C≤A none)
sound-≤ (≤a-hint ⊢e A≤H) (have spl) = ⟨ (proj₁ (sound-≤ A≤H spl)) , ⊩cons⇚ (proj₂ (sound-≤ A≤H spl)) (sound-chk ⊢e none) ⟩

sound-inf (⊢a-lit _) none = ⊢d-int
sound-inf (⊢a-var ∋ A≤H) spl = ⊩-elim (⊢d-var ∋) arg-chks spl
  where arg-chks = proj₂ (sound-≤ A≤H spl)
sound-inf (⊢a-app ⊢e) spl = sound-inf ⊢e (have spl)
sound-inf (⊢a-ann ⊢e A≤H) spl = ⊩-elim (⊢d-ann (sound-chk ⊢e none)) arg-chks spl
  where arg-chks = proj₂ (sound-≤ A≤H spl)
sound-inf (⊢a-lam₂ ⊢e ⊢f) (have spl) = {!!}

sound-chk (⊢a-lit ≤a-int) none = ⊢d-sub ⊢d-int ≤d-refl
sound-chk (⊢a-lit ≤a-top) none = ⊢d-sub ⊢d-int ≤d-top
sound-chk (⊢a-var ∋ A≤H) spl = ⊢d-sub elims A'≤T
  where arg-chks = proj₂ (sound-≤ A≤H spl)
        elims = ⊩-elim (⊢d-var ∋) arg-chks spl
        A'≤T = proj₁ (sound-≤ A≤H spl)
sound-chk (⊢a-app ⊢e) spl = sound-chk ⊢e (have spl)
sound-chk (⊢a-ann ⊢e A≤H) spl = ⊢d-sub elims A'≤T
  where arg-chks = proj₂ (sound-≤ A≤H spl)
        elims = ⊩-elim (⊢d-ann (sound-chk ⊢e none)) arg-chks spl
        A'≤T = proj₁ (sound-≤ A≤H spl)        
sound-chk (⊢a-lam₁ ⊢e) none = ⊢d-lam₁ (sound-chk ⊢e none)
sound-chk (⊢a-lam₂ ⊢e ⊢f) (have spl) = {!!}
