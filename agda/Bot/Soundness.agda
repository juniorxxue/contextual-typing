module Bot.Soundness where

open import Bot.Prelude
open import Bot.Common
open import Bot.Dec
open import Bot.Dec.Properties
open import Bot.Algo
open import Bot.Algo.Properties

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

f : Type → Term
f Int = lit 1
f Top = lit 1
f (A ⇒ A₁) = ƛ (f A₁)

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

rewrite-snoc₄ : ∀ {Γ e e' es' A cc}
  → Γ ⊢d cc ╏ (e ▻ map (_↑ 0) es') · (e' ↑ 0) ⦂ A
  → Γ ⊢d cc ╏ e ▻ map (_↑ 0) (es' ++ e' ∷ []) ⦂ A
rewrite-snoc₄ {e = e} {e' = e'} {es' = es'} ⊢e rewrite ▻snoc₁ e e' es' = ⊢e

▻snoc₂ : ∀ e es' e'
  → e ▻ (es' ++ e' ∷ []) ≡  (e ▻ es') · e'
▻snoc₂ e [] e' = refl
▻snoc₂ e (x ∷ es') e' = ▻snoc₂ (e · x) es' e'

rewrite-snoc₂ : ∀ {Γ e e₁ es' e' cc B}
  → Γ ⊢d cc ╏ (((ƛ e) · e₁) ▻ es') · e' ⦂ B
  → Γ ⊢d cc ╏ ((ƛ e) · e₁) ▻ (es' ++ e' ∷ []) ⦂ B
rewrite-snoc₂ {e = e} {e₁ = e₁} {es' = es'} {e' = e'} ⊢e rewrite ▻snoc₂ ((ƛ e) · e₁) es' e' = ⊢e

rewrite-snoc₃ : ∀ {Γ e e₁ es' e' cc B}
  → Γ ⊢d cc ╏ ((ƛ e) · e₁) ▻ (es' ++ e' ∷ []) ⦂ B
  → Γ ⊢d cc ╏ (((ƛ e) · e₁) ▻ es') · e' ⦂ B
rewrite-snoc₃ {e = e} {e₁ = e₁} {es' = es'} {e' = e'} ⊢e rewrite ▻snoc₂ ((ƛ e) · e₁) es' e' = ⊢e  

subst :  ∀ {Γ A B e e₁ n} (es : List Term)
  → Γ , A ⊢d c n ╏ e ▻ map (_↑ 0) es ⦂ B
  → Γ ⊢d c 0 ╏ e₁ ⦂ A
  → Γ ⊢d c n ╏ ((ƛ e) · e₁) ▻ es ⦂ B

subst es = rev (λ es → ∀ {Γ} {A} {B} {e} {e₁} {n}
                     → Γ , A ⊢d c n ╏ e ▻ map (_↑ 0) es ⦂ B
                     → Γ ⊢d c 0 ╏ e₁ ⦂ A
                     → Γ ⊢d c n ╏ ((ƛ e) · e₁) ▻ es ⦂ B)
                     (λ ⊢e₁ ⊢e₂ → ⊢d-app₂ (⊢d-lam₂ ⊢e₁) ⊢e₂)
                     (λ e' es' IH ⊢e₁ ⊢e₂ → rewrite-snoc₂ {es' = es'} (case (rewrite-snoc₁ {es' = es'} ⊢e₁) of λ
                     {(⊢d-app₁ ⊢1 ⊢2) → ⊢d-app₁ (IH ⊢1 ⊢e₂) (⊢d-strengthen-0 ⊢2)
                     ;(⊢d-app₂ ⊢1 ⊢2) → ⊢d-app₂ (IH ⊢1 ⊢e₂) (⊢d-strengthen-0 ⊢2)
                     })) -- ind
                     es

subst-chk :  ∀ {Γ A B e e₁} (es : List Term)
  → Γ , A ⊢d ∞ ╏ e ▻ map (_↑ 0) es ⦂ B
  → Γ ⊢d c 0 ╏ e₁ ⦂ A
  → Γ ⊢d ∞ ╏ ((ƛ e) · e₁) ▻ es ⦂ B

subst-chk es = rev (λ es → ∀ {Γ} {A} {B} {e} {e₁}
                         → Γ , A ⊢d ∞ ╏ e ▻ map (_↑ 0) es ⦂ B
                         → Γ ⊢d c 0 ╏ e₁ ⦂ A
                         → Γ ⊢d ∞ ╏ ((ƛ e) · e₁) ▻ es ⦂ B)
                         (λ ⊢e₁ ⊢e₂ → ⊢d-app₃ (⊢d-lam₁ ⊢e₁) ⊢e₂)
                         (λ e' es' IH ⊢e₁ ⊢e₂ → rewrite-snoc₂ {es' = es'} (case (rewrite-snoc₁ {es' = es'} ⊢e₁) of λ
                         { (⊢d-app₃ ⊢1 ⊢2) → ⊢d-app₃ (IH ⊢1 ⊢e₂) (⊢d-strengthen-0 ⊢2)
                         ; (⊢d-sub ⊢1 A≤B) → ⊢d-sub (rewrite-snoc₃ {es' = es'} (subst (es' ++ e' ∷ []) (rewrite-snoc₄ {es' = es'} ⊢1) ⊢e₂)) A≤B
                         }))
                         es


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
sound-inf {es = e ∷ es} (⊢a-lam₂ ⊢e ⊢f) (have spl) = subst es (sound-inf ⊢f (spl-weaken spl)) (sound-inf ⊢e none)

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
sound-chk {es = e ∷ es} (⊢a-lam₂ ⊢e ⊢f) (have spl) = subst-chk es (sound-chk ⊢f (spl-weaken spl)) (sound-inf ⊢e none)
