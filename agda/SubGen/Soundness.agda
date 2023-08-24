module SubGen.Soundness where

open import SubGen.Prelude
open import SubGen.Common
open import SubGen.Decl
open import SubGen.Decl.Properties
open import SubGen.Algo
open import SubGen.Algo.Properties


-- j represents the length of H
len : Hint → Counter
len (τ Int) = ∞
len (τ (* n)) = ∞
len (τ Top) = c 0
len (τ (x ⇒ x₁)) = ∞
len (τ (x & x₁)) = ∞
len (⟦ x ⟧⇒ H) = succ (len H)

sound-≤ : ∀ {Γ A H A'}
  → Γ ⊢a A ≤ H ⇝ A'
  → A ≤d (len H) # A'
sound-≤ ≤a-int = ≤d-int∞
sound-≤ ≤a-base = ≤d-base∞
sound-≤ ≤a-top = ≤d-refl wf-0
sound-≤ (≤a-arr {A = A} {D = D} C≤A B≤D) with A | D
... | Top | Top = ≤d-arr∞ ≤d-top {!!}

sound-≤ (≤a-hint ⊢e A≤H) = {!!}
sound-≤ (≤a-and-l A≤H) = ≤d-and₁ (sound-≤ A≤H)
sound-≤ (≤a-and-r A≤H) = ≤d-and₂ (sound-≤ A≤H)
sound-≤ (≤a-and A≤C A≤B) = ≤d-and {!!} {!!}

infix 4 _⊩_⇚_
data _⊩_⇚_ : Context → List Term → List Type → Set where
  ⊩none⇚ : ∀ {Γ}
    → Γ ⊩ [] ⇚ []

  ⊩cons⇚ : ∀ {Γ es As e A}
    → Γ ⊩ es ⇚ As
    → Γ ⊢d ∞ # e ⦂ A
    → Γ ⊩ (e ∷ es) ⇚ (A ∷ As)

⊩-elim : ∀ {Γ e H A es T As A'}
  → Γ ⊢d c 0 # e ⦂ A
  → Γ ⊩ es ⇚ As
  → ❪ H , A ❫↣❪ es , T , As , A' ❫ 
  → Γ ⊢d c 0 # e ▻ es ⦂ A'
⊩-elim ⊢d ⊩empty⇚ none = ⊢d
⊩-elim ⊢d (⊩cons⇚ ⊩es ⊢e) (have spl) = ⊩-elim (⊢d-app₁ ⊢d ⊢e) ⊩es spl

infix 4 _⊩_⇛_
data _⊩_⇛_ : Context → List Term → List Type → Set where
  ⊩none⇛ : ∀ {Γ}
    → Γ ⊩ [] ⇛ []

  ⊩cons⇛ : ∀ {Γ es As e A}
    → Γ ⊩ es ⇛ As
    → Γ ⊢d c 0 # e ⦂ A
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

{-

subst :  ∀ {Γ A B e e₁ n} (es : List Term)
  → Γ , A ⊢d c n # e ▻ map (_↑ 0) es ⦂ B
  → Γ ⊢d c 0 # e₁ ⦂ A
  → Γ ⊢d c n # ((ƛ e) · e₁) ▻ es ⦂ B

subst es = rev (λ es → ∀ {Γ} {A} {B} {e} {e₁} {n}
                     → Γ , A ⊢d c n # e ▻ map (_↑ 0) es ⦂ B
                     → Γ ⊢d c 0 # e₁ ⦂ A
                     → Γ ⊢d c n # ((ƛ e) · e₁) ▻ es ⦂ B)
                     (λ ⊢e₁ ⊢e₂ → ⊢d-app₂ (⊢d-lam₂ ⊢e₁) ⊢e₂)
                     (λ e' es' IH ⊢e₁ ⊢e₂ → rewrite-snoc₂ {es' = es'} (case (rewrite-snoc₁ {es' = es'} ⊢e₁) of λ
                     {(⊢d-app₁ ⊢1 ⊢2) → ⊢d-app₁ (IH ⊢1 ⊢e₂) (⊢d-strengthen-0 ⊢2)
                     ;(⊢d-app₂ ⊢1 ⊢2) → ⊢d-app₂ (IH ⊢1 ⊢e₂) (⊢d-strengthen-0 ⊢2)
                     ;(⊢d-sub ⊢1 A≤B) → {!!}
                     })) -- ind
                     es

subst-chk :  ∀ {Γ A B e e₁} (es : List Term)
  → Γ , A ⊢d ∞ # e ▻ map (_↑ 0) es ⦂ B
  → Γ ⊢d c 0 # e₁ ⦂ A
  → Γ ⊢d ∞ # ((ƛ e) · e₁) ▻ es ⦂ B

subst-chk es = rev (λ es → ∀ {Γ} {A} {B} {e} {e₁}
                         → Γ , A ⊢d ∞ # e ▻ map (_↑ 0) es ⦂ B
                         → Γ ⊢d c 0 # e₁ ⦂ A
                         → Γ ⊢d ∞ # ((ƛ e) · e₁) ▻ es ⦂ B)
                         (λ ⊢e₁ ⊢e₂ → ⊢d-app₃ (⊢d-lam₁ ⊢e₁) ⊢e₂)
                         (λ e' es' IH ⊢e₁ ⊢e₂ → rewrite-snoc₂ {es' = es'} (case (rewrite-snoc₁ {es' = es'} ⊢e₁) of λ
                         { (⊢d-app₃ ⊢1 ⊢2) → ⊢d-app₃ (IH ⊢1 ⊢e₂) (⊢d-strengthen-0 ⊢2)
                         ; (⊢d-sub ⊢1 A≤B) → ⊢d-sub (rewrite-snoc₃ {es' = es'} (subst (es' ++ e' ∷ []) (rewrite-snoc₄ {es' = es'} ⊢1) ⊢e₂)) A≤B
                         }))
                         es


subst-base : ∀ {Γ A B e₁ e₂ ∞/n}
  → Γ , A ⊢d ∞/n # e₁ ⦂ B
  → Γ ⊢d c 0 # e₂ ⦂ A
  → Γ ⊢d ∞/n # (ƛ e₁) · e₂ ⦂ B
subst-base {∞/n = ∞} ⊢e₁ ⊢e₂ = ⊢d-app₃ (⊢d-lam₁ ⊢e₁) ⊢e₂
subst-base {∞/n = c n} ⊢e₁ ⊢e₂ = ⊢d-app₂ (⊢d-lam₂ ⊢e₁) ⊢e₂
                         
subst-gen : ∀ {Γ A B e e₁ ∞/n} (es : List Term)
  → Γ , A ⊢d ∞/n # e ▻ map (_↑ 0) es ⦂ B
  → Γ ⊢d c 0 # e₁ ⦂ A
  → Γ ⊢d ∞/n # ((ƛ e) · e₁) ▻ es ⦂ B
subst-gen es = rev (λ es → ∀ {Γ} {A} {B} {e} {e₁} {∞/n}
                         → Γ , A ⊢d ∞/n # e ▻ map (_↑ 0) es ⦂ B
                         → Γ ⊢d c 0 # e₁ ⦂ A
                         → Γ ⊢d ∞/n # ((ƛ e) · e₁) ▻ es ⦂ B)
                   (λ ⊢e₁ ⊢e₂ → subst-base ⊢e₁ ⊢e₂)
                   (λ e' es' IH ⊢e₁ ⊢e₂ → rewrite-snoc₂ {es' = es'} (case (rewrite-snoc₁ {es' = es'} ⊢e₁) of λ
                   { (⊢d-app₁ ⊢1 ⊢2) → {!!}
                   ; (⊢d-app₂ ⊢1 ⊢2) → {!!}
                   ; (⊢d-app₃ ⊢1 ⊢2) → {!!}
                   ; (⊢d-sub ⊢1 A≤B) → ⊢d-sub {!!} A≤B
                   }
                   ))
                   es


sound-≤ : ∀ {Γ H A B es T As A' ∞/n}
  → Γ ⊢a A ≤ H ⇝ B
  → ❪ H , A ❫↣❪ es , T , As , A' ❫
  → (A' ≤d ∞/n # T) × (Γ ⊩ es ⇚ As)

sound-inf : ∀ {Γ e H A es As A'}
  → Γ ⊢a H ⇛ e ⇛ A
  → ❪ H , A ❫↣❪ es , Top , As , A' ❫
  → Γ ⊢d c 0 # e ▻ es ⦂ A'

sound-chk : ∀ {Γ e H A es T As A'}
  → Γ ⊢a H ⇛ e ⇛ A
  → ❪ H , A ❫↣❪ es , T , As , A' ❫
  → Γ ⊢d ∞ # e ▻ es ⦂ T

sound-≤ A≤H spl = {!!}

sound-inf ⊢a-lit none = ⊢d-int
sound-inf (⊢a-var x∈Γ) none = ⊢d-var x∈Γ
sound-inf (⊢a-app ⊢e) spl = sound-inf ⊢e (have spl)
sound-inf (⊢a-ann ⊢e) none = ⊢d-ann (sound-chk ⊢e none)
sound-inf {es = e ∷ es} (⊢a-lam₂ ⊢e ⊢f) (have spl) = subst-gen es (sound-inf ⊢f (spl-weaken spl)) (sound-inf ⊢e none)
sound-inf (⊢a-sub pv ⊢e A≤H) spl = {!!}

sound-chk ⊢e spl = {!!}

-}
