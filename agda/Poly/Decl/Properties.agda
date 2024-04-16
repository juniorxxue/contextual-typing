module Poly.Decl.Properties where

open import Poly.Common
open import Poly.Decl



_↑ᵗ_ : ∀ (Γ : Env n m) -> (k : Fin (1 + m)) → Env n (1 + m)
Γ ↑ᵗ #0 = Γ ,∙
Γ ↑ᵗ #S k = {!   !}

_↑ᵉ[_]_ : ∀ (Γ : Env n m) → Type m -> (k : Fin (1 + n)) → Env (1 + n) m
Γ ↑ᵉ[ e ] k = {!   !}

----------------------------------------------------------------------
--+                           Subtyping                            +--
----------------------------------------------------------------------

s-trans : ∀ {Γ : Env n m} {A B C j}
  → Γ ⊢ j # A ≤ B
  → Γ ⊢ j # B ≤ C
  → Γ ⊢ j # A ≤ C
s-trans {B = Int} (s-refl ap) s2 = {!!}
s-trans {B = Int} s-int s2 = {!!}
s-trans {B = Int} (s-∀l s1) s2 = {!!}
s-trans {B = Int} (s-∀lτ s1) s2 = {!!}
s-trans {B = Int} (s-var-l x s1) s2 = {!!}

s-trans {B = ‶ X} s1 s2 = {!!}
s-trans {B = B `→ B₁} s1 s2 = {!!}
s-trans {B = `∀ B} s1 s2 = {!!}
{-
s-trans {B = Int} (s-refl ap) (s-refl slv-int) = s-refl ap
s-trans {B = Int} (s-refl ap) (s-var-r x₁ s2) = {!!}

s-trans {B = Int} s-int s2 = s2
s-trans {B = Int} (s-∀l s1) s2 = {!!}
s-trans {B = Int} (s-∀lτ s1) s2 = {!!}
s-trans {B = Int} (s-var-l x s1) s2 = {!!}

s-trans {B = ‶ X} s1 s2 = {!!}
s-trans {B = B₁ `→ B₂} s1 s2 = {!!}
s-trans {B = `∀ B} s1 s2 = {!!}
-}
