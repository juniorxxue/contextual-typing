module Poly.Decl.Properties where

open import Poly.Common
open import Poly.Decl

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
