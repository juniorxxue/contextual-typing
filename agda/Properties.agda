module Properties where

open import Data.Nat using (ℕ)
open import Data.String using (String)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl)
open import Data.Product using (_×_; proj₁; proj₂; ∃; ∃-syntax) renaming (_,_ to ⟨_,_⟩)
open import Data.Empty using (⊥; ⊥-elim)
open import Relation.Nullary using (¬_)

open import Common
open import Dec
open import Algo

----------------------------------------------------------------------
--+                                                                +--
--+                           Soundness                            +--
--+                                                                +--
----------------------------------------------------------------------

sound₁ : ∀ {Γ e A B}
  → Γ ⊢a A ⇛ e ⇛ B
  → Γ ⊢d e ∙ ⇚ ∙ B
sound₁ (⊢a-lit ≤) = ⊢d-sub ⊢d-int ≤d-int
sound₁ (⊢a-var ∋ ≤) = ⊢d-sub (⊢d-var ∋) ≤d-refl
{-
==>lam1   1 ⇒ Int
==>app  [1] → Top ⇒ (λx. x) ⇒ Int → Int
∅ ⊢ Top ⇒ (λx. x) 1 ⇒ Int
----------------------------
∅ ⊢ (λx. x) 1 ⇐ Int
<==sub   (λx. x) 1 ⇒ Int    Int ≤ Int
<==app2  (λx. x) ⇐ Int → Int   1 ⇒ Int
-}
sound₁ (⊢a-app ⊢a) = {!!}
sound₁ (⊢a-ann ⊢a x) = ⊢d-sub (⊢d-ann (sound₁ ⊢a)) ≤d-refl
sound₁ (⊢a-lam₁ ⊢a₁ ⊢a₂ ⊨) = ⊢d-lam (sound₁ ⊢a₂)
sound₁ (⊢a-lam₂ ⊢a ⊨) = ⊢d-lam (sound₁ ⊢a)

sound₂ : ∀ {Γ e A}
  → Γ ⊢a Hop ⇛ e ⇛ A
  → Γ ⊢d e ∙ ⇛ ∙ A
sound₂ ⊢a = {!!}

----------------------------------------------------------------------
--+                                                                +--
--+                          Completeness                          +--
--+                                                                +--
----------------------------------------------------------------------

f : Mode → Type → Type
f ⇛ A = Top
f ⇚ A = A

output : Hype → Hype
output Hop = Hop
output (A *⇒ B) = B
output _ = Hop

≤a-output : ∀ {Γ A B C}
  → Γ ⊢a h A *⇒ h B ≤ C
  → Γ ⊢a h B ≤ output C
≤a-output ≤a-top = ≤a-top
≤a-output (≤a-arr ≤₁ ≤₂) = ≤₂


-- this is a wrong lemma
fun-hint : ∀ {Γ e₁ e₂ A B C}
  → Γ ⊢a C ⇛ e₁ ⇛ A ⇒ B
  → Γ ⊢a h A ⇛ e₂ ⇛ A
  → Γ ⊢a ⟦ e₂ ⟧ *⇒ output C ⇛ e₁ ⇛ A ⇒ B
fun-hint (⊢a-var ∋ ≤) ⊢₂ = ⊢a-var ∋ (≤a-arr (≤a-hole ⊢₂) (≤a-output ≤))
fun-hint (⊢a-app ⊢₁) ⊢₂ = {!!}
fun-hint (⊢a-ann ⊢₁ x) ⊢₂ = {!!}
fun-hint (⊢a-lam₁ ⊢₁ ⊢₃ ⊨) ⊢₂ = {!!}
fun-hint (⊢a-lam₂ ⊢₁ ⊨) ⊢₂ = {!!}

complete : ∀ {Γ e A ⇔}
  → Γ ⊢d e ∙ ⇔ ∙ A
  → Γ ⊢a h (f ⇔ A) ⇛ e ⇛ A
complete ⊢d-int = ⊢a-lit ≤a-top
complete (⊢d-var x) = ⊢a-var x ≤a-top
complete (⊢d-lam ⊢d) = ⊢a-lam₂ (complete ⊢d) {!!}
-- app rules require some intuition

{-
G |- Top => e1 => A -> B
G |- A => e2 => A
-----------------------------
[e2] -> Top => e1 => ? -> B

Two observations:
1. Whatever hint is given, the output type B is preseved
2. Given a hint, the e1 will infer more precise type (?)

1st try:
abstract a lemma out of here
-}
complete (⊢d-app₁ ⊢df ⊢da) = ⊢a-app {!fun-hint (complete ⊢df) (complete ⊢da)!}
complete (⊢d-app₂ (⊢d-lam ⊢df) ⊢da) = ⊢a-app (⊢a-lam₁ (complete ⊢da) {!complete ⊢df!} {!!})
complete (⊢d-app₂ (⊢d-sub ⊢df ≤d) ⊢da) = ⊢a-app {!!}
complete (⊢d-ann ⊢d) = ⊢a-ann (complete ⊢d) ≤a-top
-- sub rule, the naive idea is to do case analysis, not sure
complete (⊢d-sub ⊢d ≤d) = {!!}

-- in application
-- if we know nothing (Top)
-- we can infer the same thing with the extra hint (argument
