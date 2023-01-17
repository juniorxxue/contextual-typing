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


-- complete-chk : ∀ {Γ e A}
--   → Γ ⊢d e ∙ ⇚ ∙ A
--   → Γ ⊢a h A ⇛ e ⇛ A

-- complete : ∀ {Γ e A}
--   → Γ ⊢d e ∙ ⇛ ∙ A
--   → Γ ⊢a Hop ⇛ e ⇛ A

-- generlized to

f : Mode → Type → Type
f ⇛ A = Top
f ⇚ A = A

{-
fun-with-hint : ∀ {Γ e₁ e₂ A B}
  → Γ ⊢a Hop ⇛ e₁ ⇛ A ⇒ B
  → Γ ⊢a h A ⇛ e₂ ⇛ A
  → ∃[ C ] Γ ⊢a ⟦ e₂ ⟧ *⇒ Hop ⇛ e₁ ⇛ C ⇒ B
fun-with-hint {A = A} (⊢a-var x x₁) ⊢a = ⟨ A , ⊢a-var x (≤a-arr (≤a-hole ⊢a) ≤a-top) ⟩
fun-with-hint (⊢a-app ⊢f) ⊢a = {!!}
fun-with-hint (⊢a-ann ⊢f x) ⊢a = {!!}
-}

-- maybe the existential C is fixed for A

fun-with-hint : ∀ {Γ e₁ e₂ A B}
  → Γ ⊢a Hop ⇛ e₁ ⇛ A ⇒ B
  → Γ ⊢a h A ⇛ e₂ ⇛ A
  → Γ ⊢a ⟦ e₂ ⟧ *⇒ Hop ⇛ e₁ ⇛ A ⇒ B
fun-with-hint (⊢a-var x x₁) ⊢a = ⊢a-var x (≤a-arr (≤a-hole ⊢a) ≤a-top)
fun-with-hint (⊢a-app ⊢f) ⊢a = {!!}
fun-with-hint (⊢a-ann ⊢f x) ⊢a = ⊢a-ann ⊢f (≤a-arr (≤a-hole ⊢a) ≤a-top)

-- generlize a bit

fun-with-hint1 : ∀ {Γ e₁ e₂ A B}
  → Γ ⊢a Hop ⇛ e₁ ⇛ A ⇒ B
  → Γ ⊢a h A ⇛ e₂ ⇛ A
  → Γ ⊢a Hop ⇛ e₁ · e₂ ⇛ B
fun-with-hint1 (⊢a-var x x₁) ⊢a = ⊢a-app (⊢a-var x (≤a-arr (≤a-hole ⊢a) ≤a-top))
fun-with-hint1 (⊢a-app ⊢f) ⊢a = ⊢a-app {!!}
fun-with-hint1 (⊢a-ann ⊢f x) ⊢a = ⊢a-app (⊢a-ann ⊢f (≤a-arr (≤a-hole ⊢a) ≤a-top))

-----------------------------------------------------------

sound : ∀ {Γ e A ⇔}
  → Γ ⊢a h (f ⇔ A) ⇛ e ⇛ A
  → Γ ⊢d e ∙ ⇔ ∙ A
sound ⊢a = {!!}
-- ? 

complete : ∀ {Γ e A ⇔}
  → Γ ⊢d e ∙ ⇔ ∙ A
  → Γ ⊢a h (f ⇔ A) ⇛ e ⇛ A
complete ⊢d-int = ⊢a-lit ≤a-top
complete (⊢d-var x) = ⊢a-var x ≤a-top
complete (⊢d-lam ⊢d) = ⊢a-lam₂ (complete ⊢d)
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
complete (⊢d-app₁ ⊢df ⊢da) = ⊢a-app {!fun-with-hint (complete ⊢df) (complete ⊢da)!}
complete (⊢d-app₂ (⊢d-lam ⊢df) ⊢da) = ⊢a-app (⊢a-lam₁ (complete ⊢da) {!complete ⊢df!} {!!})
complete (⊢d-app₂ (⊢d-sub ⊢df ≤d) ⊢da) = ⊢a-app {!!}
complete (⊢d-ann ⊢d) = ⊢a-ann (complete ⊢d) ≤a-top
-- sub rule, the naive idea is to do case analysis, not sure
complete (⊢d-sub ⊢d ≤d) = {!!}

output : Hype → Hype
output Hop = Hop
output (A *⇒ B) = B
output _ = Hop

fun-with-hint2 : ∀ {Γ e₁ e₂ A B C}
  → Γ ⊢a C ⇛ e₁ ⇛ A ⇒ B
  → Γ ⊢a h A ⇛ e₂ ⇛ A
  → Γ ⊢a ⟦ e₂ ⟧ *⇒ output C ⇛ e₁ ⇛ A ⇒ B
fun-with-hint2 (⊢a-var x x₁) ⊢a = ⊢a-var x (≤a-arr (≤a-hole ⊢a) {!!})
fun-with-hint2 (⊢a-app ⊢f) ⊢a = ⊢a-app {! !}
fun-with-hint2 (⊢a-ann ⊢f x) ⊢a = {!!}
fun-with-hint2 (⊢a-lam₁ ⊢f ⊢f₁ nf) ⊢a = {!!}
fun-with-hint2 (⊢a-lam₂ ⊢f) ⊢a = {!!}

-- in application
-- if we know nothing (Top)
-- we can infer the same thing with the extra hint (argument
