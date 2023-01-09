module Properties where

open import Data.Nat using (ℕ)
open import Data.String using (String)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl)
open import Data.Product using (_×_; proj₁; proj₂; ∃; ∃-syntax) renaming (_,_ to ⟨_,_⟩)

open import Common
open import Dec
open import Algo

------------ Properties of Algorithmic System ---------------

-- renaming

ext : ∀ {Γ Δ}
  → (∀ {x A} → Γ ∋ x ⦂ A → Δ ∋ x ⦂ A)
  → (∀ {x y A B} → Γ , y ⦂ B ∋ x ⦂ A → Δ , y ⦂ B ∋ x ⦂ A)
ext ρ Z           =  Z
ext ρ (S x≢y ∋x)  =  S x≢y (ρ ∋x)

rename-≤a : ∀ {Γ Δ}
  → (∀ {x A} → Γ ∋ x ⦂ A → Δ ∋ x ⦂ A)
  → (∀ {A B} → Γ ⊢a A ≤ B → Δ ⊢a A ≤ B)

rename-⊢a : ∀ {Γ Δ}
  → (∀ {x A} → Γ ∋ x ⦂ A → Δ ∋ x ⦂ A)
  → (∀ {e A B} → Γ ⊢a B ⇛ e ⇛ A → Δ ⊢a B ⇛ e ⇛ A)

rename-≤a ρ ≤a-int = ≤a-int
rename-≤a ρ ≤a-top = ≤a-top
rename-≤a ρ (≤a-arr ≤a₁ ≤a₂) = ≤a-arr (rename-≤a ρ ≤a₁) (rename-≤a ρ ≤a₂)
rename-≤a ρ (≤a-hole ⊢a) = ≤a-hole (rename-⊢a ρ ⊢a)

rename-⊢a ρ (⊢a-lit ⊢a) = ⊢a-lit (rename-≤a ρ ⊢a)
rename-⊢a ρ (⊢a-var ≤a ∋x) = ⊢a-var (ρ ≤a) (rename-≤a ρ ∋x)
rename-⊢a ρ (⊢a-app ⊢a) = ⊢a-app (rename-⊢a ρ ⊢a)
rename-⊢a ρ (⊢a-ann ⊢a ≤a) = ⊢a-ann (rename-⊢a ρ ⊢a) (rename-≤a ρ ≤a)
rename-⊢a ρ (⊢a-lam₁ ⊢a₁ ⊢a₂) = ⊢a-lam₁ (rename-⊢a ρ ⊢a₁) (rename-⊢a (ext ρ) ⊢a₂)
rename-⊢a ρ (⊢a-lam₂ ⊢a) = ⊢a-lam₂ (rename-⊢a (ext ρ) ⊢a)

weaken : ∀ {Γ e A B}
  → ∅ ⊢a B ⇛ e ⇛ A
  → Γ ⊢a B ⇛ e ⇛ A
weaken {Γ} ⊢e = rename-⊢a ρ ⊢e
  where
  ρ : ∀ {z C}
    → ∅ ∋ z ⦂ C
    → Γ ∋ z ⦂ C
  ρ = λ ()

≤a-arr-inv : ∀ {Γ A B C D}
  → Γ ⊢a A *⇒ B ≤ C *⇒ D
  → (Γ ⊢a C ≤ A) × (Γ ⊢a B ≤ D)
≤a-arr-inv (≤a-arr ≤a₁ ≤a₂) = ⟨ ≤a₁ , ≤a₂ ⟩

⊢a-to-≤a : ∀ {Γ e A B}
  → Γ ⊢a B ⇛ e ⇛ A
  → Γ ⊢a h A ≤ B
⊢a-to-≤a (⊢a-lit ≤a) = ≤a
⊢a-to-≤a (⊢a-var ∋x ≤a) = ≤a
⊢a-to-≤a (⊢a-app ⊢a) = proj₂ (≤a-arr-inv (⊢a-to-≤a ⊢a))
⊢a-to-≤a (⊢a-ann ⊢a ≤a) = ≤a
⊢a-to-≤a (⊢a-lam₁ ⊢a₁ ⊢a₂) = ≤a-arr {!!} {!!}
⊢a-to-≤a (⊢a-lam₂ ⊢a) = {!!}
  
-------------------------------------------------------------

data Normal : Hype → Set where
  nf-int :
      Normal Hnt
  nf-top :
      Normal Hop
  nf-arr : ∀ {A B}
    → Normal A
    → Normal B
    → Normal (A *⇒ B)


-- It looks like the same with previous one, nothing special
-- hole never appears in this lemma
≤a-refl : ∀ {A Γ}
  → Normal A
  → Γ ⊢a A ≤ A
≤a-refl nf-int = ≤a-int
≤a-refl nf-top = ≤a-top
≤a-refl (nf-arr nor₁ nor₂) = ≤a-arr (≤a-refl nor₁) (≤a-refl nor₂)

-- sound-chk : ∀ {Γ e A}
--   → Γ ⊢d e ∙ ⇚ ∙ A
--   → Γ ⊢a h A ⇛ e ⇛ A

-- sound : ∀ {Γ e A}
--   → Γ ⊢d e ∙ ⇛ ∙ A
--   → Γ ⊢a Hop ⇛ e ⇛ A

-- generlized to

f : Mode → Type → Type
f ⇛ A = Top
f ⇚ A = A


------------------- Lemmas for soundness ------------------
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
  → Γ ⊢d e ∙ ⇔ ∙ A
  → Γ ⊢a h (f ⇔ A) ⇛ e ⇛ A
sound ⊢d-int = ⊢a-lit ≤a-top
sound (⊢d-var x) = ⊢a-var x ≤a-top
sound (⊢d-lam ⊢d) = ⊢a-lam₂ (sound ⊢d)
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
sound (⊢d-app₁ ⊢df ⊢da) = ⊢a-app {!fun-with-hint (sound ⊢df) (sound ⊢da)!}
sound (⊢d-app₂ ⊢df ⊢da) = {!!}
sound (⊢d-ann ⊢d) = ⊢a-ann (sound ⊢d) ≤a-top
-- sub rule, the naive idea is to do case analysis, not sure
sound (⊢d-sub ⊢d ≤d) = {!!}
