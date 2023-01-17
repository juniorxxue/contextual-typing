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

------------ Properties of Algorithmic System ---------------

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

≤a-refl-h : ∀ {A Γ}
  → Γ ⊢a h A ≤ h A
≤a-refl-h {A = Int} = ≤a-int
≤a-refl-h {A = Top} = ≤a-top
≤a-refl-h {A = A ⇒ A₁} = ≤a-arr ≤a-refl-h ≤a-refl-h

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
rename-⊢a ρ (⊢a-lam₁ ⊢a₁ ⊢a₂ nf) = ⊢a-lam₁ (rename-⊢a ρ ⊢a₁) (rename-⊢a (ext ρ) ⊢a₂) nf
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

--------------------- Lemmas for typing and subtyping --------

{-

Goal: Γ ⊢a h C ≤ B
Have: (Γ , x ⦂ A) ⊢a h C ≤ B
————————————————————————————————————————————————————————————
⊢a₂ : Γ , x ⦂ A ⊢a B ⇛ e ⇛ C
⊢a₁ : Γ ⊢a Hop ⇛ e₁ ⇛ A

Intuitively we know that this lemma holds, since x ⦂ A shouldn't appear in B type

1st try: fix the rule
2nd try: de bruijn or something else

-}

{-
strengthen : ∀ {Γ x A B C}
  → (Γ , x ⦂ A) ⊢a h C ≤ B
  → ¬ freeT B x
  → Γ ⊢a h C ≤ B
strengthen {B = Hnt} {C = Int} ≤ nf = ≤a-int
strengthen {B = Hop} {C = Int} ≤ nf = ≤a-top
strengthen {B = Hop} {C = Top} ≤ nf = ≤a-top
strengthen {B = .Hop} {C = C₁ ⇒ C₂} ≤a-top nf = ≤a-top
strengthen {B = .(_ *⇒ _)} {C = C₁ ⇒ C₂} (≤a-arr ≤ ≤₁) nf = ≤a-arr {!!} {!!}

the problem here is that arrow type is contra
Just notice that the free shouldn't be baised on each side
so

-}

strengthen : ∀ {Γ x A B C}
  → (Γ , x ⦂ A) ⊢a C ≤ B
  → ¬ freeT C x
  → ¬ freeT B x
  → Γ ⊢a C ≤ B
strengthen {B = Hnt} {C = Hnt} ≤ nf₁ nf₂ = ≤a-int
strengthen {B = Hop} {C = Hnt} ≤ nf₁ nf₂ = ≤a-top
strengthen {B = Hop} {C = Hop} ≤ nf₁ nf₂ = ≤a-top
strengthen {B = Hop} {C = C₁ *⇒ C₂} ≤ nf₁ nf₂ = ≤a-top
strengthen {B = B₁ *⇒ B₂} {C = C₁ *⇒ C₂} (≤a-arr ≤₁ ≤₂) nf₁ nf₂ = ≤a-arr (strengthen ≤₁ {!!} {!!}) (strengthen ≤₂ {!!} {!!}) -- trivial
strengthen {C = ⟦ x ⟧} ≤ nf₁ nf₂ = {!!}

{-
Goal: Γ ⊢a Hnt ⇛ x ⇛ _B_656
————————————————————————————————————————————————————————————
nf₂ : ¬ freeT Hnt x₂
nf₁ : ¬ freeT ⟦ x ⟧ x₂
x₁  : Γ , x₂ ⦂ A ⊢a Hnt ⇛ x ⇛ B
-}

-- it looks like we need a strengthen lemma for typing
⊢a-strengthen : ∀ {Γ e x A B C}
  → (Γ , x ⦂ A) ⊢a B ⇛ e ⇛ C
  → ¬ free e x
  → ¬ freeT B x
  → Γ ⊢a B ⇛ e ⇛ C
⊢a-strengthen = {!!}

⊢a-to-≤a : ∀ {Γ e A B}
  → Γ ⊢a B ⇛ e ⇛ A
  → Γ ⊢a h A ≤ B
⊢a-to-≤a (⊢a-lit ≤a) = ≤a
⊢a-to-≤a (⊢a-var ∋x ≤a) = ≤a
⊢a-to-≤a (⊢a-app ⊢a) = proj₂ (≤a-arr-inv (⊢a-to-≤a ⊢a))
⊢a-to-≤a (⊢a-ann ⊢a ≤a) = ≤a
⊢a-to-≤a (⊢a-lam₁ ⊢a₁ ⊢a₂ nf) = ≤a-arr (≤a-hole {!!}) {!⊢a-to-≤a ⊢a₂!}
⊢a-to-≤a (⊢a-lam₂ ⊢a) = ≤a-arr ≤a-refl-h {!⊢a-to-≤a ⊢a!}

------------------- Lemmas for sound/complete ------------------


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
-- we can infer the same thing with the extra hint (arguments

--------------------- Lemmas for algo typing -----------------

-- Two lemmas should be unified


⊢a-hint-self : ∀ {Γ A e}
  → Γ ⊢a Hop ⇛ e ⇛ A
  → Γ ⊢a h A ⇛ e ⇛ A
  
-- this is wrong, apparently

{-
Goal: Γ ⊢a ⟦ e₂ ⟧ *⇒ (B *⇒ h A) ⇛ e₁ ⇛ C₁ ⇒ (C ⇒ A)
————————————————————————————————————————————————————————————
⊢a :  Γ ⊢a ⟦ e₂ ⟧ *⇒ (B *⇒ Hop) ⇛ e₁ ⇛ C₁ ⇒ (C ⇒ A)
-}

⊢a-hint-self-1 : ∀ {Γ A B C e}
  → Γ ⊢a (B *⇒ Hop) ⇛ e ⇛ (C ⇒ A)
  → Γ ⊢a (B *⇒ h A) ⇛ e ⇛ (C ⇒ A)

⊢a-hint-self (⊢a-lit ≤) = ⊢a-lit ≤a-int
⊢a-hint-self (⊢a-var ∋ ≤) = ⊢a-var ∋ ≤a-refl-h
⊢a-hint-self (⊢a-app ⊢a) = ⊢a-app (⊢a-hint-self-1 ⊢a)
⊢a-hint-self (⊢a-ann ⊢a ≤) = ⊢a-ann ⊢a ≤a-refl-h
