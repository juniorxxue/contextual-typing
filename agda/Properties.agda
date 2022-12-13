module Properties where

open import Common
open import Dec
open import Algo

data Normal : Hype → Set where
  nf-int :
      Normal Hnt
  nf-top :
      Normal Hop
  nf-arr : ∀ {A B}
    → Normal A
    → Normal B
    → Normal (A *⇒ B)


-- It looks like the same with previous one
-- hole never appears in this lemma
≤a-refl : ∀ {A Γ}
  → Normal A
  → Γ ⊢a A ≤ A
≤a-refl = {!!}


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

sound : ∀ {Γ e A ⇔}
  → Γ ⊢d e ∙ ⇔ ∙ A
  → Γ ⊢a h (f ⇔ A) ⇛ e ⇛ A
sound = {!!}
