module Poly.Decl.Properties where

open import Poly.Common
open import Poly.Decl

{-

_↑ᵗ_ : ∀ (Γ : Env n m) -> (k : Fin (1 + m)) → Env n (1 + m)
Γ ↑ᵗ #0 = Γ ,∙
Γ ↑ᵗ #S k = {!   !}

_↑ᵉ[_]_ : ∀ (Γ : Env n m) → Type m -> (k : Fin (1 + n)) → Env (1 + n) m
Γ ↑ᵉ[ e ] k = {!   !}

-}

-- the needed lemmas
-- will do later
postulate
  strengthen-0 : ∀ {Γ : Env n m} {j A B e}
    → Γ , A ⊢ j # ↑tm0 e ⦂ B
    → Γ ⊢ j # e ⦂ B

  ⊢sub' : ∀ {Γ : Env n m} {e A B j}
    → Γ ⊢ Z # e ⦂ B
    → Γ ⊢ j # B ≤ A
    → Γ ⊢ j # e ⦂ A

  s-weaken-tm-0 : ∀ {Γ : Env n m} {A B C j}
    → Γ , A ⊢ j # B ≤ C
    → Γ ⊢ j # B ≤ C

----------------------------------------------------------------------
--+                           Weakening                            +--
----------------------------------------------------------------------


_/ˣ_ : Env (1 + n) m → Fin (1 + n) → Env n m
(Γ , A) /ˣ #0 = Γ
(Γ ,∙) /ˣ #0 = (Γ /ˣ #0) ,∙
(Γ ,= A) /ˣ #0 = (Γ /ˣ #0) ,∙
_/ˣ_ {suc n} (Γ , A) (#S k) = (Γ /ˣ k) , A
(Γ ,∙) /ˣ #S k = (Γ /ˣ #S k) ,∙
(Γ ,= A) /ˣ #S k = (Γ /ˣ #S k) ,= A

{-
-- seems tricky to define, in a safe way
(∅ , A) /ˣ k = {!!}
(Γ , A , B) /ˣ k = {!!}
(Γ ,∙ , A) /ˣ k = {!!}
(Γ ,= A , B) /ˣ k = {!!}

(Γ ,∙) /ˣ k = {!!}
(Γ ,= A) /ˣ k = {!!}
-}
lookup-weaken : ∀ {Γ : Env (1 + n) m} {k x}
  → lookup (Γ /ˣ k) x ≡ lookup Γ (punchIn k x)
lookup-weaken = {!   !}

s-weaken : ∀ {Γ : Env (1 + n) m} {k j A B }
  → Γ /ˣ k ⊢ j # A ≤ B
  → Γ ⊢ j # A ≤ B
s-weaken (s-refl ap) = s-refl {!   !}
s-weaken s-int = s-int
s-weaken s-var = s-var
s-weaken (s-arr₁ B≤D C≤A) = {!   !}
s-weaken (s-arr₂ A≤B A≤B₁) = {!   !}
s-weaken (s-∀ A≤B) = {!   !}
s-weaken (s-∀l A≤B) = {!   !}
s-weaken (s-∀lτ A≤B) = {!   !}
s-weaken (s-var-l x A≤B) = {!   !}
s-weaken (s-var-r x A≤B) = {!   !}

weaken : ∀ {Γ : Env (1 + n) m} {k j e A}
  → Γ /ˣ k ⊢ j # e ⦂ A
  → Γ ⊢ j # ↑tm k e ⦂ A
weaken ⊢lit = ⊢lit
weaken {k = k} (⊢var {x = x} refl) = {!   !}
weaken (⊢ann e⇔A) = ⊢ann (weaken e⇔A)
weaken (⊢lam₁ e⇔A) = ⊢lam₁ (weaken e⇔A)
weaken (⊢lam₂ e⇔A) = ⊢lam₂ (weaken e⇔A)
weaken (⊢app₁ e₁⇔A e₂⇔A) = ⊢app₁ (weaken e₁⇔A) (weaken e₂⇔A)
weaken (⊢app₂ e₁⇔A e₂⇔A) = ⊢app₂ (weaken e₁⇔A) (weaken e₂⇔A)
weaken (⊢sub e⇔A B≤A j≢Z) = ⊢sub (weaken e⇔A) (s-weaken B≤A)  j≢Z
weaken (⊢tabs₁ e⇔A) = ⊢tabs₁ (weaken {!   !})
weaken (⊢tapp e⇔A) = ⊢tapp (weaken e⇔A)

weaken-0 : ∀ {Γ : Env (1 + n) m} {j e A}
  → Γ ⊢ j # e ⦂ A
  → Γ , A ⊢ j # ↑tm0 e ⦂ A
weaken-0 {Γ = Γ} {A = A} ⊢e = weaken {Γ = Γ , A} {k = #0} {!⊢e!}

----------------------------------------------------------------------
--+                           Subtyping                            +--
----------------------------------------------------------------------
{-
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
-}
