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
_/ˣ_ {suc n} (Γ , A) (#S k) = (Γ /ˣ k) , A
(Γ ,∙) /ˣ k = (Γ /ˣ k) ,∙
(Γ ,= A) /ˣ k = (Γ /ˣ k) ,= A

∈-weaken : ∀ {Γ : Env (1 + n) m} {k X B}
  → X := B ∈ (Γ /ˣ k)
  → X := B ∈ Γ
∈-weaken {m = suc m} {Γ = Γ , A} {#0} ∈Γ = S, ∈Γ
∈-weaken {suc n} {m = suc m} {Γ = Γ , A} {#S k} (S, ∈Γ) = S, (∈-weaken ∈Γ)
∈-weaken {Γ = _,∙ {m = zero} Γ} (S∙ {k = ()} ∈Γ)
∈-weaken {Γ = _,∙ {m = suc m} Γ} (S∙ ∈Γ) = S∙ (∈-weaken ∈Γ)
∈-weaken {Γ = Γ ,= A} {B = B} (S= ∈Γ) = S= (∈-weaken ∈Γ)
∈-weaken {m = suc m} {Γ ,= A} {X = #0} Z = Z

lookup-weaken : ∀ {Γ : Env (1 + n) m} {k x}
  → lookup (Γ /ˣ k) x ≡ lookup Γ (punchIn k x)
lookup-weaken {Γ = Γ , A} {k = #0} {x = #0} = refl
lookup-weaken {Γ = Γ ,∙} {k = #0} {x = #0} = cong ↑ty0 (lookup-weaken {Γ = Γ})
lookup-weaken {Γ = Γ ,= A} {k = #0} {x = #0} = cong ↑ty0 (lookup-weaken {Γ = Γ})
lookup-weaken {Γ = Γ , A} {k = #S k} {x = #0} = refl
lookup-weaken {Γ = Γ ,∙} {k = #S k} {x = #0} = cong ↑ty0 (lookup-weaken {Γ = Γ})
lookup-weaken {Γ = Γ ,= A} {k = #S k} {x = #0} = cong ↑ty0 (lookup-weaken {Γ = Γ})
lookup-weaken {Γ = Γ , A} {k = #0} {x = #S x} = refl
lookup-weaken {Γ = Γ ,∙} {k = #0} {x = #S x} = cong ↑ty0 (lookup-weaken {Γ = Γ})
lookup-weaken {Γ = Γ ,= A} {k = #0} {x = #S x} = cong ↑ty0 (lookup-weaken {Γ = Γ})
lookup-weaken {Γ = Γ , A} {k = #S k} {x = #S x} = lookup-weaken {Γ = Γ} {k = k} {x = x}
lookup-weaken {Γ = Γ ,∙} {k = #S k} {x = #S x} = cong ↑ty0 (lookup-weaken {Γ = Γ})
lookup-weaken {Γ = Γ ,= A} {k = #S k} {x = #S x} = cong ↑ty0 (lookup-weaken {Γ = Γ})

slv'-weaken : ∀ {Γ : Env (1 + n) m} {k X B}
  → (Γ /ˣ k) ⟦ X ⟧⟹' B
  → Γ ⟦ X ⟧⟹' B
slv'-weaken {n} {m = m} {Γ = Γ , A} {#0} ⟦X⟧⟹'B = slv'-, ⟦X⟧⟹'B 
slv'-weaken {suc n} {m = suc m} {Γ = Γ , A} {#S k} (slv'-, ⟦X⟧⟹'B) = slv'-, (slv'-weaken ⟦X⟧⟹'B)
slv'-weaken {Γ = Γ ,∙} slv'-∙-Z = slv'-∙-Z 
slv'-weaken {Γ = Γ ,∙} (slv'-∙-S ⟦X⟧⟹'B refl) = slv'-∙-S (slv'-weaken ⟦X⟧⟹'B) refl
slv'-weaken {Γ = Γ ,= A} (slv'-=-Z refl) = slv'-=-Z refl
slv'-weaken {Γ = Γ ,= A} (slv'-=-S ⟦X⟧⟹'B refl) = slv'-=-S (slv'-weaken ⟦X⟧⟹'B) refl

slv-weaken : ∀ {Γ : Env (1 + n) m} {k A B}
  → (Γ /ˣ k) ⟦ A ⟧⟹ B
  → Γ ⟦ A ⟧⟹ B
slv-weaken {A = Int} {Int} ⟦A⟧⟹B = slv-int
slv-weaken {A = ‶ X} {B} (slv-var x) = slv-var (slv'-weaken x)
slv-weaken {A = A `→ A₁} {B `→ B₁} (slv-arr ⟦A⟧⟹B ⟦A⟧⟹B₁) = slv-arr (slv-weaken ⟦A⟧⟹B) (slv-weaken ⟦A⟧⟹B₁)
slv-weaken {A = `∀ A} {`∀ B} (slv-∀ ⟦A⟧⟹B) = slv-∀ (slv-weaken ⟦A⟧⟹B)

s-weaken : ∀ {Γ : Env (1 + n) m} {k j A B }
  → Γ /ˣ k ⊢ j # A ≤ B
  → Γ ⊢ j # A ≤ B
s-weaken (s-refl ap) = s-refl (slv-weaken ap)
s-weaken s-int = s-int
s-weaken s-var = s-var
s-weaken (s-arr₁ C≤A B≤D) = s-arr₁ (s-weaken C≤A) (s-weaken B≤D)
s-weaken (s-arr₂ C≤A B≤D) = s-arr₂ (s-weaken C≤A) (s-weaken B≤D)
s-weaken (s-∀ A≤B) = s-∀ (s-weaken A≤B)
s-weaken (s-∀l A≤B) = s-∀l (s-weaken A≤B)
s-weaken (s-∀lτ A≤B) = s-∀lτ (s-weaken A≤B)
s-weaken (s-var-l x A≤B) = s-var-l (∈-weaken x) (s-weaken A≤B)
s-weaken (s-var-r x A≤B) = s-var-r (∈-weaken x) (s-weaken A≤B)

weaken : ∀ {Γ : Env (1 + n) m} {k j e A}
  → Γ /ˣ k ⊢ j # e ⦂ A
  → Γ ⊢ j # ↑tm k e ⦂ A
weaken ⊢lit = ⊢lit
weaken {Γ = Γ} {k = k} (⊢var {x = x} refl) = ⊢var (sym (lookup-weaken {Γ = Γ}))
weaken (⊢ann e⇔A) = ⊢ann (weaken e⇔A)
weaken (⊢lam₁ e⇔A) = ⊢lam₁ (weaken e⇔A)
weaken (⊢lam₂ e⇔A) = ⊢lam₂ (weaken e⇔A)
weaken (⊢app₁ e₁⇔A e₂⇔A) = ⊢app₁ (weaken e₁⇔A) (weaken e₂⇔A)
weaken (⊢app₂ e₁⇔A e₂⇔A) = ⊢app₂ (weaken e₁⇔A) (weaken e₂⇔A)
weaken (⊢sub e⇔A B≤A j≢Z) = ⊢sub (weaken e⇔A) (s-weaken B≤A)  j≢Z
weaken (⊢tabs₁ e⇔A) = ⊢tabs₁ (weaken e⇔A)
weaken (⊢tapp e⇔A) = ⊢tapp (weaken e⇔A)

weaken-0 : ∀ {Γ : Env (1 + n) m} {j e A}
  → Γ ⊢ j # e ⦂ A
  → Γ , A ⊢ j # ↑tm0 e ⦂ A
weaken-0 {Γ = Γ} {A = A} ⊢e = weaken {Γ = Γ , A} {k = #0} ⊢e

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
  
   