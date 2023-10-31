module SubGen.Algo where

open import SubGen.Prelude
open import SubGen.Common

infixr 8 ⟦_⟧⇒_

data Hint : Set where
  □ : Hint
  τ : Type → Hint
  ⟦_⟧⇒_ : Term → Hint → Hint

infixl 7 _⇧_
_⇧_ : Hint → ℕ → Hint
□ ⇧ n = □
τ A ⇧ n = τ A
(⟦ e ⟧⇒ H) ⇧ n = ⟦ e ↑ n ⟧⇒ (H ⇧ n)

infixl 7 _⇩_
_⇩_ : Hint → ℕ → Hint
□ ⇩ n = □
τ A ⇩ n = τ A
(⟦ e ⟧⇒ H) ⇩ n = ⟦ e ↓ n ⟧⇒ (H ⇩ n)

data pv : Term → Set where

  pv-i : ∀ {n}
    → pv (lit n)

  pv-var : ∀ {x}
    → pv (` x)

  pv-ann : ∀ {e A}
    → pv (e ⦂ A)

↑-pv-prv : ∀ {p n}
  → pv p
  → pv (p ↑ n)
↑-pv-prv pv-i = pv-i
↑-pv-prv pv-var = pv-var
↑-pv-prv pv-ann = pv-ann

↓-pv-prv : ∀ {p n}
  → pv p
  → pv (p ↓ n)
↓-pv-prv pv-i = pv-i
↓-pv-prv pv-var = pv-var
↓-pv-prv pv-ann = pv-ann
  
infix 4 _⊢a_≤_⇝_
infix 4 _⊢a_⇛_⇛_ 

data _⊢a_≤_⇝_ : Context → Type → Hint → Type → Set
data _⊢a_⇛_⇛_ : Context → Hint → Term → Type → Set

data _⊢a_≤_⇝_ where
  ≤a-int : ∀ {Γ}
    → Γ ⊢a Int ≤ τ Int ⇝ Int
  ≤a-base : ∀ {Γ n}
    → Γ ⊢a * n ≤ τ (* n) ⇝ (* n)
  ≤a-top : ∀ {Γ A}
    → Γ ⊢a A ≤ τ Top ⇝ Top
  ≤a-□ : ∀ {Γ A}
    → Γ ⊢a A ≤ □ ⇝ A
  ≤a-arr : ∀ {Γ A B C D}
    → Γ ⊢a C ≤ τ A ⇝ A
    → Γ ⊢a B ≤ τ D ⇝ D
    ---------------------------
    → Γ ⊢a (A ⇒ B) ≤ τ (C ⇒ D) ⇝ (C ⇒ D)
  ≤a-hint : ∀ {Γ A B H e D}
    → Γ ⊢a τ A ⇛ e ⇛ A
    → Γ ⊢a B ≤ H ⇝ D
    ------------------------
    → Γ ⊢a A ⇒ B ≤ ⟦ e ⟧⇒ H ⇝ (A ⇒ D)
  ≤a-and-l : ∀ {Γ A B H C}
    → Γ ⊢a A ≤ H ⇝ C
    → Γ ⊢a A & B ≤ H ⇝ C
  ≤a-and-r : ∀ {Γ A B H C}
    → Γ ⊢a B ≤ H ⇝ C
    → Γ ⊢a A & B ≤ H ⇝ C
  ≤a-and : ∀ {Γ A B C}
    → Γ ⊢a A ≤ τ B ⇝ B
    → Γ ⊢a A ≤ τ C ⇝ C
    → Γ ⊢a A ≤ τ (B & C) ⇝ (B & C)

data _⊢a_⇛_⇛_ where

  ⊢a-lit : ∀ {Γ n}
    -----------------------
    → Γ ⊢a □ ⇛ lit n ⇛ Int

  ⊢a-var : ∀ {Γ A x}
    → Γ ∋ x ⦂ A
    -------------------
    → Γ ⊢a □ ⇛ ` x ⇛ A
    
  ⊢a-ann : ∀ {Γ e A B}
    → Γ ⊢a τ A ⇛ e ⇛ B
    ---------------------
    → Γ ⊢a □ ⇛ e ⦂ A ⇛ A
    
  ⊢a-app : ∀ {Γ e₁ e₂ H A B}
    → Γ ⊢a ⟦ e₂ ⟧⇒ H ⇛ e₁ ⇛ A ⇒ B
    ----------------------------------
    → Γ ⊢a H ⇛ e₁ · e₂ ⇛ B

  ⊢a-lam₁ : ∀ {Γ e A B C}
    → Γ , A ⊢a τ B ⇛ e ⇛ C
    ------------------------------------
    → Γ ⊢a τ (A ⇒ B) ⇛ ƛ e ⇛ A ⇒ C

  ⊢a-lam₂ : ∀ {Γ e₁ e A B H}
    → Γ ⊢a □ ⇛ e₁ ⇛ A
    → Γ , A ⊢a (H ⇧ 0) ⇛ e ⇛ B
      -------------------------------------
    → Γ ⊢a ⟦ e₁ ⟧⇒ H ⇛ ƛ e ⇛ A ⇒ B

  ⊢a-sub : ∀ {Γ H p A B}
    → pv p
    → Γ ⊢a □ ⇛ p ⇛ A
    → Γ ⊢a A ≤ H ⇝ B -- to forbid H to be □, we can try to achive this via restricting subtyping behavior
    → Γ ⊢a H ⇛ p ⇛ B

  ⊢a-& : ∀ {Γ A A' B B' e}
    → Γ ⊢a τ A ⇛ e ⇛ A'
    → Γ ⊢a τ B ⇛ e ⇛ B'
    → Γ ⊢a τ (A & B) ⇛ e ⇛ (A' & B')



----------------------------------------------------------------------
--                                                                  --
--                             Examples                             --
--                                                                  --
----------------------------------------------------------------------

≤a-refl : ∀ {Γ A}
  → Γ ⊢a A ≤ τ A ⇝ A
≤a-refl {A = Int} = ≤a-int
≤a-refl {A = * x} = ≤a-base
≤a-refl {A = Top} = ≤a-top
≤a-refl {A = A ⇒ A₁} = ≤a-arr ≤a-refl ≤a-refl
≤a-refl {A = A & B} = ≤a-and (≤a-and-l ≤a-refl) (≤a-and-r ≤a-refl)

----------------------------------------------------------------------
--+                                                                +--
--+                           Transform                            +--
--+                                                                +--
----------------------------------------------------------------------

_▻_ : Term → List Term → Term
e ▻ [] = e
e₁ ▻ (e₂ ∷ es) = (e₁ · e₂) ▻ es

infix 4 ❪_,_❫↣❪_,_,_,_❫

data ❪_,_❫↣❪_,_,_,_❫ : Hint → Type → List Term → Hint → List Type → Type → Set where

  none-□ : ∀ {A}
    → ❪ □ , A ❫↣❪ [] , □ , [] , A ❫

  none-τ : ∀ {A B}
    → ❪ τ A , B ❫↣❪ [] , τ A , [] , B ❫

  have : ∀ {e H A B es A' B' Bs}
    → ❪ H , B ❫↣❪ es , A' , Bs , B' ❫
    → ❪ ⟦ e ⟧⇒ H , A ⇒ B ❫↣❪ e ∷ es , A' , A ∷ Bs , B' ❫

{-

≤a-determinism : ∀ {Γ H A B C}
  → H ≢ τ Top
  → Γ ⊢a A ≤ H ⇝ B
  → Γ ⊢a A ≤ H ⇝ C
  → B ≡ C
≤a-determinism neq ≤a-int ≤a-int = refl
≤a-determinism neq ≤a-base ≤a-base = refl
≤a-determinism neq ≤a-top ≤C = ⊥-elim (neq refl)
≤a-determinism neq (≤a-arr ≤B ≤B₁) (≤a-arr ≤C ≤C₁) = {!≤a-determinism ? ≤B ≤C!} -- easy
≤a-determinism neq (≤a-hint ⊢1 ≤B) (≤a-hint ⊢2 ≤C) = {!!} -- easy
≤a-determinism neq (≤a-and-l ≤B) ≤C = {!!}
≤a-determinism neq (≤a-and-r ≤B) ≤C = {!!}
≤a-determinism neq (≤a-and ≤B ≤B₁) (≤a-and-l ≤C) = {!!}
≤a-determinism neq (≤a-and ≤B ≤B₁) (≤a-and-r ≤C) = {!!}
≤a-determinism neq (≤a-and ≤B ≤B₁) (≤a-and ≤C ≤C₁) = {!!}


⊢a-determinism : ∀ {Γ H e A B}
  → Γ ⊢a H ⇛ e ⇛ A
  → Γ ⊢a H ⇛ e ⇛ B
  → A ≡ B
⊢a-determinism ⊢a-lit ⊢a-lit = refl
⊢a-determinism ⊢a-lit (⊢a-sub x ⊢2 x₁ x₂) = {!!} -- easy
⊢a-determinism (⊢a-var x) ⊢2 = {!!} -- easy

⊢a-determinism (⊢a-app ⊢1) (⊢a-app ⊢2) = {!⊢a-determinism ⊢1 ⊢2!} -- easy

⊢a-determinism (⊢a-ann ⊢1) (⊢a-ann ⊢2) = refl
⊢a-determinism (⊢a-ann ⊢1) (⊢a-sub x ⊢2 x₁ x₂) = {!!} -- easy

⊢a-determinism (⊢a-lam₁ ⊢1) (⊢a-lam₁ ⊢2) = {!⊢a-determinism ⊢1 ⊢2 !}  -- easy
⊢a-determinism (⊢a-lam₂ ⊢1 ⊢3) (⊢a-lam₂ ⊢2 ⊢4) rewrite ⊢a-determinism ⊢1 ⊢2 = {!⊢a-determinism ⊢3 ⊢4!} -- easy
⊢a-determinism (⊢a-lam₃ ⊢1 ⊢3) (⊢a-lam₃ ⊢2 ⊢4) rewrite ⊢a-determinism ⊢1 ⊢2 | ⊢a-determinism ⊢3 ⊢4 = refl
⊢a-determinism (⊢a-sub x ⊢1 x₁ x₂) ⊢a-lit = {!!}
⊢a-determinism (⊢a-sub x ⊢1 x₁ x₂) (⊢a-var x₃) = {!!}
⊢a-determinism (⊢a-sub x ⊢1 x₁ x₂) (⊢a-ann ⊢2) = {!!} -- all absurds
⊢a-determinism (⊢a-sub x ⊢1 x₁ x₂) (⊢a-sub x₃ ⊢2 x₄ x₅) rewrite ⊢a-determinism ⊢1 ⊢2 = {!!}
-}

⊢a-id : ∀ {Γ H e A A' T es As}
  → Γ ⊢a H ⇛ e ⇛ A
  → ❪ H , A ❫↣❪ es , τ T , As , A' ❫
  → T ≡ A'

≤a-id : ∀ {Γ H A B Bs B' es T}
  → Γ ⊢a A ≤ H ⇝ B
  → ❪ H , B ❫↣❪ es , τ T , Bs , B' ❫
  → T ≡ B'
≤a-id ≤a-int none-τ = refl
≤a-id ≤a-base none-τ = refl
≤a-id ≤a-top none-τ = refl
≤a-id (≤a-arr A≤H A≤H₁) none-τ = refl
≤a-id (≤a-hint x A≤H) (have spl) = ≤a-id A≤H spl
≤a-id (≤a-and-l A≤H) spl = ≤a-id A≤H spl
≤a-id (≤a-and-r A≤H) spl = ≤a-id A≤H spl
≤a-id (≤a-and A≤H A≤H₁) none-τ = refl

⊢a-id (⊢a-app ⊢e) spl = ⊢a-id ⊢e (have spl)
⊢a-id (⊢a-lam₁ ⊢e) none-τ rewrite ⊢a-id ⊢e none-τ = refl
⊢a-id (⊢a-lam₂ ⊢e ⊢e₁) (have spl) = ⊢a-id ⊢e₁ (spl-⇧ spl)
  where
    spl-⇧ : ∀ {H B es T Bs A'}
      → ❪ H , B ❫↣❪ es , τ T , Bs , A' ❫
      → ❪ H ⇧ 0 , B ❫↣❪ map (_↑ 0) es , τ T , Bs , A' ❫
    spl-⇧ none-τ = none-τ
    spl-⇧ (have spl) = have (spl-⇧ spl)
⊢a-id (⊢a-sub x ⊢e x₁) spl = ≤a-id x₁ spl
⊢a-id (⊢a-& ⊢e ⊢e₁) none-τ rewrite ⊢a-id ⊢e none-τ | ⊢a-id ⊢e₁ none-τ = refl

⊢a-id-0 : ∀ {Γ e A B}
  → Γ ⊢a τ B ⇛ e ⇛ A
  → A ≡ B
⊢a-id-0 ⊢e = sym (⊢a-id ⊢e none-τ)

≤a-id-0 : ∀ {Γ A B C}
  → Γ ⊢a A ≤ τ B ⇝ C
  → C ≡ B
≤a-id-0 A≤B = sym (≤a-id A≤B none-τ)
