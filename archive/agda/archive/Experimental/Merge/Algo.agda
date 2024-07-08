{-# OPTIONS --allow-unsolved-metas #-}
module Merge.Algo where

open import Merge.Prelude
open import Merge.Common

infixr 8 ⟦_⟧⇒_
infixr 8 ⌊_⌋⇒_

data Hint : Set where
  □ : Hint
  τ : Type → Hint
  ⟦_⟧⇒_ : Term → Hint → Hint
  ⌊_⌋⇒_ : Label → Hint → Hint

infixl 7 _⇧_
_⇧_ : Hint → ℕ → Hint
□ ⇧ n = □
τ A ⇧ n = τ A
(⟦ e ⟧⇒ H) ⇧ n = ⟦ e ↑ n ⟧⇒ (H ⇧ n)
⌊ l ⌋⇒ H ⇧ n = ⌊ l ⌋⇒ (H ⇧ n)

infixl 7 _⇩_
_⇩_ : Hint → ℕ → Hint
□ ⇩ n = □
τ A ⇩ n = τ A
(⟦ e ⟧⇒ H) ⇩ n = ⟦ e ↓ n ⟧⇒ (H ⇩ n)
⌊ l ⌋⇒ H ⇩ n = ⌊ l ⌋⇒ (H ⇩ n)

data pv : Term → Set where

  pv-i : ∀ {n}
    → pv (lit n)

  pv-var : ∀ {x}
    → pv (` x)

  pv-ann : ∀ {e A}
    → pv (e ⦂ A)

  pv-mrg : ∀ {e₁ e₂}
    → pv (e₁ ⨟ e₂)

--  pv-rcd : ∀ {e l}
--    → pv ⌊ l ⇒ e ⌋

↑-pv-prv : ∀ {p n}
  → pv p
  → pv (p ↑ n)
↑-pv-prv pv-i = pv-i
↑-pv-prv pv-var = pv-var
↑-pv-prv pv-ann = pv-ann
↑-pv-prv {p ⨟ p₁} pv-mrg = {!!}

↓-pv-prv : ∀ {p n}
  → pv p
  → pv (p ↓ n)
↓-pv-prv pv-i = pv-i
↓-pv-prv pv-var = pv-var
↓-pv-prv pv-ann = pv-ann
↓-pv-prv {p ⨟ p₁} pv-mrg = {!!}
  
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
  ≤a-rcd : ∀ {Γ l A B}
    → Γ ⊢a A ≤ τ B ⇝ B
    → Γ ⊢a ⌊ l ⇒ A ⌋ ≤ τ ⌊ l ⇒ B ⌋ ⇝ ⌊ l ⇒ B ⌋
  ≤a-hint : ∀ {Γ A B H e D}
    → (⊢e : Γ ⊢a τ A ⇛ e ⇛ A)
    → Γ ⊢a B ≤ H ⇝ D
    ------------------------
    → Γ ⊢a A ⇒ B ≤ ⟦ e ⟧⇒ H ⇝ (A ⇒ D)
  ≤a-hint-l : ∀ {Γ H l A A'}
    → Γ ⊢a A ≤ H ⇝ A'
    → Γ ⊢a ⌊ l ⇒ A ⌋ ≤ ⌊ l ⌋⇒ H ⇝ ⌊ l ⇒ A' ⌋
  ≤a-and-l : ∀ {Γ A B H C}
    → Γ ⊢a A ≤ H ⇝ C
    → H ≢ □
    → Γ ⊢a A & B ≤ H ⇝ C
  ≤a-and-r : ∀ {Γ A B H C}
    → Γ ⊢a B ≤ H ⇝ C
    → H ≢ □
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
    
  ⊢a-ann : ∀ {Γ e A}
    → Γ ⊢a τ A ⇛ e ⇛ A
    ---------------------
    → Γ ⊢a □ ⇛ e ⦂ A ⇛ A
    
  ⊢a-app : ∀ {Γ e₁ e₂ H A B}
    → Γ ⊢a ⟦ e₂ ⟧⇒ H ⇛ e₁ ⇛ A ⇒ B
    ----------------------------------
    → Γ ⊢a H ⇛ e₁ · e₂ ⇛ B

  ⊢a-lam₁ : ∀ {Γ e A B}
    → Γ , A ⊢a τ B ⇛ e ⇛ B
    ------------------------------------
    → Γ ⊢a τ (A ⇒ B) ⇛ ƛ e ⇛ A ⇒ B

  ⊢a-lam₂ : ∀ {Γ e₁ e A B H}
    → Γ ⊢a □ ⇛ e₁ ⇛ A
    → Γ , A ⊢a (H ⇧ 0) ⇛ e ⇛ B
      -------------------------------------
    → Γ ⊢a ⟦ e₁ ⟧⇒ H ⇛ ƛ e ⇛ A ⇒ B

  ⊢a-sub : ∀ {Γ H p A B}
    → pv p -- we actually never use this property, it should be just NOT application and projection <- to avoid 
    → Γ ⊢a □ ⇛ p ⇛ A
    → Γ ⊢a A ≤ H ⇝ B -- to forbid H to be □, we can try to achive this via restricting subtyping behavior
    → Γ ⊢a H ⇛ p ⇛ B

  ⊢a-& : ∀ {Γ A B e}
    → Γ ⊢a τ A ⇛ e ⇛ A
    → Γ ⊢a τ B ⇛ e ⇛ B
    → Γ ⊢a τ (A & B) ⇛ e ⇛ (A & B)

  -- record
  ⊢a-⨟ : ∀ {Γ A B e₁ e₂}
    → Γ ⊢a □ ⇛ e₁ ⇛ A
    → Γ ⊢a □ ⇛ e₂ ⇛ B
    → Γ ⊢a □ ⇛ e₁ ⨟ e₂ ⇛ A & B

  ⊢a-rcd : ∀ {Γ H l e A}
    → Γ ⊢a H ⇛ e ⇛ A
    → Γ ⊢a ⌊ l ⌋⇒ H ⇛ ⌊ l ⇒ e ⌋ ⇛ ⌊ l ⇒ A ⌋

  ⊢a-prj : ∀ {Γ H e l A}
    → Γ ⊢a ⌊ l ⌋⇒ H ⇛ e ⇛ ⌊ l ⇒ A ⌋
    → Γ ⊢a H ⇛ e ⋆ l ⇛ A


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
≤a-refl {A = A & B} = ≤a-and (≤a-and-l ≤a-refl λ ()) (≤a-and-r ≤a-refl λ ())
≤a-refl {A = ⌊ l ⇒ A ⌋} = ≤a-rcd ≤a-refl

----------------------------------------------------------------------
--+                                                                +--
--+                           Transform                            +--
--+                                                                +--
----------------------------------------------------------------------

data Apps : Set where
  [] : Apps
  _∷a_ : Term → Apps → Apps
  _∷l_ : Label → Apps → Apps

data AppsType : Set where
  [] : AppsType
  _∷a_ : Type → AppsType → AppsType
  _∷l_ : Label → AppsType → AppsType

_▻_ : Term → Apps → Term
e ▻ [] = e
e ▻ (e' ∷a es) = (e · e') ▻ es
e ▻ (l ∷l es) = (e ⋆ l) ▻ es

_↑ : Apps → Apps
[] ↑ = []
(e ∷a es) ↑ = (e ↑ 0) ∷a (es ↑)
(l ∷l es) ↑ = l ∷l (es ↑)

infix 4 ⟦_,_⟧→⟦_,_,_,_⟧

data ⟦_,_⟧→⟦_,_,_,_⟧ : Hint → Type → Apps → Hint → AppsType → Type → Set where

  none-□ : ∀ {A}
    → ⟦ □ , A ⟧→⟦ [] , □ , [] , A ⟧

  none-τ : ∀ {A B}
    → ⟦ τ A , B ⟧→⟦ [] , τ A , [] , B ⟧

  have-a : ∀ {e H A B es A' B' Bs}
    → ⟦ H , B ⟧→⟦ es , A' , Bs , B' ⟧
    → ⟦ ⟦ e ⟧⇒ H , A ⇒ B ⟧→⟦ e ∷a es , A' , A ∷a Bs , B' ⟧

  have-l : ∀ {l H A es A' B' Bs}
    → ⟦ H , A ⟧→⟦ es , A' , Bs , B' ⟧
    → ⟦ ⌊ l ⌋⇒ H , ⌊ l ⇒ A ⌋ ⟧→⟦ l ∷l es , A' , l ∷l Bs , B' ⟧

⊢a-id : ∀ {Γ H e A A' T es As}
  → Γ ⊢a H ⇛ e ⇛ A
  → ⟦ H , A ⟧→⟦ es , τ T , As , A' ⟧
  → T ≡ A'

≤a-id : ∀ {Γ H A B Bs B' es T}
  → Γ ⊢a A ≤ H ⇝ B
  → ⟦ H , B ⟧→⟦ es , τ T , Bs , B' ⟧
  → T ≡ B'

⊢a-id-0 : ∀ {Γ e A B}
  → Γ ⊢a τ B ⇛ e ⇛ A
  → A ≡ B
⊢a-id-0 ⊢e = sym (⊢a-id ⊢e none-τ)

≤a-id-0 : ∀ {Γ A B C}
  → Γ ⊢a A ≤ τ B ⇝ C
  → C ≡ B
≤a-id-0 A≤B = sym (≤a-id A≤B none-τ)

⊢a-id (⊢a-app ⊢e) spl = ⊢a-id ⊢e (have-a spl)
⊢a-id (⊢a-lam₁ ⊢e) none-τ = refl
⊢a-id (⊢a-lam₂ ⊢e ⊢e₁) (have-a spl) = ⊢a-id ⊢e₁ (spl-⇧ spl)
  where
    spl-⇧ : ∀ {H B es T Bs A'}
      → ⟦ H , B ⟧→⟦ es , τ T , Bs , A' ⟧
      → ⟦ H ⇧ 0 , B ⟧→⟦ es ↑ , τ T , Bs , A' ⟧
    spl-⇧ none-τ = none-τ
    spl-⇧ (have-a spl) = have-a (spl-⇧ spl)
    spl-⇧ (have-l spl) = have-l (spl-⇧ spl)
⊢a-id (⊢a-sub x ⊢e x₁) spl = ≤a-id x₁ spl
⊢a-id (⊢a-& ⊢e ⊢e₁) none-τ = refl
⊢a-id (⊢a-rcd ⊢e) (have-l spl) = ⊢a-id ⊢e spl
⊢a-id (⊢a-prj ⊢e) spl = ⊢a-id ⊢e (have-l spl)

≤a-id ≤a-int none-τ = refl
≤a-id ≤a-base none-τ = refl
≤a-id ≤a-top none-τ = refl
≤a-id (≤a-arr A≤H A≤H₁) none-τ = refl
≤a-id (≤a-rcd A≤H) none-τ = refl
≤a-id (≤a-hint ⊢e A≤H) (have-a spl) = ≤a-id A≤H spl
≤a-id (≤a-hint-l A≤H) (have-l spl) = ≤a-id A≤H spl
≤a-id (≤a-and-l A≤H x) spl = ≤a-id A≤H spl
≤a-id (≤a-and-r A≤H x) spl = ≤a-id A≤H spl
≤a-id (≤a-and A≤H A≤H₁) none-τ = refl

