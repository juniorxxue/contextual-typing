module Record.Algo where

open import Record.Prelude
open import Record.Common

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
    → pv (𝕔 n)

  pv-var : ∀ {x}
    → pv (` x)

  pv-ann : ∀ {e A}
    → pv (e ⦂ A)

  pv-rcd : ∀ {rs}
    → pv (𝕣 rs)

↑-pv-prv : ∀ {p n}
  → pv p
  → pv (p ↑ n)
↑-pv-prv pv-i = pv-i
↑-pv-prv pv-var = pv-var
↑-pv-prv pv-ann = pv-ann
↑-pv-prv pv-rcd = pv-rcd

↓-pv-prv : ∀ {p n}
  → pv p
  → pv (p ↓ n)
↓-pv-prv pv-i = pv-i
↓-pv-prv pv-var = pv-var
↓-pv-prv pv-ann = pv-ann
↓-pv-prv pv-rcd = pv-rcd
  
infix 4 _⊢a_≤_⇝_
infix 4 _⊢a_⇛_⇛_
infix 4 _⊢r_⇛_⇛_

data _⊢a_≤_⇝_ : Context → Type → Hint → Type → Set
data _⊢a_⇛_⇛_ : Context → Hint → Term → Type → Set
data _⊢r_⇛_⇛_ : Context → Hint → Record → Type → Set

data _⊢a_≤_⇝_ where
  ≤a-int : ∀ {Γ}
    → Γ ⊢a Int ≤ τ Int ⇝ Int
  ≤a-float : ∀ {Γ}
    → Γ ⊢a Float ≤ τ Float ⇝ Float
  ≤a-top : ∀ {Γ A}
    → Γ ⊢a A ≤ τ Top ⇝ Top
  ≤a-□ : ∀ {Γ A}
    → Γ ⊢a A ≤ □ ⇝ A
  ≤a-arr : ∀ {Γ A B C D A' D'}
    → Γ ⊢a C ≤ τ A ⇝ A'
    → Γ ⊢a B ≤ τ D ⇝ D'
    ---------------------------
    → Γ ⊢a (A ⇒ B) ≤ τ (C ⇒ D) ⇝ (C ⇒ D)
  ≤a-rcd : ∀ {Γ l A B B'}
    → Γ ⊢a A ≤ τ B ⇝ B'
    → Γ ⊢a τ⟦ l ↦ A ⟧ ≤ τ (τ⟦ l ↦ B ⟧) ⇝ τ⟦ l ↦ B' ⟧
  ≤a-hint : ∀ {Γ A B C H e D}
    → Γ ⊢a τ A ⇛ e ⇛ C
    → Γ ⊢a B ≤ H ⇝ D
    ------------------------
    → Γ ⊢a A ⇒ B ≤ ⟦ e ⟧⇒ H ⇝ (A ⇒ D)
  ≤a-hint-l : ∀ {Γ H l A A'}
    → Γ ⊢a A ≤ H ⇝ A'
    → Γ ⊢a τ⟦ l ↦ A ⟧ ≤  ⌊ l ⌋⇒ H ⇝ τ⟦ l ↦ A' ⟧
  ≤a-and-l : ∀ {Γ A B H C}
    → Γ ⊢a A ≤ H ⇝ C
    → H ≢ □
    → Γ ⊢a A & B ≤ H ⇝ C
  ≤a-and-r : ∀ {Γ A B H C}
    → Γ ⊢a B ≤ H ⇝ C
    → H ≢ □
    → Γ ⊢a A & B ≤ H ⇝ C
  ≤a-and : ∀ {Γ A B C B' C'}
    → Γ ⊢a A ≤ τ B ⇝ B'
    → Γ ⊢a A ≤ τ C ⇝ C'
    → Γ ⊢a A ≤ τ (B & C) ⇝ (B' & C')

data _⊢a_⇛_⇛_ where

  ⊢a-c : ∀ {Γ c}
    -----------------------
    → Γ ⊢a □ ⇛ 𝕔 c ⇛ c-τ c

  ⊢a-var : ∀ {Γ A x}
    → (x∈Γ : Γ ∋ x ⦂ A)
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
    → (p-e : pv p)
    → Γ ⊢a □ ⇛ p ⇛ A
    → (A≤H : Γ ⊢a A ≤ H ⇝ B)
    → (H≢□ : H ≢ □)
    → Γ ⊢a H ⇛ p ⇛ B

  -- record
  ⊢a-rcd : ∀ {Γ rs A}  
    → Γ ⊢r □ ⇛ rs ⇛ A
    → Γ ⊢a □ ⇛ 𝕣 rs ⇛ A

  ⊢a-prj : ∀ {Γ H e l₁ l₂ A}
    → Γ ⊢a ⌊ l₁ ⌋⇒ H ⇛ e ⇛ τ⟦ l₂ ↦ A ⟧
    → Γ ⊢a H ⇛ e 𝕡 l₁ ⇛ A

data _⊢r_⇛_⇛_ where

  ⊢a-nil : ∀ {Γ}
    → Γ ⊢r □ ⇛ rnil ⇛ Top

  ⊢a-one : ∀ {Γ e A l}
    → Γ ⊢a □ ⇛ e ⇛ A
    → Γ ⊢r □ ⇛ r⟦ l ↦ e ⟧ rnil ⇛ τ⟦ l ↦ A ⟧

  ⊢a-cons : ∀ {Γ e A Bs rs l}
    → Γ ⊢a □ ⇛ e ⇛ A
    → Γ ⊢r □ ⇛ rs ⇛ Bs
    → Γ ⊢r □ ⇛ r⟦ l ↦ e ⟧ rs ⇛ τ⟦ l ↦ A ⟧ & Bs


----------------------------------------------------------------------
--                                                                  --
--                             Examples                             --
--                                                                  --
----------------------------------------------------------------------

≤a-refl : ∀ {Γ A}
  → Γ ⊢a A ≤ τ A ⇝ A
≤a-refl {A = Int} = ≤a-int
≤a-refl {A = Float} = ≤a-float
≤a-refl {A = Top} = ≤a-top
≤a-refl {A = A ⇒ A₁} = ≤a-arr ≤a-refl ≤a-refl
≤a-refl {A = A & B} = ≤a-and (≤a-and-l ≤a-refl λ ()) (≤a-and-r ≤a-refl λ ())
≤a-refl {A = τ⟦ l ↦ A ⟧} = ≤a-rcd ≤a-refl

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
e ▻ (l ∷l es) = (e 𝕡 l) ▻ es

infix 4 ⟦_,_⟧→⟦_,_,_,_⟧

data ⟦_,_⟧→⟦_,_,_,_⟧ : Hint → Type → Apps → Hint → AppsType → Type → Set where

  none-□ : ∀ {A}
    → ⟦ □ , A ⟧→⟦ [] , □ , [] , A ⟧

  none-τ : ∀ {A B}
    → ⟦ τ A , B ⟧→⟦ [] , τ A , [] , B ⟧

  have-a : ∀ {e H A B es A' B' Bs}
    → ⟦ H , B ⟧→⟦ es , A' , Bs , B' ⟧
    → ⟦ ⟦ e ⟧⇒ H , A ⇒ B ⟧→⟦ e ∷a es , A' , A ∷a Bs , B' ⟧

  have-l : ∀ {l₁ l₂ H A es A' B' Bs}
    → ⟦ H , A ⟧→⟦ es , A' , Bs , B' ⟧
    → ⟦ ⌊ l₁ ⌋⇒ H , (τ⟦ l₂ ↦ A ⟧) ⟧→⟦ l₁ ∷l es , A' , l₂ ∷l Bs , B' ⟧



