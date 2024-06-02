module Record.Algo where

open import Record.Prelude
open import Record.Common

infixr 8 ⟦_⟧⇒_
infixr 8 ⌊_⌋⇒_

data Context : Set where
  □ : Context
  τ : Type → Context
  ⟦_⟧⇒_ : Term → Context → Context
  ⌊_⌋⇒_ : Label → Context → Context

infixl 7 _⇧_
_⇧_ : Context → ℕ → Context
□ ⇧ n = □
τ A ⇧ n = τ A
(⟦ e ⟧⇒ Σ) ⇧ n = ⟦ e ↑ n ⟧⇒ (Σ ⇧ n)
⌊ l ⌋⇒ Σ ⇧ n = ⌊ l ⌋⇒ (Σ ⇧ n)

infixl 7 _⇩_
_⇩_ : Context → ℕ → Context
□ ⇩ n = □
τ A ⇩ n = τ A
(⟦ e ⟧⇒ Σ) ⇩ n = ⟦ e ↓ n ⟧⇒ (Σ ⇩ n)
⌊ l ⌋⇒ Σ ⇩ n = ⌊ l ⌋⇒ (Σ ⇩ n)

data GenericConsumer : Term → Set where

  gc-i : ∀ {n} → GenericConsumer (𝕔 n)
  gc-var : ∀ {x} → GenericConsumer (` x)
  gc-ann : ∀ {e A} → GenericConsumer (e ⦂ A)
  gc-rcd : ∀ {rs} → GenericConsumer (𝕣 rs)

↑-gc-prv : ∀ {p n}
  → GenericConsumer p
  → GenericConsumer (p ↑ n)
↑-gc-prv gc-i = gc-i
↑-gc-prv gc-var = gc-var
↑-gc-prv gc-ann = gc-ann
↑-gc-prv gc-rcd = gc-rcd

↓-gc-prv : ∀ {p n}
  → GenericConsumer p
  → GenericConsumer (p ↓ n)
↓-gc-prv gc-i = gc-i
↓-gc-prv gc-var = gc-var
↓-gc-prv gc-ann = gc-ann
↓-gc-prv gc-rcd = gc-rcd
  
infix 4 _⊢_≤_⇝_
infix 4 _⊢_⇒_⇒_
infix 4 _⊢r_⇒_⇒_

data _⊢_≤_⇝_ : Env → Type → Context → Type → Set
data _⊢_⇒_⇒_ : Env → Context → Term → Type → Set
data _⊢r_⇒_⇒_ : Env → Context → Record → Type → Set

data _⊢_≤_⇝_ where
  ≤int : ∀ {Γ}
    → Γ ⊢ Int ≤ τ Int ⇝ Int
  ≤float : ∀ {Γ}
    → Γ ⊢ Float ≤ τ Float ⇝ Float
  ≤top : ∀ {Γ A}
    → Γ ⊢ A ≤ τ Top ⇝ Top
  ≤□ : ∀ {Γ A}
    → Γ ⊢ A ≤ □ ⇝ A
  ≤arr : ∀ {Γ A B C D A' D'}
    → Γ ⊢ C ≤ τ A ⇝ A'
    → Γ ⊢ B ≤ τ D ⇝ D'
    ---------------------------
    → Γ ⊢ (A `→ B) ≤ τ (C `→ D) ⇝ (C `→ D)
  ≤rcd : ∀ {Γ l A B B'}
    → Γ ⊢ A ≤ τ B ⇝ B'
    → Γ ⊢ τ⟦ l ↦ A ⟧ ≤ τ (τ⟦ l ↦ B ⟧) ⇝ τ⟦ l ↦ B' ⟧
  ≤hint : ∀ {Γ A B C Σ e D}
    → Γ ⊢ τ A ⇒ e ⇒ C
    → Γ ⊢ B ≤ Σ ⇝ D
    ------------------------
    → Γ ⊢ A `→ B ≤ ⟦ e ⟧⇒ Σ ⇝ (A `→ D)
  ≤hint-l : ∀ {Γ Σ l A A'}
    → Γ ⊢ A ≤ Σ ⇝ A'
    → Γ ⊢ τ⟦ l ↦ A ⟧ ≤  ⌊ l ⌋⇒ Σ ⇝ τ⟦ l ↦ A' ⟧
  ≤and-l : ∀ {Γ A B Σ C}
    → Γ ⊢ A ≤ Σ ⇝ C
    → Σ ≢ □
    → Γ ⊢ A & B ≤ Σ ⇝ C
  ≤and-r : ∀ {Γ A B Σ C}
    → Γ ⊢ B ≤ Σ ⇝ C
    → Σ ≢ □
    → Γ ⊢ A & B ≤ Σ ⇝ C
  ≤and : ∀ {Γ A B C B' C'}
    → Γ ⊢ A ≤ τ B ⇝ B'
    → Γ ⊢ A ≤ τ C ⇝ C'
    → Γ ⊢ A ≤ τ (B & C) ⇝ (B' & C')

data _⊢_⇒_⇒_ where

  ⊢c : ∀ {Γ c}
    -----------------------
    → Γ ⊢ □ ⇒ 𝕔 c ⇒ c-τ c

  ⊢var : ∀ {Γ A x}
    → (x∈Γ : Γ ∋ x ⦂ A)
    -------------------
    → Γ ⊢ □ ⇒ ` x ⇒ A
    
  ⊢ann : ∀ {Γ e A B}
    → Γ ⊢ τ A ⇒ e ⇒ B
    ---------------------
    → Γ ⊢ □ ⇒ e ⦂ A ⇒ A
    
  ⊢app : ∀ {Γ e₁ e₂ Σ A B}
    → Γ ⊢ ⟦ e₂ ⟧⇒ Σ ⇒ e₁ ⇒ A `→ B
    ----------------------------------
    → Γ ⊢ Σ ⇒ e₁ · e₂ ⇒ B

  ⊢lam₁ : ∀ {Γ e A B C}
    → Γ , A ⊢ τ B ⇒ e ⇒ C
    ------------------------------------
    → Γ ⊢ τ (A `→ B) ⇒ ƛ e ⇒ A `→ C

  ⊢lam₂ : ∀ {Γ e₁ e A B Σ}
    → Γ ⊢ □ ⇒ e₁ ⇒ A
    → Γ , A ⊢ (Σ ⇧ 0) ⇒ e ⇒ B
      -------------------------------------
    → Γ ⊢ ⟦ e₁ ⟧⇒ Σ ⇒ ƛ e ⇒ A `→ B

  ⊢sub : ∀ {Γ Σ g A B}
    → (g-e : GenericConsumer g)
    → Γ ⊢ □ ⇒ g ⇒ A
    → (A≤Σ : Γ ⊢ A ≤ Σ ⇝ B)
    → (Σ≢□ : Σ ≢ □)
    → Γ ⊢ Σ ⇒ g ⇒ B

  -- record
  ⊢rcd : ∀ {Γ rs A}  
    → Γ ⊢r □ ⇒ rs ⇒ A
    → Γ ⊢ □ ⇒ 𝕣 rs ⇒ A

  ⊢prj : ∀ {Γ Σ e l₁ l₂ A}
    → Γ ⊢ ⌊ l₁ ⌋⇒ Σ ⇒ e ⇒ τ⟦ l₂ ↦ A ⟧
    → Γ ⊢ Σ ⇒ e 𝕡 l₁ ⇒ A

data _⊢r_⇒_⇒_ where

  ⊢nil : ∀ {Γ}
    → Γ ⊢r □ ⇒ rnil ⇒ Top

  ⊢one : ∀ {Γ e A l}
    → Γ ⊢ □ ⇒ e ⇒ A
    → Γ ⊢r □ ⇒ r⟦ l ↦ e ⟧ rnil ⇒ τ⟦ l ↦ A ⟧

  ⊢cons : ∀ {Γ e A Bs rs l}
    → Γ ⊢ □ ⇒ e ⇒ A
    → Γ ⊢r □ ⇒ rs ⇒ Bs
    → rs ≢ rnil
    → Γ ⊢r □ ⇒ r⟦ l ↦ e ⟧ rs ⇒ τ⟦ l ↦ A ⟧ & Bs


----------------------------------------------------------------------
--                                                                  --
--                             Examples                             --
--                                                                  --
----------------------------------------------------------------------

≤refl : ∀ {Γ A}
  → Γ ⊢ A ≤ τ A ⇝ A
≤refl {A = Int} = ≤int
≤refl {A = Float} = ≤float
≤refl {A = Top} = ≤top
≤refl {A = A `→ A₁} = ≤arr ≤refl ≤refl
≤refl {A = A & B} = ≤and (≤and-l ≤refl λ ()) (≤and-r ≤refl λ ())
≤refl {A = τ⟦ l ↦ A ⟧} = ≤rcd ≤refl

----------------------------------------------------------------------
--+                           Transform                            +--
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

data ⟦_,_⟧→⟦_,_,_,_⟧ : Context → Type → Apps → Context → AppsType → Type → Set where

  none-□ : ∀ {A}
    → ⟦ □ , A ⟧→⟦ [] , □ , [] , A ⟧

  none-τ : ∀ {A B}
    → ⟦ τ A , B ⟧→⟦ [] , τ A , [] , B ⟧

  have-a : ∀ {e Σ A B es A' B' Bs}
    → ⟦ Σ , B ⟧→⟦ es , A' , Bs , B' ⟧
    → ⟦ ⟦ e ⟧⇒ Σ , A `→ B ⟧→⟦ e ∷a es , A' , A ∷a Bs , B' ⟧

  have-l : ∀ {l₁ l₂ Σ A es A' B' Bs}
    → ⟦ Σ , A ⟧→⟦ es , A' , Bs , B' ⟧
    → ⟦ ⌊ l₁ ⌋⇒ Σ , (τ⟦ l₂ ↦ A ⟧) ⟧→⟦ l₁ ∷l es , A' , l₂ ∷l Bs , B' ⟧
