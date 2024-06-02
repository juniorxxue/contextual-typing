module Record.Decl where

open import Record.Prelude
open import Record.Common

----------------------------------------------------------------------
--+                            Counter                             +--
----------------------------------------------------------------------

-- check counter
data CCounter : Set where
   Z : CCounter
   ∞ : CCounter
   S⇐ : CCounter → CCounter
   Sl : CCounter → CCounter

-- counter   
data Counter : Set where
   ♭ : (j : CCounter) → Counter
   S⇒ : Counter → Counter

----------------------------------------------------------------------
--+                           Subtyping                            +--
----------------------------------------------------------------------

infix 5 _≤_#_
data _≤_#_ : Type → Counter → Type → Set where
  ≤Z : ∀ {A}
    → A ≤ ♭ Z # A
  ≤int∞ :
      Int ≤ ♭ ∞ # Int
  ≤float∞ :
      Float ≤ ♭ ∞ # Float
  ≤top : ∀ {A}
    → A ≤ ♭ ∞ # Top
  ≤arr-∞ : ∀ {A B C D}
    → C ≤ ♭ ∞ # A
    → B ≤ ♭ ∞ # D
    → A `→ B ≤ ♭ ∞ # C `→ D
  ≤rcd∞ : ∀ {A B l}
    → A ≤ ♭ ∞ # B
    → τ⟦ l ↦ A ⟧ ≤ (♭ ∞) # τ⟦ l ↦ B ⟧
  ≤arr-S⇐ : ∀ {A B D j}
    → A ≤ ♭ ∞ # A
    → B ≤ ♭ j # D
    → A `→ B ≤ ♭ (S⇐ j) # A `→ D
  ≤arr-S⇒ : ∀ {A B D i}
    → A ≤ ♭ ∞ # A
    → B ≤ i # D
    → A `→ B ≤ S⇒ i # A `→ D    
  ≤rcd-Sl : ∀ {A B l j}
    → A ≤ ♭ j # B
    → τ⟦ l ↦ A ⟧ ≤ ♭ (Sl j) # (τ⟦ l ↦ B ⟧)
  ≤and₁ : ∀ {A B C j}
    → A ≤ j # C
    → j ≢ ♭ Z
    → A & B ≤ j # C
  ≤and₂ : ∀ {A B C j}
    → B ≤ j # C
    → j ≢ ♭ Z
    → A & B ≤ j # C
  ≤and : ∀ {A B C}
    → A ≤ ♭ ∞ # B
    → A ≤ ♭ ∞ # C
    → A ≤ ♭ ∞ # B & C

≤refl0 : ∀ {A} → A ≤ ♭ Z # A
≤refl0 = ≤Z

≤refl∞ : ∀ {A} → A ≤ ♭ ∞ # A
≤refl∞ {A = Int} = ≤int∞
≤refl∞ {A = Float} = ≤float∞
≤refl∞ {A = Top} = ≤top
≤refl∞ {A = A `→ A₁} = ≤arr-∞ ≤refl∞ ≤refl∞
≤refl∞ {A = A & A₁} = ≤and (≤and₁ ≤refl∞ λ ()) (≤and₂ ≤refl∞ λ ())
≤refl∞ {τ⟦ l ↦ A ⟧} = ≤rcd∞ ≤refl∞

----------------------------------------------------------------------
--+                                                                +--
--+                             Typing                             +--
--+                                                                +--
----------------------------------------------------------------------


infix 4 _⊢_#_⦂_
infix 4 _⊢r_#_⦂_

data _⊢_#_⦂_ : Env → Counter → Term → Type → Set
data _⊢r_#_⦂_ : Env → Counter → Record → Type → Set

data _⊢_#_⦂_ where

  ⊢c : ∀ {Γ c}
    → Γ ⊢ ♭ Z # 𝕔 c ⦂ c-τ c

  ⊢var : ∀ {Γ x A}
    → Γ ∋ x ⦂ A
    → Γ ⊢ ♭ Z # ` x ⦂ A

  ⊢ann : ∀ {Γ e A}
    → Γ ⊢ ♭ ∞ # e ⦂ A
    → Γ ⊢ ♭ Z # (e ⦂ A) ⦂ A

  ⊢lam₁ : ∀ {Γ e A B}
    → Γ , A ⊢ ♭ ∞ # e ⦂ B
    → Γ ⊢ ♭ ∞ # (ƛ e) ⦂ A `→ B

  ⊢lam₂ : ∀ {Γ e A B i}
    → Γ , A ⊢ i # e ⦂ B
    → Γ ⊢ S⇒ i # (ƛ e) ⦂ A `→ B

  ⊢app⇐ : ∀ {Γ e₁ e₂ A B j}
    → Γ ⊢ ♭ (S⇐ j) # e₁ ⦂ A `→ B
    → Γ ⊢ ♭ ∞ # e₂ ⦂ A
    → Γ ⊢ ♭ j # e₁ · e₂ ⦂ B

  ⊢app⇒ : ∀ {Γ e₁ e₂ A B j}
    → Γ ⊢ S⇒ j # e₁ ⦂ A `→ B
    → Γ ⊢ ♭ Z # e₂ ⦂ A
    → Γ ⊢ j # e₁ · e₂ ⦂ B

  ⊢sub : ∀ {Γ e A B i}
    → Γ ⊢ ♭ Z # e ⦂ B
    → B ≤ i # A
    → i ≢ ♭ Z
    → Γ ⊢ i # e ⦂ A

  ⊢rcd : ∀ {Γ rs As}
    → Γ ⊢r ♭ Z # rs ⦂ As
    → Γ ⊢ ♭ Z # (𝕣 rs) ⦂ As

  ⊢prj : ∀ {Γ e l j A}
    → Γ ⊢ ♭ (Sl j) # e ⦂ τ⟦ l ↦ A ⟧
    → Γ ⊢ ♭ j # e 𝕡 l ⦂ A

data _⊢r_#_⦂_ where

  ⊢r-nil : ∀ {Γ}
    → Γ ⊢r ♭ Z # rnil ⦂ Top

  ⊢r-one : ∀ {Γ e A l}
    → Γ ⊢ ♭ Z # e ⦂ A
    → Γ ⊢r ♭ Z # r⟦ l ↦ e ⟧ rnil ⦂ τ⟦ l ↦ A ⟧

  ⊢r-cons : ∀ {Γ l e rs A As}
    → Γ ⊢ ♭ Z # e ⦂ A
    → Γ ⊢r ♭ Z # rs ⦂ As
    → rs ≢ rnil
    → Γ ⊢r ♭ Z # r⟦ l ↦ e ⟧ rs ⦂ (τ⟦ l ↦ A ⟧ & As)
