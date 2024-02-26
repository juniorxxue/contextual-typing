module Record.Decl where

open import Record.Prelude
open import Record.Common

----------------------------------------------------------------------
--+                                                                +--
--+                            Counter                             +--
--+                                                                +--
----------------------------------------------------------------------

data CCounter : Set where
   Z : CCounter
   ∞ : CCounter
   S⇐ : CCounter → CCounter
   Sl : CCounter → CCounter -- remember to argue that this is not interleaved with S⇒

   
data Counter : Set where
   ♭ : (j : CCounter) → Counter
   S⇒ : Counter → Counter


----------------------------------------------------------------------
--+                                                                +--
--+                           Subtyping                            +--
--+                                                                +--
----------------------------------------------------------------------

infix 5 _≤d_#_
data _≤d_#_ : Type → Counter → Type → Set where
  ≤d-Z : ∀ {A}
    → A ≤d ♭ Z # A
  ≤d-int∞ :
      Int ≤d ♭ ∞ # Int
  ≤d-float∞ :
      Float ≤d ♭ ∞ # Float
  ≤d-top : ∀ {A}
    → A ≤d ♭ ∞ # Top
  ≤d-arr-∞ : ∀ {A B C D}
    → C ≤d ♭ ∞ # A
    → B ≤d ♭ ∞ # D
    → A ⇒ B ≤d ♭ ∞ # C ⇒ D
  ≤d-rcd∞ : ∀ {A B l}
    → A ≤d ♭ ∞ # B
    → τ⟦ l ↦ A ⟧ ≤d ♭ ∞ # τ⟦ l ↦ B ⟧
  ≤d-arr-S⇐ : ∀ {A B D j}
    → A ≤d ♭ ∞ # A
    → B ≤d ♭ j # D
    → A ⇒ B ≤d ♭ (S⇐ j) # A ⇒ D -- this is wrong
  ≤d-arr-S⇒ : ∀ {A B D i}
    → A ≤d ♭ ∞ # A
    → B ≤d i # D
    → A ⇒ B ≤d S⇒ i # A ⇒ D    
  ≤d-rcd-Sl : ∀ {A B l j}
    → A ≤d ♭ j # B
    → τ⟦ l ↦ A ⟧ ≤d ♭ (Sl j) # (τ⟦ l ↦ B ⟧)
  ≤d-and₁ : ∀ {A B C j}
    → A ≤d j # C
    → j ≢ ♭ Z
    → A & B ≤d j # C
  ≤d-and₂ : ∀ {A B C j}
    → B ≤d j # C
    → j ≢ ♭ Z
    → A & B ≤d j # C
  ≤d-and : ∀ {A B C}
    → A ≤d ♭ ∞ # B
    → A ≤d ♭ ∞ # C
    → A ≤d ♭ ∞ # B & C

≤-refl0 : ∀ {A} → A ≤d ♭ Z # A
≤-refl0 = ≤d-Z

≤d-refl∞ : ∀ {A} → A ≤d ♭ ∞ # A
≤d-refl∞ {A = Int} = ≤d-int∞
≤d-refl∞ {A = Float} = ≤d-float∞
≤d-refl∞ {A = Top} = ≤d-top
≤d-refl∞ {A = A ⇒ A₁} = ≤d-arr-∞ ≤d-refl∞ ≤d-refl∞
≤d-refl∞ {A = A & A₁} = ≤d-and (≤d-and₁ ≤d-refl∞ λ ()) (≤d-and₂ ≤d-refl∞ λ ())
≤d-refl∞ {τ⟦ l ↦ A ⟧} = ≤d-rcd∞ ≤d-refl∞

----------------------------------------------------------------------
--+                                                                +--
--+                             Typing                             +--
--+                                                                +--
----------------------------------------------------------------------


infix 4 _⊢d_#_⦂_
infix 4 _⊢r_#_⦂_

data _⊢d_#_⦂_ : Context → Counter → Term → Type → Set
data _⊢r_#_⦂_ : Context → Counter → Record → Type → Set

data _⊢d_#_⦂_ where

  ⊢d-c : ∀ {Γ c}
    → Γ ⊢d ♭ Z # 𝕔 c ⦂ c-τ c

  ⊢d-var : ∀ {Γ x A}
    → Γ ∋ x ⦂ A
    → Γ ⊢d ♭ Z # ` x ⦂ A

  ⊢d-ann : ∀ {Γ e A}
    → Γ ⊢d ♭ ∞ # e ⦂ A
    → Γ ⊢d ♭ Z # (e ⦂ A) ⦂ A

  ⊢d-lam₁ : ∀ {Γ e A B}
    → Γ , A ⊢d ♭ ∞ # e ⦂ B
    → Γ ⊢d ♭ ∞ # (ƛ e) ⦂ A ⇒ B

  ⊢d-lam₂ : ∀ {Γ e A B i}
    → Γ , A ⊢d i # e ⦂ B
    → Γ ⊢d S⇒ i # (ƛ e) ⦂ A ⇒ B

  ⊢d-app⇐ : ∀ {Γ e₁ e₂ A B j}
    → Γ ⊢d ♭ (S⇐ j) # e₁ ⦂ A ⇒ B
    → Γ ⊢d ♭ ∞ # e₂ ⦂ A
    → Γ ⊢d ♭ j # e₁ · e₂ ⦂ B

  ⊢d-app⇒ : ∀ {Γ e₁ e₂ A B j}
    → Γ ⊢d S⇒ j # e₁ ⦂ A ⇒ B
    → Γ ⊢d ♭ Z # e₂ ⦂ A
    → Γ ⊢d j # e₁ · e₂ ⦂ B

  ⊢d-sub : ∀ {Γ e A B i}
    → Γ ⊢d ♭ Z # e ⦂ B
    → B ≤d i # A
    → i ≢ ♭ Z
    → Γ ⊢d i # e ⦂ A

  ⊢d-rcd : ∀ {Γ rs As}
    → Γ ⊢r ♭ Z # rs ⦂ As
    → Γ ⊢d ♭ Z # (𝕣 rs) ⦂ As

  ⊢d-prj : ∀ {Γ e l j A}
    → Γ ⊢d ♭ (Sl j) # e ⦂ τ⟦ l ↦ A ⟧
    → Γ ⊢d ♭ j # e 𝕡 l ⦂ A

data _⊢r_#_⦂_ where

  ⊢r-nil : ∀ {Γ}
    → Γ ⊢r ♭ Z # rnil ⦂ Top

  ⊢r-one : ∀ {Γ e A l}
    → Γ ⊢d ♭ Z # e ⦂ A
    → Γ ⊢r ♭ Z # r⟦ l ↦ e ⟧ rnil ⦂ τ⟦ l ↦ A ⟧

  ⊢r-cons : ∀ {Γ l e rs A As}
    → Γ ⊢d ♭ Z # e ⦂ A
    → Γ ⊢r ♭ Z # rs ⦂ As
    → rs ≢ rnil
    → Γ ⊢r ♭ Z # r⟦ l ↦ e ⟧ rs ⦂ (τ⟦ l ↦ A ⟧ & As)
