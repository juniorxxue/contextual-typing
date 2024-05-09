module Record.Decl where

open import Record.Prelude
open import Record.Common

----------------------------------------------------------------------
--+                                                                +--
--+                            Counter                             +--
--+                                                                +--
----------------------------------------------------------------------

data Counter : Set where
   Z : Counter
   ∞ : Counter
   S : Counter → Counter


----------------------------------------------------------------------
--+                                                                +--
--+                           Subtyping                            +--
--+                                                                +--
----------------------------------------------------------------------

infix 5 _≤d_
data _≤d_ : Type → Type → Set where
  ≤d-int∞ :
      Int ≤d Int
  ≤d-float∞ :
      Float ≤d Float
  ≤d-top : ∀ {A}
    → A ≤d Top
  ≤d-arr : ∀ {A B C D}
    → C ≤d A
    → B ≤d D
    → A ⇒ B ≤d C ⇒ D
  ≤d-rcd : ∀ {A B l}
    → A ≤d B
    → τ⟦ l ↦ A ⟧ ≤d τ⟦ l ↦ B ⟧
  ≤d-and₁ : ∀ {A B C}
    → A ≤d C
    → A & B ≤d C
  ≤d-and₂ : ∀ {A B C}
    → B ≤d C
    → A & B ≤d C
  ≤d-and : ∀ {A B C}
    → A ≤d B
    → A ≤d C
    → A ≤d B & C

≤-refl0 : ∀ {A} → A ≤d A
≤-refl0 {Int} = ≤d-int∞
≤-refl0 {Float} = ≤d-float∞
≤-refl0 {Top} = ≤d-top
≤-refl0 {A ⇒ A₁} = ≤d-arr ≤-refl0 ≤-refl0
≤-refl0 {A & A₁} = ≤d-and (≤d-and₁ ≤-refl0) (≤d-and₂ ≤-refl0)
≤-refl0 {τ⟦ x ↦ A ⟧} = ≤d-rcd ≤-refl0

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
    → Γ ⊢d Z # 𝕔 c ⦂ c-τ c

  ⊢d-var : ∀ {Γ x A}
    → Γ ∋ x ⦂ A
    → Γ ⊢d Z # ` x ⦂ A

  ⊢d-ann : ∀ {Γ e A}
    → Γ ⊢d ∞ # e ⦂ A
    → Γ ⊢d Z # (e ⦂ A) ⦂ A

  ⊢d-lam₁ : ∀ {Γ e A B}
    → Γ , A ⊢d ∞ # e ⦂ B
    → Γ ⊢d ∞ # (ƛ e) ⦂ A ⇒ B

  ⊢d-lam₂ : ∀ {Γ e A B i}
    → Γ , A ⊢d i # e ⦂ B
    → Γ ⊢d S i # (ƛ e) ⦂ A ⇒ B

  ⊢d-app⇐ : ∀ {Γ e₁ e₂ A B}
    → Γ ⊢d Z # e₁ ⦂ A ⇒ B
    → Γ ⊢d ∞ # e₂ ⦂ A
    → Γ ⊢d Z # e₁ · e₂ ⦂ B

  ⊢d-app⇒ : ∀ {Γ e₁ e₂ A B j}
    → Γ ⊢d S j # e₁ ⦂ A ⇒ B
    → Γ ⊢d Z # e₂ ⦂ A
    → Γ ⊢d j # e₁ · e₂ ⦂ B

  ⊢d-sub : ∀ {Γ e A B i}
    → Γ ⊢d Z # e ⦂ B
    → B ≤d A
    → i ≢ Z
    → Γ ⊢d i # e ⦂ A

  ⊢d-rcd : ∀ {Γ rs As}
    → Γ ⊢r Z # rs ⦂ As
    → Γ ⊢d Z # (𝕣 rs) ⦂ As

  ⊢d-prj : ∀ {Γ e l j A}
    → Γ ⊢d j # e ⦂ τ⟦ l ↦ A ⟧
    → Γ ⊢d j # e 𝕡 l ⦂ A

data _⊢r_#_⦂_ where

  ⊢r-nil : ∀ {Γ}
    → Γ ⊢r Z # rnil ⦂ Top

  ⊢r-one : ∀ {Γ e A l}
    → Γ ⊢d Z # e ⦂ A
    → Γ ⊢r Z # r⟦ l ↦ e ⟧ rnil ⦂ τ⟦ l ↦ A ⟧

  ⊢r-cons : ∀ {Γ l e rs A As}
    → Γ ⊢d Z # e ⦂ A
    → Γ ⊢r Z # rs ⦂ As
    → rs ≢ rnil
    → Γ ⊢r Z # r⟦ l ↦ e ⟧ rs ⦂ (τ⟦ l ↦ A ⟧ & As)


----------------------------------------------------------------------
--+                            Examples                            +--
----------------------------------------------------------------------

overloading : ∅ ⊢d Z # (𝕔 +s) · (𝕔 (lit 1)) · (𝕔 (lit 2)) ⦂ Int
overloading = ⊢d-app⇐ (⊢d-app⇐ {!!} (⊢d-sub ⊢d-c ≤d-int∞ (λ ()))) (⊢d-sub ⊢d-c ≤d-int∞ (λ ()))
-- this seems a good argument
