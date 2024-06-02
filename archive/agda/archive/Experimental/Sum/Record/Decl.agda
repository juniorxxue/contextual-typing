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
  ≤d-base∞ : ∀ {n}
    → * n ≤d ♭ ∞ # * n
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
  ≤d-sum : ∀ {A B C D}
    → A ≤d ♭ ∞ # C
    → B ≤d ♭ ∞ # D
    → (A ⊕ B) ≤d ♭ ∞ # (C ⊕ D)
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
≤d-refl∞ {A = * x} = ≤d-base∞
≤d-refl∞ {A = Top} = ≤d-top
≤d-refl∞ {A = A ⇒ A₁} = ≤d-arr-∞ ≤d-refl∞ ≤d-refl∞
≤d-refl∞ {A = A & A₁} = ≤d-and (≤d-and₁ ≤d-refl∞ λ ()) (≤d-and₂ ≤d-refl∞ λ ())
≤d-refl∞ {τ⟦ l ↦ A ⟧} = ≤d-rcd∞ ≤d-refl∞
≤d-refl∞ {A ⊕ A₁} = ≤d-sum ≤d-refl∞ ≤d-refl∞

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

  ⊢d-& : ∀ {Γ e A B}
    → Γ ⊢d ♭ ∞ # e ⦂ A
    → Γ ⊢d ♭ ∞ # e ⦂ B
    → Γ ⊢d ♭ ∞ # e ⦂ A & B

  ⊢d-rcd : ∀ {Γ rs As}
    → Γ ⊢r ♭ Z # rs ⦂ As
    → Γ ⊢d ♭ Z # (𝕣 rs) ⦂ As

  ⊢d-prj : ∀ {Γ e l j A}
    → Γ ⊢d ♭ (Sl j) # e ⦂ τ⟦ l ↦ A ⟧
    → Γ ⊢d ♭ j # e 𝕡 l ⦂ A

  ⊢d-sum : ∀ {Γ e e₁ e₂ A₁ A₂ B j}
    → Γ ⊢d ♭ Z # e ⦂ A₁ ⊕ A₂
    → Γ , A₁ ⊢d j # e₁ ⦂ B
    → Γ , A₂ ⊢d j # e₂ ⦂ B
    → Γ ⊢d j # case e [inj₁⇒ e₁ |inj₂⇒ e₂ ] ⦂ B

data _⊢r_#_⦂_ where

  ⊢r-nil : ∀ {Γ}
    → Γ ⊢r ♭ Z # rnil ⦂ Top

  ⊢r-one : ∀ {Γ e A l}
    → Γ ⊢d ♭ Z # e ⦂ A
    → Γ ⊢r ♭ Z # r⟦ l ↦ e ⟧ rnil ⦂ τ⟦ l ↦ A ⟧

  ⊢r-cons : ∀ {Γ l e rs A As}
    → Γ ⊢d ♭ Z # e ⦂ A
    → Γ ⊢r ♭ Z # rs ⦂ As
    → Γ ⊢r ♭ Z # r⟦ l ↦ e ⟧ rs ⦂ (τ⟦ l ↦ A ⟧ & As)


----------------------------------------------------------------------
--+                                                                +--
--+                            Examples                            +--
--+                                                                +--
----------------------------------------------------------------------

id-fun-& : Term
id-fun-& = (ƛ ` 0) ⦂ (Int ⇒ Int) & (* 1 ⇒ * 1)

⊢id-fun-& : ∅ ⊢d ♭ Z # id-fun-& ⦂ (Int ⇒ Int) & (* 1 ⇒ * 1)
⊢id-fun-& = ⊢d-ann (⊢d-& (⊢d-lam₁ (⊢d-sub (⊢d-var Z) ≤d-int∞ (λ ()))) (⊢d-lam₁ (⊢d-sub (⊢d-var Z) ≤d-base∞ (λ ()))))

example-1-sub : (τ⟦ 1 ↦ (Int ⇒ Int) & (* 1 ⇒ * 1) ⟧ & (τ⟦ 2 ↦ Int ⟧))
                    ≤d ♭ (Sl (S⇐ Z)) # (τ⟦ 1 ↦ Int ⇒ Int ⟧)
example-1-sub = ≤d-and₁ (≤d-rcd-Sl (≤d-and₁ (≤d-arr-S⇐ ≤d-int∞ ≤d-Z) (λ ()))) (λ ())