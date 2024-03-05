module Record.Decl where

open import Record.Prelude
open import Record.Common

----------------------------------------------------------------------
--+                                                                +--
--+                            Counter                             +--
--+                                                                +--
----------------------------------------------------------------------

infixr 6 𝕓
infixr 5 𝕚

data CCounter : Set where
   Z : CCounter
   S⇐ : CCounter → CCounter
   Sl : CCounter → CCounter

data ICounter : Set where
   𝕓 : (j : CCounter) → ICounter
   S⇒ : ICounter → ICounter

data Counter : Set where
   𝕚 : (i : ICounter) → Counter
   ∞ : Counter

𝕫 = 𝕚 (𝕓 (Z))

----------------------------------------------------------------------
--+                                                                +--
--+                           Subtyping                            +--
--+                                                                +--
----------------------------------------------------------------------

infix 5 _≤d_#_
data _≤d_#_ : Type → Counter → Type → Set where
  ≤d-Z : ∀ {A}
    → A ≤d 𝕫 # A
  ≤d-int∞ :
      Int ≤d ∞ # Int
  ≤d-float∞ :
      Float ≤d ∞ # Float
  ≤d-base∞ : ∀ {n}
    → * n ≤d ∞ # * n
  ≤d-top : ∀ {A}
    → A ≤d ∞ # Top
  ≤d-arr-∞ : ∀ {A B C D}
    → C ≤d ∞ # A
    → B ≤d ∞ # D
    → A ⇒ B ≤d ∞ # C ⇒ D
  ≤d-rcd∞ : ∀ {A B l}
    → A ≤d ∞ # B
    → τ⟦ l ↦ A ⟧ ≤d ∞ # τ⟦ l ↦ B ⟧
  ≤d-arr-S⇐ : ∀ {A B C D j}
    → C ≤d ∞ # A
    → B ≤d 𝕚 (𝕓 j) # D
    → A ⇒ B ≤d 𝕚 (𝕓 (S⇐ j)) # A ⇒ D
  ≤d-rcd-Sl : ∀ {A B l j}
    → A ≤d 𝕚 (𝕓 j) # B
    → τ⟦ l ↦ A ⟧ ≤d 𝕚 (𝕓 (Sl j)) # (τ⟦ l ↦ B ⟧)
  ≤d-and₁ : ∀ {A B C j}
    → A ≤d j # C
    → j ≢ 𝕫
    → A & B ≤d j # C
  ≤d-and₂ : ∀ {A B C j}
    → B ≤d j # C
    → j ≢ 𝕫
    → A & B ≤d j # C
  ≤d-and : ∀ {A B C}
    → A ≤d ∞ # B
    → A ≤d ∞ # C
    → A ≤d ∞ # B & C

≤d-refl∞ : ∀ {A} → A ≤d ∞ # A
≤d-refl∞ {A = Int} = ≤d-int∞
≤d-refl∞ {A = Float} = ≤d-float∞
≤d-refl∞ {A = * x} = ≤d-base∞
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
    → Γ ⊢d 𝕫 # 𝕔 c ⦂ c-τ c

  ⊢d-var : ∀ {Γ x A}
    → Γ ∋ x ⦂ A
    → Γ ⊢d 𝕫 # ` x ⦂ A

  ⊢d-ann : ∀ {Γ e A}
    → Γ ⊢d ∞ # e ⦂ A
    → Γ ⊢d 𝕫 # (e ⦂ A) ⦂ A

  ⊢d-lam₁ : ∀ {Γ e A B}
    → Γ , A ⊢d ∞ # e ⦂ B
    → Γ ⊢d ∞ # (ƛ e) ⦂ A ⇒ B

  ⊢d-lam₂ : ∀ {Γ e A B i}
    → Γ , A ⊢d 𝕚 i # e ⦂ B
    → Γ ⊢d 𝕚 (S⇒ i) # (ƛ e) ⦂ A ⇒ B

  ⊢d-app⇐ : ∀ {Γ e₁ e₂ A B j}
    → Γ ⊢d 𝕚 (𝕓 (S⇐ j)) # e₁ ⦂ A ⇒ B
    → Γ ⊢d ∞ # e₂ ⦂ A
    → Γ ⊢d 𝕚 (𝕓 j) # e₁ · e₂ ⦂ B

{-
  ⊢d-app∞∞ : ∀ {Γ e₁ e₂ A B}
    → Γ ⊢d ∞ # e₁ ⦂ A ⇒ B
    → Γ ⊢d ∞ # e₂ ⦂ A
    → Γ ⊢d ∞ # e₁ · e₂ ⦂ B
-}    

  ⊢d-app∞ : ∀ {Γ e₁ e₂ A B}
    → Γ ⊢d ∞ # e₁ ⦂ A ⇒ B
    → Γ ⊢d 𝕫 # e₂ ⦂ A
    → Γ ⊢d ∞ # e₁ · e₂ ⦂ B

  ⊢d-app⇒ : ∀ {Γ e₁ e₂ A B j}
    → Γ ⊢d 𝕚 (S⇒ j) # e₁ ⦂ A ⇒ B
    → Γ ⊢d 𝕫 # e₂ ⦂ A
    → Γ ⊢d 𝕚 j # e₁ · e₂ ⦂ B

  ⊢d-sub : ∀ {Γ e A B i}
    → Γ ⊢d 𝕫 # e ⦂ B
    → B ≤d i # A
    → i ≢ 𝕫
    → Γ ⊢d i # e ⦂ A

  ⊢d-& : ∀ {Γ e A B}
    → Γ ⊢d ∞ # e ⦂ A
    → Γ ⊢d ∞ # e ⦂ B
    → Γ ⊢d ∞ # e ⦂ A & B

  ⊢d-rcd : ∀ {Γ rs As}
    → Γ ⊢r 𝕫 # rs ⦂ As
    → Γ ⊢d 𝕫 # (𝕣 rs) ⦂ As

  ⊢d-prj : ∀ {Γ e l j A}
    → Γ ⊢d 𝕚 (𝕓 (Sl j)) # e ⦂ τ⟦ l ↦ A ⟧
    → Γ ⊢d 𝕚 (𝕓 j) # e 𝕡 l ⦂ A

  ⊢d-prj∞ : ∀ {Γ e l A}
    → Γ ⊢d ∞ # e ⦂ τ⟦ l ↦ A ⟧
    → Γ ⊢d ∞ # e 𝕡 l ⦂ A

data _⊢r_#_⦂_ where

  ⊢r-nil : ∀ {Γ}
    → Γ ⊢r 𝕫 # rnil ⦂ Top

  ⊢r-one : ∀ {Γ e A l}
    → Γ ⊢d 𝕫 # e ⦂ A
    → Γ ⊢r 𝕫 # r⟦ l ↦ e ⟧ rnil ⦂ τ⟦ l ↦ A ⟧

  ⊢r-cons : ∀ {Γ l e rs A As}
    → Γ ⊢d 𝕫 # e ⦂ A
    → Γ ⊢r 𝕫 # rs ⦂ As
    → Γ ⊢r 𝕫 # r⟦ l ↦ e ⟧ rs ⦂ (τ⟦ l ↦ A ⟧ & As)


----------------------------------------------------------------------
--+                                                                +--
--+                            Examples                            +--
--+                                                                +--
----------------------------------------------------------------------

id-fun-& : Term
id-fun-& = (ƛ ` 0) ⦂ (Int ⇒ Int) & (* 1 ⇒ * 1)

⊢id-fun-& : ∅ ⊢d 𝕫 # id-fun-& ⦂ (Int ⇒ Int) & (* 1 ⇒ * 1)
⊢id-fun-& = ⊢d-ann (⊢d-& (⊢d-lam₁ (⊢d-sub (⊢d-var Z) ≤d-int∞ (λ ()))) (⊢d-lam₁ (⊢d-sub (⊢d-var Z) ≤d-base∞ (λ ()))))

example-1-sub : (τ⟦ 1 ↦ (Int ⇒ Int) & (* 1 ⇒ * 1) ⟧ & (τ⟦ 2 ↦ Int ⟧))
                    ≤d 𝕚 (𝕓 (Sl (S⇐ Z))) # (τ⟦ 1 ↦ Int ⇒ Int ⟧)
example-1-sub = ≤d-and₁ (≤d-rcd-Sl (≤d-and₁ (≤d-arr-S⇐ ≤d-int∞ ≤d-Z) (λ ()))) (λ ())
