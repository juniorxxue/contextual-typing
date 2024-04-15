module Poly.Decl where

open import Poly.Common

data Counter : Set where
  Z  : Counter
  ∞  : Counter
  S  : Counter → Counter
  Sτ : Counter → Counter

private
  variable
    Γ : Env n m

infix 3 _:=_∈_
data _:=_∈_ : Fin m → Type m → Env n m → Set where

  Z : ∀ {A} → #0 := A ∈ Γ ,= ↓ty0 A
  S, : ∀ {k A B}
    → k := A ∈ Γ
    → k := A ∈ Γ , B
  S∙ : ∀ {k A}
    → k := ↓ty0 A ∈ Γ
    → #S k := A ∈ Γ ,∙
  S= : ∀ {k A B}
    → k := ↓ty0 A ∈ Γ
    → #S k := A ∈ Γ ,= B

-- apply solutions in Env to a type

-- the function version is hard to destruct in the conclusion
-- thus model it as datatype in the next
infix 5 _⟦_⟧
_⟦_⟧ : (Γ : Env n m) → (A : Type m) → Type m
Γ ⟦ Int ⟧    = Int
Γ ⟦ ‶ X ⟧    = applying Γ X
  where applying : (Γ : Env n m) → (X : Fin m) → Type m
        applying (Γ , A) X       = applying Γ X
        applying (Γ ,∙) #0       = ‶ #0
        applying (Γ ,∙) (#S X)   = ↑ty0 (applying Γ X)
        applying (Γ ,= A) #0     = ↑ty0 A
        applying (Γ ,= A) (#S X) = ↑ty0 (applying Γ X)
Γ ⟦ A `→ B ⟧ = (Γ ⟦ A ⟧) `→ (Γ ⟦ B ⟧)
Γ ⟦ `∀ A ⟧   = `∀ ((Γ ,∙) ⟦ A ⟧)

infix 4 _⟦_⟧⟹'_
data _⟦_⟧⟹'_ : Env n m → Fin m → Type m → Set where
  slv'-, : ∀ {A B X}
    → Γ ⟦ X ⟧⟹' B
    → (Γ , A) ⟦ X ⟧⟹' B
  slv'-∙-Z : 
      (Γ ,∙) ⟦ #0 ⟧⟹' ‶ #0
  slv'-∙-S : ∀ {X A A'}
    → Γ ⟦ X ⟧⟹' A
    → A' ≡ ↑ty0 A
    → (Γ ,∙) ⟦ #S X ⟧⟹' A'
--    → (Γ ,∙) ⟦ #S X ⟧⟹' ↑ty0 A
  slv'-=-Z : ∀ {A A'}
    → A' ≡ ↑ty0 A
    → (Γ ,= A) ⟦ #0 ⟧⟹' A'
  slv'-=-S : ∀ {A X B B'}
    → Γ ⟦ X ⟧⟹' B
    → B' ≡ ↑ty0 B
    → (Γ ,= A) ⟦ #S X ⟧⟹' B'

infix 4 _⟦_⟧⟹_
data _⟦_⟧⟹_ : Env n m → Type m → Type m → Set where
  slv-int : Γ ⟦ Int ⟧⟹ Int
  slv-var : ∀ {X A}
    → Γ ⟦ X ⟧⟹' A
    → Γ ⟦ ‶ X ⟧⟹ A
  slv-arr : ∀ {A B A' B'}
    → Γ ⟦ A ⟧⟹ A'
    → Γ ⟦ B ⟧⟹ B'
    → Γ ⟦ A `→ B ⟧⟹ A' `→ B'
  slv-∀ : ∀ {A A'}
    → (Γ ,∙) ⟦ A ⟧⟹ A'
    → Γ ⟦ `∀ A ⟧⟹ `∀ A'    

infix 3 _⊢_#_⦂_
infix 3 _⊢_#_≤_

data _⊢_#_≤_ : Env n m → Counter → Type m → Type m → Set where
  s-refl : ∀ {A A'}
    → (ap : Γ ⟦ A ⟧⟹ A')
    → Γ ⊢ Z # A ≤ A'
-- → Γ ⊢ Z # A ≤ Γ ⟦ A ⟧
  s-int :
      Γ ⊢ ∞ # Int ≤ Int
  s-var : ∀ {X} 
    → Γ ⊢ ∞ # ‶ X ≤ ‶ X
  s-arr₁ : ∀ {A B C D}
    → Γ ⊢ ∞ # C ≤ A
    → Γ ⊢ ∞ # B ≤ D
    → Γ ⊢ ∞ # A `→ B ≤ C `→ D
  s-arr₂ : ∀ {j A B C D}
    → Γ ⊢ ∞ # C ≤ A
    → Γ ⊢ j # B ≤ D
    → Γ ⊢ S j # A `→ B ≤ C `→ D
  s-∀ : ∀ {A B}
    → Γ ,∙ ⊢ ∞ # A ≤ B
    → Γ ⊢ ∞ # `∀ A ≤ `∀ B
  s-∀l : ∀ {j A B C}
    → Γ ,= B ⊢ j # A ≤ ↑ty0 C 
    → Γ ⊢ S j # `∀ A ≤ C
  s-∀lτ : ∀ {j A B C}
    → Γ ,= B ⊢ j # A ≤ ↑ty0 C 
    → Γ ⊢ Sτ j # `∀ A ≤ C
  -- two atomic rules, not sure where to use them
  s-var-l : ∀ {X j A B}
    → X := B ∈ Γ
    → Γ ⊢ j # B ≤ A
    → Γ ⊢ j # ‶ X ≤ A
  s-var-r : ∀ {X j A B}
    → X := B ∈ Γ
    → Γ ⊢ j # A ≤ B
    → Γ ⊢ j # A ≤ ‶ X

data _⊢_#_⦂_ : Env n m → Counter → Term n m → Type m → Set where
  ⊢lit : ∀ {i} → Γ ⊢ Z # (lit i) ⦂ Int
  ⊢var : ∀ {x A}
    → lookup Γ x ≡ A
    → Γ ⊢ Z # ` x ⦂ A
  ⊢ann : ∀ {e A}
    → Γ ⊢ ∞ # e ⦂ A
    → Γ ⊢ Z # (e ⦂ A) ⦂ A
  ⊢lam₁ : ∀ {e A B}
    → Γ , A ⊢ ∞ # e ⦂ B
    → Γ ⊢ ∞ # ƛ e ⦂ A `→ B
  ⊢lam₂ : ∀ {e j A B}
    → Γ , A ⊢ j # e ⦂ B
    → Γ ⊢ S j # ƛ e ⦂ A `→ B
  ⊢app₁ : ∀ {e₁ e₂ j A B}
    → Γ ⊢ Z # e₁ ⦂ A `→ B
    → Γ ⊢ ∞ # e₂ ⦂ A
    → Γ ⊢ j # e₁ · e₂ ⦂ B
  ⊢app₂ : ∀ {e₁ e₂ j A B}
    → Γ ⊢ S j # e₁ ⦂ A `→ B
    → Γ ⊢ Z # e₂ ⦂ A
    → Γ ⊢ j # e₁ · e₂ ⦂ B
  ⊢sub : ∀ {e j A B}
    → Γ ⊢ Z # e ⦂ B
    → Γ ⊢ j # B ≤ A
    → Γ ⊢ j # e ⦂ A
  ⊢tabs₁ : ∀ {e A}
    → Γ ,∙ ⊢ Z # e ⦂ A
    → Γ ⊢ Z # Λ e ⦂ `∀ A    
  ⊢tapp : ∀ {e j A B}
    → Γ ⊢ Sτ j # e ⦂ B
    → Γ ⊢ j # e [ A ] ⦂ B

idEnv : Env 1 0
idEnv = ∅ , `∀ (‶ #0 `→ ‶ #0)

id[Int]1 : idEnv ⊢ Z # ((` #0) [ Int ]) · (lit 1) ⦂ Int
id[Int]1 = ⊢app₁ (⊢tapp (⊢sub (⊢var refl) (s-∀lτ (s-refl (slv-arr (slv-var (slv'-=-Z refl)) (slv-var (slv'-=-Z refl)))))))
                 (⊢sub ⊢lit s-int)

idExp : Term 0 0
idExp = Λ (((ƛ ` #0) ⦂ ‶ #0 `→ ‶ #0))

idExp[Int]1 : ∅ ⊢ Z # (idExp [ Int ]) · (lit 1) ⦂ Int
idExp[Int]1 = ⊢app₁ (⊢tapp (⊢sub (⊢tabs₁ (⊢ann (⊢lam₁ (⊢sub (⊢var refl) s-var))))
                                 (s-∀lτ (s-refl (slv-arr (slv-var (slv'-=-Z refl)) (slv-var (slv'-=-Z refl)))))))
                    (⊢sub ⊢lit s-int)

idExp[Int] : ∅ ⊢ Z # idExp [ Int ] ⦂ Int `→ Int
idExp[Int] = ⊢tapp (⊢sub (⊢tabs₁ (⊢ann (⊢lam₁ (⊢sub (⊢var refl) s-var))))
                         (s-∀lτ (s-refl (slv-arr (slv-var (slv'-=-Z refl)) (slv-var (slv'-=-Z refl))))))

-- implicit inst
id1 : idEnv ⊢ Z # (` #0) · (lit 1) ⦂ Int
id1 = ⊢app₂ (⊢sub (⊢var refl)
                  (s-∀l (s-refl (slv-arr (slv-var (slv'-=-Z refl)) (slv-var (slv'-=-Z refl))))))
            ⊢lit
