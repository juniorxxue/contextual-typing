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
  
infix 3 _⊢_#_⦂_
infix 3 _⊢_#_≤_

data _⊢_#_≤_ : Env n m → Counter → Type m → Type m → Set where
  s-refl : ∀ {A}
    → Γ ⊢ Z # A ≤ A -- applying solutions here
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
id[Int]1 = ⊢app₁ (⊢tapp (⊢sub (⊢var refl) (s-∀lτ {!!})))
                 (⊢sub ⊢lit s-int)

idExp : Term 0 0
idExp = Λ (((ƛ ` #0) ⦂ ‶ #0 `→ ‶ #0))

idExp[Int]1 : ∅ ⊢ Z # (idExp [ Int ]) · (lit 1) ⦂ Int
idExp[Int]1 = ⊢app₁ (⊢tapp (⊢sub (⊢tabs₁ (⊢ann (⊢lam₁ (⊢sub (⊢var refl) s-var))))
                                 (s-∀lτ {!!})))
                    (⊢sub ⊢lit s-int)

idExp[Int] : ∅ ⊢ Z # idExp [ Int ] ⦂ Int `→ Int
idExp[Int] = ⊢tapp (⊢sub (⊢tabs₁ (⊢ann (⊢lam₁ (⊢sub (⊢var refl) s-var))))
                         (s-∀lτ {!!}))

-- implicit inst
id1 : idEnv ⊢ Z # (` #0) · (lit 1) ⦂ Int
id1 = ⊢app₂ (⊢sub (⊢var refl)
                  (s-∀l {!!}))
            ⊢lit
