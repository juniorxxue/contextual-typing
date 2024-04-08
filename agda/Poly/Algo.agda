module Poly.Algo where

open import Poly.Common

-- Env for algorithmic subtyping
data SEnv : ℕ → ℕ → Set where
  𝕓     : Env n m → SEnv n m
  _,∙   : SEnv n m → SEnv n (1 + m) -- universal variable
  _,^   : SEnv n m → SEnv n (1 + m) -- existential variable
  _,=_  : SEnv n m → (A : Type m) → SEnv n (1 + m) -- solved equation


----------------------------------------------------------------------
--+                           Type Subst                           +--
----------------------------------------------------------------------

-- shift for term
↑tm : Fin (1 + n) → Term n m → Term (1 + n) m
↑tm k (lit i)    = lit i
↑tm k (` x)      = ` (punchIn k x)
↑tm k (ƛ e)      = ƛ (↑tm (#S k) e)
↑tm k (e₁ · e₂)  = ↑tm k e₁ · ↑tm k e₂
↑tm k (e ⦂ A)    = (↑tm k e) ⦂ A
↑tm k (Λ e)      = Λ (↑tm k e)
↑tm k (e [ A ])  = ↑tm k e [ A ]

-- shift type in term
↑ty-in-tm : Fin (1 + m) → Term n m → Term n (1 + m)
↑ty-in-tm k (lit i)    = lit i
↑ty-in-tm k (` x)      = ` x
↑ty-in-tm k (ƛ e)      = ƛ (↑ty-in-tm k e)
↑ty-in-tm k (e₁ · e₂)  = ↑ty-in-tm k e₁ · ↑ty-in-tm k e₂
↑ty-in-tm k (e ⦂ A)    = (↑ty-in-tm k e) ⦂ (↑ty k A)
↑ty-in-tm k (Λ e)      = Λ (↑ty-in-tm (#S k) e)
↑ty-in-tm k (e [ A ])  = ↑ty-in-tm k e [ ↑ty k A ]

-- subst
infix 6 [_/_]ˢ_

[_/_]ˢ_ : Fin (1 + m) → Type m → Type (1 + m) → Type m
[ k / A ]ˢ Int      = Int
[ k / A ]ˢ (‶ X) with k #≟ X
... | yes p = A
... | no ¬p = ‶ punchOut {i = k} {j = X} ¬p
[ k / A ]ˢ (B `→ C) = ([ k / A ]ˢ B) `→ ([ k / A ]ˢ C)
[ k / A ]ˢ (`∀ B)   = `∀ ([ #S k / ↑ty0 A ]ˢ B)

infix 6 [_]ˢ_
[_]ˢ_ : Type m → Type (1 + m) → Type m
[_]ˢ_ = [_/_]ˢ_ #0

infix 6 [_/_]ᵗ_
[_/_]ᵗ_ : Fin (1 + m) → Type m → Term n (1 + m) → Term n m
[ k / A ]ᵗ lit i = lit i
[ k / A ]ᵗ ` x = ` x
[ k / A ]ᵗ (ƛ e) = ƛ ([ k / A ]ᵗ e)
[ k / A ]ᵗ e₁ · e₂ = ([ k / A ]ᵗ e₁) · ([ k / A ]ᵗ e₂)
[ k / A ]ᵗ (e ⦂ B) = ([ k / A ]ᵗ e) ⦂ ([ k / A ]ˢ B)
[ k / A ]ᵗ (Λ e) = Λ [ #S k / ↑ty0 A ]ᵗ e
[ k / A ]ᵗ (e [ B ]) = ([ k / A ]ᵗ e) [ ([ k / A ]ˢ B) ]

infix 6 [_]ᵗ_
[_]ᵗ_ : Type m → Term n (1 + m) → Term n m
[_]ᵗ_ = [_/_]ᵗ_ #0

----------------------------------------------------------------------
--+                             Typing                             +--
----------------------------------------------------------------------

infixr 7 [_]↝_
infixr 7 ⟦_⟧↝_

data Context : ℕ → ℕ → Set where
  □     : Context n m
  τ_    : (A : Type m) → Context n m
  [_]↝_ : (e : Term n m) → Context n m → Context n m
  ⟦_⟧↝_ : (A : Type m) → Context n m → Context n m

↑Σ : Fin (1 + n) → Context n m → Context (1 + n) m
↑Σ k □ = □
↑Σ k (τ A) = τ A
↑Σ k ([ e ]↝ Σ) = [ ↑tm k e ]↝ (↑Σ k Σ)
↑Σ k (⟦ A ⟧↝ Σ) = ⟦ A ⟧↝ (↑Σ k Σ)

↑Σ0 : Context n m → Context (1 + n) m
↑Σ0 = ↑Σ #0

↑tyΣ : Fin (1 + m) → Context n m → Context n (1 + m)
↑tyΣ k □ = □
↑tyΣ k (τ A) = τ (↑ty k A)
↑tyΣ k ([ e ]↝ Σ) = [ ↑ty-in-tm k e ]↝ (↑tyΣ k Σ)
↑tyΣ k (⟦ A ⟧↝ Σ) = ⟦ ↑ty k A ⟧↝ (↑tyΣ k Σ)

↑tyΣ0 : Context n m → Context n (1 + m)
↑tyΣ0 = ↑tyΣ #0

↓ty0 : Type (1 + m) → Type m
↓ty0 A = [ Int ]ˢ A

{-
-- environment substition
[_/ᵉ_] : SEnv n m → Type m → Type m
[ Ψ /ᵉ Int ] = Int
[ Ψ /ᵉ ‶ #0 ] = {!!}
[ Ψ /ᵉ ‶ #S X ] = {!!}
[ Ψ /ᵉ A `→ B ] = ([ Ψ /ᵉ A ]) `→ ([ Ψ /ᵉ B ])
[ Ψ /ᵉ `∀ A ] = {!!}
-}

Ψ→Γ : SEnv n m → Env n m
Ψ→Γ (𝕓 Γ)    = Γ
Ψ→Γ (Ψ ,∙)   = (Ψ→Γ Ψ) ,∙
Ψ→Γ (Ψ ,^)   = {!!}
Ψ→Γ (Ψ ,= A) = (Ψ→Γ Ψ) ,= A

private
  variable
    Γ : Env n m
    Ψ Ψ' Ψ₁ Ψ₂ Ψ₃ : SEnv n m
    Σ : Context n m

infix 3 _⊢c_
infix 3 _⊢o_

-- closed: no free existential variables
data _⊢c_ : SEnv n m → Type m → Set where
  ⊢c-int : Ψ ⊢c Int
  ⊢c-base : ∀ {X}
    → 𝕓 Γ ⊢c ‶ X
  ⊢c-var∙0 : Ψ ,∙ ⊢c ‶ #0
  ⊢c-var∙S : ∀ {X}
    → Ψ ⊢c ‶ X
    → Ψ ,∙ ⊢c ‶ #S X
  ⊢c-var^S : ∀ {X}
    → Ψ ⊢c ‶ X
    → Ψ ,^ ⊢c ‶ #S X
  ⊢c-var=0 : ∀ {A} → Ψ ,= A ⊢c ‶ #0
  ⊢c-var=S : ∀ {A X}
    → Ψ ⊢c ‶ X
    → Ψ ,= A ⊢c ‶ #S X
  ⊢c-arr : ∀ {A B}
    → Ψ ⊢c A
    → Ψ ⊢c B
    → Ψ ⊢c (A `→ B)
  ⊢c-∀ : ∀ {A}
    → Ψ ,∙ ⊢c A
    → Ψ ⊢c `∀ A

-- open: have free existential variables
data _⊢o_ : SEnv n m → Type m → Set where
  ⊢o-var∙S : ∀ {X}
    → Ψ ⊢o ‶ X
    → Ψ ,∙ ⊢o ‶ #S X
  ⊢o-var^0 : Ψ ,^ ⊢o ‶ #0
  ⊢o-var^S : ∀ {X}
    → Ψ ⊢o ‶ X
    → Ψ ,^ ⊢o ‶ #S X
  ⊢o-var=S : ∀ {A X}
    → Ψ ⊢o ‶ X
    → Ψ ,= A ⊢o ‶ #S X
  ⊢o-arr-l : ∀ {A B}
    → Ψ ⊢o A
    → Ψ ⊢o (A `→ B)
  ⊢o-arr-r : ∀ {A B}
    → Ψ ⊢o B
    → Ψ ⊢o (A `→ B)    
  ⊢o-∀ : ∀ {A}
    → Ψ ,∙ ⊢o A
    → Ψ ⊢o `∀ A

-- apply solutions in Env to a type
_⟦_⟧_ : (Ψ : SEnv n m) → (A : Type m) → (Ψ ⊢c A) → Type m
Ψ ⟦ Int ⟧ p = Int
Ψ ⟦ ‶ X ⟧ p = applying Ψ X p
  where
    applying : (Ψ : SEnv n m) → (X : Fin m) → (Ψ ⊢c ‶ X) → Type m
    applying (𝕓 x) X p = ‶ X
    applying (Ψ ,∙) #0 p = ‶ #0
    applying (Ψ ,∙) (#S X) (⊢c-var∙S p) = ↑ty0 (applying Ψ X p)
    applying (Ψ ,^) (#S X) (⊢c-var^S p) = ↑ty0 (applying Ψ X p)
    applying (Ψ ,= A) X p = ↑ty0 A
Ψ ⟦ A `→ B ⟧ ⊢c-arr p p₁ = (Ψ ⟦ A ⟧ p) `→ (Ψ ⟦ B ⟧ p₁)
Ψ ⟦ `∀ A ⟧ ⊢c-∀ p = `∀ ((Ψ ,∙) ⟦ A ⟧ p)

infix 4 [_/_]_⟹_

data [_/_]_⟹_ : Type m → Fin m → SEnv n m → SEnv n m → Set where

{-
  ⟹, : ∀ {Ψ Ψ' : Env n m} {k A B}
    → [ A / k ] Ψ ⟹ Ψ'
    → [ A / k ] (Ψ , B) ⟹ Ψ' , B
-}
    
  ⟹^0 : ∀ {Ψ : SEnv n m} {A}
    → [ A / #0 ] (Ψ ,^) ⟹ Ψ ,= (↓ty0 A)

  ⟹^S : ∀ {Ψ Ψ' : SEnv n m} {A k}
    → [ ↓ty0 A / k ] Ψ ⟹ Ψ'
    → [ A / #S k ] (Ψ ,^) ⟹ Ψ' ,^

{-
  ⟹=0 : ∀ {Ψ : SEnv n m} {A B}
    → [ A / #0 ] (Ψ ,= B) ⟹ Ψ ,= B -- this is wrong, should be some equivlent reasoning

  ⟹=S : ∀ {Ψ Ψ' : SEnv n m} {A B k}
    → [ [ B ]ˢ A / k ] Ψ ⟹ Ψ'
    → [ A / #S k ] (Ψ ,= B) ⟹ Ψ' ,= B
-}

infix 3 _^∈_
data _^∈_ : Fin m → SEnv n m → Set where

  Z : #0 ^∈ Ψ ,^
  S^ : ∀ {k}
    → k ^∈ Ψ
    → #S k ^∈ Ψ ,^
  S∙ : ∀ {k}
    → k ^∈ Ψ
    → #S k ^∈ Ψ ,∙
  S= : ∀ {k A}
    → k ^∈ Ψ
    → #S k ^∈ Ψ ,= A    

infix 3 _:=_∈_
data _:=_∈_ : Fin m → Type m → SEnv n m → Set where

  Z : ∀ {A} → #0 := A ∈ Ψ ,= ↓ty0 A
  S^ : ∀ {k} {A : Type (1 + m')}
    → k := ↓ty0 A ∈ Ψ
    → #S k := A ∈ Ψ ,^
  S∙ : ∀ {k} {A : Type (1 + m')}
    → k := ↓ty0 A ∈ Ψ
    → #S k := A ∈ Ψ ,∙
  S= : ∀ {k B} {A : Type (1 + m')}
    → k := ↓ty0 A ∈ Ψ
    → #S k := A ∈ Ψ ,= B

infix 3 _⊢_⇒_⇒_
infix 3 _⊢_≤_⊣_↪_

data _⊢_⇒_⇒_ : Env n m → Context n m → Term n m → Type m → Set
-- we cannot syntactically distinguish the result type here, which should contain unsolved variables
data _⊢_≤_⊣_↪_ : SEnv n m → Type m → Context n m → SEnv n m → Type m → Set

data _⊢_⇒_⇒_ where

  ⊢lit : ∀ {i}
    → Γ ⊢ □ ⇒ lit i ⇒ Int

  ⊢var : ∀ {x A}
    → lookup Γ x ≡ A
    → Γ ⊢ □ ⇒ ` x ⇒ A

  ⊢ann : ∀ {e A B}
    → Γ ⊢ τ A ⇒ e ⇒ B
    → Γ ⊢ □ ⇒ e ⦂ A ⇒ A

  ⊢app : ∀ {e₁ e₂ A B}
    → Γ ⊢ [ e₂ ]↝ Σ ⇒ e₁ ⇒ A `→ B
    → Γ ⊢ Σ ⇒ e₁ · e₂ ⇒ B

  ⊢lam₁ : ∀ {A B C e}
    → Γ , A ⊢ τ B ⇒ e ⇒ C
    → Γ ⊢ τ (A `→ B) ⇒ ƛ e ⇒ A `→ C

  ⊢lam₂ : ∀ {A B e e₂}
    → Γ ⊢ □ ⇒ e₂ ⇒ A
    → Γ , A ⊢ ↑Σ0 Σ ⇒ e ⇒ B
    → Γ ⊢ [ e₂ ]↝ Σ ⇒ ƛ e ⇒ A `→ B

  ⊢sub : ∀ {g A B}
    → Γ ⊢ □ ⇒ g ⇒ A
    → 𝕓 Γ ⊢ A ≤ Σ ⊣ Ψ ↪ B
    → Γ ⊢ Σ ⇒ g ⇒ B

  -- design choices here,
  -- (1) we maybe need a checking for tabs
  -- (2) we need a context (must have, if we intend to be consistent)
  ⊢tabs₁ : ∀ {e A}
    → Γ ,∙ ⊢ □ ⇒ e ⇒ A
    → Γ ⊢ □ ⇒ Λ e ⇒ `∀ A

{-
  -- alternative approach is to follow the design of let-argument-go-first
  -- modeling a type synonym
  ⊢tabs₂' : ∀ {e A B}
    → Γ ⊢ Σ ⇒ [ A ]ᵗ e ⇒ B
    → Γ ⊢ ⟦ A ⟧↝ Σ ⇒ Λ e ⇒ B
-}    

  -- classic approach, accpet less examples
  ⊢tabs₂ : ∀ {e A B}
    → Γ ,∙ ⊢ ↑tyΣ0 Σ ⇒ e ⇒ B
--    → Γ ⊢ Σ ⇒ Λ e ⇒ `∀ B -- funny premise
    → Γ ⊢ ⟦ A ⟧↝ Σ ⇒ Λ e ⇒ [ A ]ˢ B    

  ⊢tapp : ∀ {e A B}
    → Γ ⊢ ⟦ A ⟧↝ Σ ⇒ e ⇒ B
    → Γ ⊢ Σ ⇒ e [ A ] ⇒ B
  
data _⊢_≤_⊣_↪_ where
  s-int :
      Ψ ⊢ Int ≤ τ Int ⊣ Ψ ↪ Int

  s-empty : ∀ {A}
    → Ψ ⊢c A
    → Ψ ⊢ A ≤ □ ⊣ Ψ ↪ A

  s-ex-l^ : ∀ {A X}
    → Ψ ⊢c A
    → X ^∈ Ψ
    → [ A / X ] Ψ ⟹ Ψ'
    → Ψ ⊢ ‶ X ≤ τ A ⊣ Ψ' ↪ A

  s-ex-l= : ∀ {A A₁ A₂ B X}
    → Ψ ⊢c A
    → X := B ∈ Ψ
    → Ψ ⊢ B ≤ τ A ⊣ Ψ₁ ↪ A₁
    → Ψ₁ ⊢ A ≤ τ B ⊣ Ψ₂ ↪ A₂
    → Ψ ⊢ ‶ X ≤ τ A ⊣ Ψ₂ ↪ A₂

  s-ex-r^ : ∀ {A X}
    → Ψ ⊢c A
    → X ^∈ Ψ
    → [ A / X ] Ψ ⟹ Ψ'
    → Ψ ⊢ A ≤ τ (‶ X) ⊣ Ψ' ↪ A

  s-ex-r= : ∀ {A A₁ A₂ B X}
    → Ψ ⊢c A
    → X := B ∈ Ψ
    → Ψ ⊢ B ≤ τ A ⊣ Ψ₁ ↪ A₁
    → Ψ₁ ⊢ A ≤ τ B ⊣ Ψ₂ ↪ A₂
    → Ψ ⊢ A ≤ τ (‶ X) ⊣ Ψ₂ ↪ A₂

  s-arr : ∀ {A B C D A' D'}
    → Ψ₁ ⊢ C ≤ τ A ⊣ Ψ₂ ↪ A'
    → Ψ₂ ⊢ B ≤ τ D ⊣ Ψ₃ ↪ D'
    → Ψ₁ ⊢ A `→ B ≤ τ (C `→ D) ⊣ Ψ₃ ↪ (C `→ D)

  s-term-no : ∀ {A B C D e}
    → Ψ ⊢c A
    → (Ψ→Γ Ψ) ⊢ τ A ⇒ e ⇒ C
    → Ψ ⊢ B ≤ Σ ⊣ Ψ' ↪ D
    → Ψ ⊢ (A `→ B) ≤ ([ e ]↝ Σ) ⊣ Ψ' ↪ A `→ D

  s-term : ∀ {A A' B C D e}
    → Ψ ⊢o A
    → (Ψ→Γ Ψ) ⊢ □ ⇒ e ⇒ C
    → Ψ ⊢ C ≤ τ A ⊣ Ψ₁ ↪ A'
    → Ψ₁ ⊢ B ≤ Σ ⊣ Ψ₂ ↪ D
    → Ψ ⊢ A `→ B ≤ ([ e ]↝ Σ) ⊣ Ψ₂ ↪ A' `→ D

  s-∀ : ∀ {A B C}
    → Ψ ,∙ ⊢ A ≤ τ B ⊣ Ψ' ,∙ ↪ C
    → Ψ ⊢ `∀ A ≤ τ (`∀ B) ⊣ Ψ' ↪ `∀ C

  s-∀l-^ : ∀ {A B e}
    → Ψ ,^ ⊢ A ≤ ↑tyΣ0 ([ e ]↝ Σ) ⊣ Ψ' ,^ ↪ ↑ty0 B
    → Ψ ⊢ `∀ A ≤ ([ e ]↝ Σ) ⊣ Ψ' ↪ B

  s-∀l-eq : ∀ {A B C e}
    → Ψ ,^ ⊢ A ≤ ↑tyΣ0 ([ e ]↝ Σ) ⊣ Ψ' ,= C ↪ ↑ty0 B
    → Ψ ⊢ `∀ A ≤ ([ e ]↝ Σ) ⊣ Ψ' ↪ B

  
----------------------------------------------------------------------
--+                            Examples                            +--
----------------------------------------------------------------------


