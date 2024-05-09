module Poly.Algo where

open import Poly.Common

-- Env for algorithmic subtyping
data SEnv : ℕ → ℕ → Set where
  𝕓     : (Γ : Env n m) → SEnv n m
  _,∙   : SEnv n m → SEnv n (1 + m) -- universal variable
  _,^   : SEnv n m → SEnv n (1 + m) -- existential variable
  _,=_  : SEnv n m → (A : Type m) → SEnv n (1 + m) -- solved equation

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
-- this seems to be dangerous, I give a solution which could never reach (`e` is shifted)
-- so that I no need to touch the indices in expression `e`
Ψ→Γ (Ψ ,^)   = (Ψ→Γ Ψ) ,= Int
Ψ→Γ (Ψ ,= A) = (Ψ→Γ Ψ) ,= A

infix 3 _↪_,_
data _↪_,_ : SEnv n (1 + m) → Env n m → Type m → Set where
  
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
infix 5 _⟦_⟧_
_⟦_⟧_ : (Ψ : SEnv n m) → (A : Type m) → (Ψ ⊢c A) → Type m
Ψ ⟦ Int ⟧ p = Int
Ψ ⟦ ‶ X ⟧ p = applying Ψ X p
  where
    applying : (Ψ : SEnv n m) → (X : Fin m) → (Ψ ⊢c ‶ X) → Type m
    applying (𝕓 Γ) X p                    = ‶ X
    applying (Ψ ,∙) #0 p                  = ‶ #0
    applying (Ψ ,∙) (#S X) (⊢c-var∙S p)   = ↑ty0 (applying Ψ X p)
    applying (Ψ ,^) (#S X) (⊢c-var^S p)   = ↑ty0 (applying Ψ X p)
    applying (Ψ ,= A) #0 p                = ↑ty0 A
    applying (Ψ ,= A) (#S X) (⊢c-var=S p) = ↑ty0 (applying Ψ X p)
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
    → [ A / #0 ] (Ψ ,^) ⟹ (Ψ ,= (↓ty0 A))

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

-- ⚠️ this impl is changed recently, not justiifed alot
infix 3 _:=_∈'_
data _:=_∈'_ : Fin m → Type m → Env n m → Set where
  Z  : ∀ {A} → #0 := A ∈' Γ ,= ↓ty0 A
  S∙ : ∀ {k} {A}
    → k := ↓ty0 A ∈' Γ
    → #S k := A ∈' Γ ,∙
  S= : ∀ {k A B}
    → k := ↓ty0 A ∈' Γ
    → #S k := A ∈' Γ ,= B
  k, : ∀ {k A B}
    → k := A ∈' Γ
    → k := A ∈' Γ , B 

infix 3 _:=_∈_
data _:=_∈_ : Fin m → Type m → SEnv n m → Set where

--  Z : ∀ {A} → #0 := A ∈ Ψ ,= ↓ty0 A
  kΓ : ∀ {k} {A}
    → k := A ∈' Γ
    → k := A ∈ (𝕓 Γ)
  S^ : ∀ {k} {A : Type (1 + m)}
    → k := ↓ty0 A ∈ Ψ
    → #S k := A ∈ Ψ ,^
  S∙ : ∀ {k} {A : Type (1 + m)}
    → k := ↓ty0 A ∈ Ψ
    → #S k := A ∈ Ψ ,∙
  S= : ∀ {k B} {A : Type (1 + m)}
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
    → (x∈Γ : lookup Γ x ≡ A)
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
    → Γ ⊢ □ ⇒ g ⇒ A          --- Γ ⊢ Z # e : A
    → 𝕓 Γ ⊢ A ≤ Σ ⊣ Ψ ↪ B    --- Γ ⊢ j # A ≤ B
    → Γ ⊢ Σ ⇒ g ⇒ B          --- Γ ⊢ j # e ∶ B

  -- design choices here,
  -- (1) we maybe need a checking for tabs
  -- (2) we need a context (must have, if we intend to be consistent)
  ⊢tabs₁ : ∀ {e A}
    → Γ ,∙ ⊢ □ ⇒ e ⇒ A
    → Γ ⊢ □ ⇒ Λ e ⇒ `∀ A

  ⊢tapp : ∀ {e A B}
    → Γ ⊢ ⟦ A ⟧↝ Σ ⇒ e ⇒ B
    → Γ ⊢ Σ ⇒ e [ A ] ⇒ B
  
data _⊢_≤_⊣_↪_ where
  s-int :
      Ψ ⊢ Int ≤ τ Int ⊣ Ψ ↪ Int

  s-empty : ∀ {A}
    → (p : Ψ ⊢c A)
    → Ψ ⊢ A ≤ □ ⊣ Ψ ↪ Ψ ⟦ A ⟧ p

  s-var : ∀ {X}
    → Ψ ⊢ ‶ X ≤ τ (‶ X) ⊣ Ψ ↪ ‶ X

  s-ex-l^ : ∀ {A X}
    → Ψ ⊢c A
    → X ^∈ Ψ
    → [ A / X ] Ψ ⟹ Ψ'
    → Ψ ⊢ ‶ X ≤ τ A ⊣ Ψ' ↪ A

  s-ex-l= : ∀ {A A₁ A₂ B X}
    → Ψ ⊢c A
    → X := B ∈ Ψ
    → Ψ ⊢ B ≤ τ A ⊣ Ψ₁ ↪ A₁
--    → Ψ₁ ⊢ A ≤ τ B ⊣ Ψ₂ ↪ A₂
    → Ψ ⊢ ‶ X ≤ τ A ⊣ Ψ₂ ↪ A₂

  s-ex-r^ : ∀ {A X}
    → Ψ ⊢c A
    → X ^∈ Ψ
    → [ A / X ] Ψ ⟹ Ψ'
    → Ψ ⊢ A ≤ τ (‶ X) ⊣ Ψ' ↪ A

  s-ex-r= : ∀ {A A₂ B X}
    → Ψ ⊢c A
    → X := B ∈ Ψ
--    → Ψ ⊢ B ≤ τ A ⊣ Ψ₁ ↪ A₁
    → Ψ₁ ⊢ A ≤ τ B ⊣ Ψ₂ ↪ A₂
    → Ψ ⊢ A ≤ τ (‶ X) ⊣ Ψ₂ ↪ A₂

  s-arr : ∀ {A B C D A' D'}
    → Ψ₁ ⊢ C ≤ τ A ⊣ Ψ₂ ↪ A'
    → Ψ₂ ⊢ B ≤ τ D ⊣ Ψ₃ ↪ D'
    → Ψ₁ ⊢ A `→ B ≤ τ (C `→ D) ⊣ Ψ₃ ↪ (C `→ D)

  s-term-c : ∀ {A B A' D e}
    → Ψ ⊢c A
    → Ψ ⊢c B
    → (Ψ→Γ Ψ) ⊢ τ A ⇒ e ⇒ A'
    → Ψ ⊢ B ≤ Σ ⊣ Ψ' ↪ D
    → Ψ ⊢ (A `→ B) ≤ ([ e ]↝ Σ) ⊣ Ψ' ↪ A' `→ D

  s-term-o : ∀ {A A' B C D e}
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

  -- explicit type applicatoin
{-
  s-∀-t : ∀ {A B C}
    → Ψ ⊢ [ B ]ˢ A ≤ Σ ⊣ Ψ' ↪ C
    → Ψ ⊢ `∀ A ≤ (⟦ B ⟧↝ Σ) ⊣ Ψ' ↪ C
-}
  s-∀-t : ∀ {A B C}
    → Ψ ,= B ⊢ A ≤ ↑tyΣ0 Σ ⊣ Ψ' ,= B ↪ ↑ty0 C
    → Ψ ⊢ `∀ A ≤ (⟦ B ⟧↝ Σ) ⊣ Ψ' ↪ C

----------------------------------------------------------------------
--+                            Examples                            +--
----------------------------------------------------------------------

idEnv : Env 1 0
idEnv = ∅ , `∀ (‶ #0 `→ ‶ #0)

sub-id[Int]1 : ∀ {Γ : Env n m} → 𝕓 Γ ⊢ `∀ ‶ #0 `→ ‶ #0 ≤ ⟦ Int ⟧↝ [ lit 1 ]↝ □ ⊣ 𝕓 Γ ↪ Int `→ Int
sub-id[Int]1 {Γ = Γ} = s-∀-t (s-term-c ⊢c-var=0
                               ⊢c-var=0
                               (⊢sub {Ψ = 𝕓 (Γ ,= Int)} ⊢lit (s-ex-r= ⊢c-int (kΓ Z) s-int))
                               (s-empty ⊢c-var=0))

sub-id[Int] : ∀ {Γ : Env n m} → 𝕓 Γ ⊢ `∀ ‶ #0 `→ ‶ #0 ≤ ⟦ Int ⟧↝ □ ⊣ 𝕓 Γ ↪ Int `→ Int
sub-id[Int] = s-∀-t (s-empty (⊢c-arr ⊢c-var=0 ⊢c-var=0))

sub-id1 : ∀ {Γ : Env n m} → 𝕓 Γ ⊢ `∀ ‶ #0 `→ ‶ #0 ≤ [ lit 1 ]↝ □ ⊣ 𝕓 Γ ↪ Int `→ Int
sub-id1 = s-∀l-eq (s-term-o ⊢o-var^0
                           ⊢lit
                           (s-ex-r^ ⊢c-int Z ⟹^0)
                           (s-empty ⊢c-var=0))

id[Int]1 : idEnv ⊢ □ ⇒ ((` #0) [ Int ]) · (lit 1) ⇒ Int
id[Int]1 = ⊢app (⊢tapp (⊢sub (⊢var refl)
                             sub-id[Int]1))
idExp : Term 0 0
idExp = Λ (((ƛ ` #0) ⦂ ‶ #0 `→ ‶ #0))

idExp[Int]1 : ∅ ⊢ □ ⇒ (idExp [ Int ]) · (lit 1) ⇒ Int
idExp[Int]1 = ⊢app (⊢tapp (⊢sub (⊢tabs₁ (⊢ann (⊢lam₁ (⊢sub (⊢var refl) s-var)))) (sub-id[Int]1 {Γ = ∅})))

idExp[Int] : ∅ ⊢ □ ⇒ idExp [ Int ] ⇒ Int `→ Int
idExp[Int] = ⊢tapp (⊢sub (⊢tabs₁ (⊢ann (⊢lam₁ (⊢sub (⊢var refl) s-var)))) sub-id[Int])

-- implicit inst
id1 : idEnv ⊢ □ ⇒ (` #0) · (lit 1) ⇒ Int
id1 = ⊢app (⊢sub (⊢var refl) sub-id1)


-- [e1] -> [e2] -> [e3] -> []
-- ------- Inf----- Chk -------

-- [1] -> [2] -> [] -- can we ensure the order of inference of 1 / 2
