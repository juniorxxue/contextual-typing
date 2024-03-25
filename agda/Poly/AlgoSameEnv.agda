module Poly.AlgoSameEnv where

open import Poly.Prelude

infixr 5  ƛ_
infixl 7  _·_
infix  9  `_
infixr 5  Λ_
infix  5  _[_]
infix  5  _⦂_

infix  9  ‶_
infixr 8  _`→_
infixr 8  `∀_

private
  variable
    m n : ℕ

#1 : Fin (2 + n)
#1 = #S #0

#2 : Fin (3 + n)
#2 = #S (#S #0)

data Type : ℕ → Set where
  Int    : Type m
  ‶_     : (X : Fin m) → Type m
  _`→_   : (A : Type m) → (B : Type m) → Type m
  `∀_    : (A : Type (1 + m)) → Type m

data Term : ℕ → ℕ → Set where
  lit      : (i : ℕ) → Term n m
  `_       : (x : Fin n) → Term n m
  ƛ_       : (e : Term (1 + n) m) → Term n m
  _·_      : (e₁ : Term n m) → (e₂ : Term n m) → Term n m
  _⦂_      : (e : Term n m) → (A : Type m) → Term n m
  Λ_       : (e : Term n (1 + m)) → Term n m
  _[_]     : (e : Term n m) → (A : Type m) → Term n m

----------------------------------------------------------------------
--+                             Shift                              +--
----------------------------------------------------------------------

↑ty : Fin (1 + m) → Type m → Type (1 + m)
↑ty k Int      = Int
↑ty k (‶ X)    = ‶ punchIn k X
↑ty k (A `→ B) = ↑ty k A `→ ↑ty k B
↑ty k (`∀ A)   = `∀ (↑ty (#S k) A)

↑ty0 : Type m → Type (1 + m)
↑ty0 {m} = ↑ty {m} #0

infixl 5 _,_

-- Env for typing
data Env : ℕ → ℕ → Set where
  ∅     : Env 0 0
  _,_   : Env n m → (A : Type m) → Env (1 + n) m
  _,∙   : Env n m → Env n (1 + m)
  _,^   : Env n m → Env n (1 + m)
  _,=_  : Env n m → (A : Type m) → Env n (1 + m)

-- the n ensures we can find the type
lookup : Env n m → Fin n → Type m
lookup (Γ , A) #0     = A
lookup (Γ , A) (#S k) = lookup Γ k
lookup (Γ ,∙) k       = ↑ty0 (lookup Γ k)
lookup (Γ ,^) k       = ↑ty0 (lookup Γ k)
lookup (Γ ,= A) k     = ↑ty0 (lookup Γ k)

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


private
  variable
    Γ Γ' Γ₁ Γ₂ Γ₃ : Env n m
    Σ : Context n m

-- syntatically defined free variables

-- function first
fvars? : Env n m → Type m → Bool
fvars? Γ Int = false
fvars? (Γ , A) (‶ X) = fvars? Γ (‶ X)
fvars? (Γ ,∙) (‶ #0) = false
fvars? (Γ ,∙) (‶ #S X) = fvars? Γ (‶ X)
fvars? (Γ ,^) (‶ #0) = true
fvars? (Γ ,^) (‶ #S X) = fvars? Γ (‶ X)
fvars? (Γ ,= A) (‶ #0) = false
fvars? (Γ ,= A) (‶ #S X) = fvars? Γ (‶ X)
fvars? Γ (A `→ B) = (fvars? Γ A) ∧ (fvars? Γ B)
fvars? Γ (`∀ A) = fvars? (Γ ,∙) A -- not sure

infix 3 _⊢c_
infix 3 _⊢o_

-- closed: no free existential variables
data _⊢c_ : Env n m → Type m → Set where
  ⊢c-int : Γ ⊢c Int
  ⊢c-term-var : ∀ {A X}
    → Γ ⊢c ‶ X
    → Γ , A ⊢c ‶ X
  ⊢c-var∙0 : Γ ,∙ ⊢c ‶ #0
  ⊢c-var∙S : ∀ {X}
    → Γ ⊢c ‶ X
    → Γ ,∙ ⊢c ‶ #S X
  ⊢c-var^S : ∀ {X}
    → Γ ⊢c ‶ X
    → Γ ,^ ⊢c ‶ #S X
  ⊢c-var=0 : ∀ {A} → Γ ,= A ⊢c ‶ #0
  ⊢c-var=S : ∀ {A X}
    → Γ ⊢c ‶ X
    → Γ ,= A ⊢c ‶ #S X
  ⊢c-arr : ∀ {A B}
    → Γ ⊢c A
    → Γ ⊢c B
    → Γ ⊢c (A `→ B)
  ⊢c-∀ : ∀ {A}
    → Γ ,∙ ⊢c A
    → Γ ⊢c `∀ A

-- open: have free existential variables
data _⊢o_ : Env n m → Type m → Set where
  ⊢o-term-var : ∀ {A X}
    → Γ ⊢o ‶ X
    → Γ , A ⊢o ‶ X
  ⊢o-var∙S : ∀ {X}
    → Γ ⊢o ‶ X
    → Γ ,∙ ⊢o ‶ #S X
  ⊢o-var^0 : Γ ,^ ⊢o ‶ #0
  ⊢o-var^S : ∀ {X}
    → Γ ⊢o ‶ X
    → Γ ,^ ⊢o ‶ #S X
  ⊢o-var=S : ∀ {A X}
    → Γ ⊢o ‶ X
    → Γ ,= A ⊢o ‶ #S X
  ⊢o-arr-l : ∀ {A B}
    → Γ ⊢o A
--    → Γ ⊢o B
    → Γ ⊢o (A `→ B)
  ⊢o-arr-r : ∀ {A B}
--    → Γ ⊢o A
    → Γ ⊢o B
    → Γ ⊢o (A `→ B)    
  ⊢o-∀ : ∀ {A}
    → Γ ,∙ ⊢o A
    → Γ ⊢o `∀ A
    
-- unshifting
-- ↓ty : ∀ (Γ : Env n (1 + m)) → (A : Type (1 + m)) → (fvars? Γ A ≡ false) → Type m
-- ↓ty Γ Int p = {!!}
-- ↓ty (Γ , A) (‶ #0) p = {!!}
-- ↓ty (Γ ,∙) (‶ #0) p = {!!}
-- ↓ty (Γ ,= A) (‶ #0) p = {!!}
-- ↓ty Γ (‶ #S X) p = {!!}
-- ↓ty Γ (A `→ B) p = {!!}
-- ↓ty Γ (`∀ A) p = {!!}

{-
looks like we don't need it

↓ty : (A : Type (1 + m)) → Fin (1 + m) → Type m
↓ty Int k = Int
↓ty (‶ X) k = {!!}
↓ty (A `→ B) k = (↓ty A k) `→ (↓ty B k)
↓ty (`∀ A) k = `∀ (↓ty A (#S k))

↓ty0 : (A : Type (1 + m)) → Type m
↓ty0 A = ↓ty A #0
-}

{-
-- Note: this is intended to be partial, but let's write the function first
[_/_]ᵉ_ : Type m → Fin m → Env n m → Env n m
[ A / k ]ᵉ (Γ , B) = ([ A / k ]ᵉ Γ) , B
[ A / k ]ᵉ (Γ ,∙) = Γ ,∙ -- undefined, fill in a wrong thing (hope it never reaches) will fix later
[ A / #0 ]ᵉ (Γ ,^) = Γ ,= ([ Int ]ˢ A) -- we need a unshift for type A, probably via subst a irrevelent type into it
[ A / #S k ]ᵉ (Γ ,^) = ([ [ Int ]ˢ A / k ]ᵉ Γ) ,^
[ A / #0 ]ᵉ (Γ ,= B) = Γ ,= B -- only defined when A = B
[ A / #S k ]ᵉ (Γ ,= B) =  ([ ([ B ]ˢ A) / k ]ᵉ Γ) ,= B
-}

infix 4 [_/_]_⟹_

data [_/_]_⟹_ : Type m → Fin m → Env n m → Env n m → Set where
  ⟹, : ∀ {Γ Γ' : Env n m} {k A B}
    → [ A / k ] Γ ⟹ Γ'
    → [ A / k ] (Γ , B) ⟹ Γ' , B
    
  ⟹^0 : ∀ {Γ : Env n m} {A}
    → [ A / #0 ] (Γ ,^) ⟹ Γ ,= ([ Int ]ˢ A)

  ⟹^S : ∀ {Γ Γ' : Env n m} {A k}
    → [ [ Int ]ˢ A / k ] Γ ⟹ Γ'
    → [ A / #S k ] (Γ ,^) ⟹ Γ' ,^

  ⟹=0 : ∀ {Γ : Env n m} {A B}
    → [ A / #0 ] (Γ ,= B) ⟹ Γ ,= B -- this is wrong

  ⟹=S : ∀ {Γ Γ' : Env n m} {A B k}
    → [ [ B ]ˢ A / k ] Γ ⟹ Γ'
    → [ A / #S k ] (Γ ,= B) ⟹ Γ' ,= B

infix 3 _⊢_⇒_⇒_
infix 3 _⊢_≤_⊣_↪_

data _⊢_⇒_⇒_ : Env n m → Context n m → Term n m → Type m → Set
-- we cannot syntactically distinguish the result type here, which should contain unsolved variables
data _⊢_≤_⊣_↪_ : Env n m → Type m → Context n m → Env n m → Type m → Set

data _⊢_⇒_⇒_ where

  ⊢lit : ∀ {i}
    → Γ ⊢ □ ⇒ lit i ⇒ Int

  ⊢var : ∀ {x A}
    → lookup Γ x ≡ A -- could be replaced by datatype, but later
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
    → Γ ⊢ A ≤ Σ ⊣ Γ' ↪ B
    → Γ ⊢ Σ ⇒ g ⇒ B

  -- design choices here,
  -- (1) we maybe need a checking for tabs
  -- (2) we need a context (must have, if we intend to be consistent)
  ⊢tabs₁ : ∀ {e A}
    → Γ ,∙ ⊢ □ ⇒ e ⇒ A
    → Γ ⊢ □ ⇒ Λ e ⇒ `∀ A

  ⊢tabs₂ : ∀ {e A B}
    → Γ ,∙ ⊢ ↑tyΣ0 Σ ⇒ e ⇒ B
    → Γ ⊢ ⟦ A ⟧↝ Σ ⇒ Λ e ⇒ [ A ]ˢ B    

  ⊢tapp : ∀ {e A B}
    → Γ ⊢ ⟦ A ⟧↝ Σ ⇒ e ⇒ B
    → Γ ⊢ Σ ⇒ e [ A ] ⇒ B
  
data _⊢_≤_⊣_↪_ where
  s-int :
      Γ ⊢ Int ≤ τ Int ⊣ Γ ↪ Int

  s-empty : ∀ {A}
    → Γ ⊢c A
    → Γ ⊢ A ≤ □ ⊣ Γ ↪ A

  s-ex-l : ∀ {A X}
    → Γ ⊢c A
    → [ A / X ] Γ ⟹ Γ'
    → Γ ⊢ ‶ X ≤ τ A ⊣ Γ' ↪ A

  s-ex-r : ∀ {A X}
    → Γ ⊢c A
    → [ A / X ] Γ ⟹ Γ'
    → Γ ⊢ A ≤ τ (‶ X) ⊣ Γ' ↪ A

  s-arr : ∀ {A B C D A' D'}
    → Γ₁ ⊢ C ≤ τ A ⊣ Γ₂ ↪ A'
    → Γ₂ ⊢ B ≤ τ D ⊣ Γ₃ ↪ D'
    → Γ₁ ⊢ A `→ B ≤ τ (C `→ D) ⊣ Γ₃ ↪ (C `→ D)

  s-term-no : ∀ {A B C D e}
    → Γ ⊢c A
    → Γ ⊢ τ A ⇒ e ⇒ C
    → Γ ⊢ B ≤ Σ ⊣ Γ' ↪ D
    → Γ ⊢ (A `→ B) ≤ ([ e ]↝ Σ) ⊣ Γ' ↪ A `→ D

  s-term : ∀ {A A' B C D e}
    → Γ ⊢o A
    → Γ ⊢ □ ⇒ e ⇒ C
    → Γ ⊢ C ≤ τ A ⊣ Γ₁ ↪ A'
    → Γ₁ ⊢ B ≤ Σ ⊣ Γ₂ ↪ D
    → Γ ⊢ A `→ B ≤ ([ e ]↝ Σ) ⊣ Γ₂ ↪ A' `→ D

  s-∀ : ∀ {A B C}
    → Γ ,∙ ⊢ A ≤ τ B ⊣ Γ' ,∙ ↪ C
    → Γ ⊢ `∀ A ≤ τ (`∀ B) ⊣ Γ' ↪ `∀ C

  s-∀l-^ : ∀ {A B e}
    → Γ ,^ ⊢ A ≤ ↑tyΣ0 ([ e ]↝ Σ) ⊣ Γ' ,^ ↪ ↑ty0 B
    → Γ ⊢ `∀ A ≤ ([ e ]↝ Σ) ⊣ Γ' ↪ B

  s-∀l-eq : ∀ {A B C e}
    → Γ ,^ ⊢ A ≤ ↑tyΣ0 ([ e ]↝ Σ) ⊣ Γ' ,= C ↪ ↑ty0 B
    → Γ ⊢ `∀ A ≤ ([ e ]↝ Σ) ⊣ Γ' ↪ B
  
----------------------------------------------------------------------
--+                            Examples                            +--
----------------------------------------------------------------------

idEnv : Env 1 0
idEnv = ∅ , (`∀ ‶ #0 `→ ‶ #0)

ex1-id1 : idEnv ⊢ □ ⇒  ` #0 · (lit 1) ⇒ Int
ex1-id1 = ⊢app (⊢sub (⊢var refl) (s-∀l-eq (s-term ⊢o-var^0 ⊢lit (s-ex-r ⊢c-int ⟹^0) {!!})))
-- ⊢app (⊢sub (⊢var refl) (s-∀l-eq (s-term refl ⊢lit (s-ex-r refl) {!!})))

succfEnv : Env 2 0
succfEnv = ∅ , (Int `→ Int) , `∀ (‶ #0 `→ ‶ #0) `→ (‶ #0 `→ ‶ #0)

fsucc : Term 2 0
fsucc = (` #0) · (` #1)

ex2-fsucc : succfEnv ⊢ □ ⇒ fsucc ⇒ Int `→ Int
ex2-fsucc = ⊢app (⊢sub (⊢var refl) (s-∀l-eq (s-term (⊢o-arr-l ⊢o-var^0) (⊢var refl) {!s-arr ? ?!} {!!})))


{-
Γ ⊢ ∀ (0 -> 0) -> (0 -> 0) <: [succ] -> [] ⊣ Γ' ~> (Int -> Int) -> Int -> Int
----------------------------------------------------------------------------- Sub
Γ ⊢ [succ] -> [] => f => (Int -> Int) -> Int -> Int
--------------------------------------------------- App
Γ ⊢ [] => f succ => Int -> Int
-}


{-
-----------------------------------
Γ,^ ⊢ Int -> Int <: 0 -> 0 ⊣ Γ₁ ~> Int -> Int      Γ₁ ⊢ 0 -> 0 <: [] ⊣ Γ₂ ~>
------------------------------------------------------------------------------- S-Term
Γ,^ ⊢ (0 -> 0) -> (0 -> 0) <: [succ] -> [] ⊣ Γ' ,? ~> (Int -> Int) -> Int -> Int
------------------------------------------------------------------------------- ∀L
Γ ⊢ ∀ (0 -> 0) -> (0 -> 0) <: [succ] -> [] ⊣ Γ' ~> (Int -> Int) -> Int -> Int
-}


{-
----------------------------------------------
Γ,^ ⊢ Int -> Int <: 0 -> 0 ⊣ Γ₁ ~> Int -> Int 
-}
