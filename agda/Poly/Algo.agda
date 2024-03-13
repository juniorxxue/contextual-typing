module Poly.Algo where

open import Poly.Prelude

infixr 5  ƛ_⇒_
infixl 7  _·_
infix  9  `_
infixr 5  Λ_
infix  5  _[_]

infix  9  ‶_
infixr 8  _`→_
infixr 8  `∀_

private
  variable
    m n : ℕ

data Type : ℕ → Set where
  Int    : Type m
  ‶_     : (X : Fin m) → Type m
  _`→_   : (A : Type m) → (B : Type m) → Type m
  `∀_    : (A : Type (1 + m)) → Type m

data Term : ℕ → ℕ → Set where
  lit      : (i : ℕ) → Term n m
  `_       : (x : Fin n) → Term n m
  ƛ_⇒_     : (A : Type m) → (e : Term (1 + n) m) → Term n m
  _·_      : (e₁ : Term n m) → (e₂ : Term n m) → Term n m
  Λ_       : (e : Term n (1 + m)) → Term n m
  _[_]     : (e : Term n m) → (A : Type m) → Term n m

----------------------------------------------------------------------
--+                             Shift                              +--
----------------------------------------------------------------------

↑ty : Fin (suc m) → Type m → Type (suc m)
↑ty k Int      = Int
↑ty k (‶ X)    = ‶ punchIn k X
↑ty k (A `→ B) = ↑ty k A `→ ↑ty k B
↑ty k (`∀ A)   = `∀ (↑ty (#S k) A)

↑ty0 : Type m → Type (suc m)
↑ty0 {m} = ↑ty {m} #0

-- Env for typing
data Env : ℕ → ℕ → Set where
  ∅     : Env 0 m
  _,_   : Env n m → (A : Type m) → Env (1 + n) m
  _,∙   : Env n m → Env n m
  _,=_  : Env n m → (A : Type m) → Env n m

-- Env for subtyping
data SEnv : ℕ → ℕ → Set where
  𝕓     : Env n m → SEnv n m
  _,∙   : SEnv n m → SEnv n m -- universal variable
  _,^   : SEnv n m → SEnv n m -- existential variable
  _,=_  : SEnv n m → (A : Type m) → SEnv (1 + n) m

↑Γ : (k : Fin (suc m)) → Env n m → Env n (suc m)
↑Γ k ∅        = ∅
↑Γ k (Γ , A)  = ↑Γ k Γ , ↑ty k A
↑Γ k (Γ ,∙)   = ↑Γ k Γ ,∙
↑Γ k (Γ ,= A) = ↑Γ k Γ ,= ↑ty k A

↑Γ0 : Env n m → Env n (suc m)
↑Γ0 = ↑Γ #0

-- the n ensures we can find the type
lookup : Env n m → Fin n → Type m
lookup (Γ , A) #0     = A
lookup (Γ , A) (#S k) = lookup Γ k
lookup (Γ ,∙) k       = lookup Γ k
lookup (Γ ,= A) k     = lookup Γ k

----------------------------------------------------------------------
--+                           Type Subst                           +--
----------------------------------------------------------------------

-- shift for term
↑tm : Fin (suc n) → Term n m → Term (suc n) m
↑tm k (lit i)    = lit i
↑tm k (` x)      = ` (punchIn k x)
↑tm k (ƛ A ⇒ e)  = ƛ A ⇒ (↑tm (#S k) e)
↑tm k (e₁ · e₂)  = ↑tm k e₁ · ↑tm k e₂
↑tm k (Λ e)      = Λ (↑tm k e)
↑tm k (e [ A ])  = ↑tm k e [ A ]

-- shift type in term
↑ty-in-tm : Fin (suc m) → Term n m → Term n (suc m)
↑ty-in-tm k (lit i)    = lit i
↑ty-in-tm k (` x)      = ` x
↑ty-in-tm k (ƛ A ⇒ e)  = ƛ (↑ty k A) ⇒ (↑ty-in-tm k e)
↑ty-in-tm k (e₁ · e₂)  = ↑ty-in-tm k e₁ · ↑ty-in-tm k e₂
↑ty-in-tm k (Λ e)      = Λ (↑ty-in-tm (#S k) e)
↑ty-in-tm k (e [ A ])  = ↑ty-in-tm k e [ ↑ty k A ]

-- subst
infix 6 [_/_]ˢ_

-- forall a. forall b. a -> b -> (forall c. c -> c)
--> forall. forall. 1 -> 0 -> (forall 0 -> 0)
--> [forall.0 -> 1] (forall. 1 -> 0 -> (forall 0 -> 0))
--> I realised that the B here, should be in higher-indices, since it hides in forall

[_/_]ˢ_ : Fin (suc m) → Type m → Type (suc m) → Type m
[ k / A ]ˢ Int      = Int
[ k / A ]ˢ (‶ X) with k #≟ X
... | yes p = A
... | no ¬p = ‶ punchOut {i = k} {j = X} ¬p
[ k / A ]ˢ (B `→ C) = ([ k / A ]ˢ B) `→ ([ k / A ]ˢ C)
[ k / A ]ˢ (`∀ B)   = `∀ ([ #S k / ↑ty0 A ]ˢ B)

infix 6 [_]ˢ_
[_]ˢ_ : Type m → Type (suc m) → Type m
[_]ˢ_ = [_/_]ˢ_ #0

----------------------------------------------------------------------
--+                             Typing                             +--
----------------------------------------------------------------------

infixr 7 [_]↝_
infixr 7 ⟦_⟧↝_

data Context : ℕ → ℕ → Set where
  □     : Context n m
  τ_    : Type m → Context n m
  [_]↝_ : Term n m → Context n m → Context n m
  ⟦_⟧↝_ : Type m → Context n m → Context n m

private
  variable
    Γ : Env n m
    Ψ : SEnv n m
    Σ : Context n m

infix 3 _⊢_⇒_⇒_
infix 3 _⊢_≤_⊣_↪_

data _⊢_⇒_⇒_ : Env n m → Context n m → Term n m → Type m → Set
data _⊢_≤_⊣_↪_ : SEnv n m → Type m → Context n m → SEnv n m → Type m → Set

data _⊢_⇒_⇒_ where

  ⊢lit : ∀ {i}
    → Γ ⊢ □ ⇒ lit i ⇒ Int

  ⊢var : ∀ {x A}
    → Γ ⊢ □ ⇒ ` x ⇒ A
  
data _⊢_≤_⊣_↪_ where

