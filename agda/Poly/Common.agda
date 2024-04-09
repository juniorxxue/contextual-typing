module Poly.Common where
-- shared constructs between Decl. and Algo.

open import Poly.Prelude public

----------------------------------------------------------------------
--+                             Syntax                             +--
----------------------------------------------------------------------

infixr 5  ƛ_
infixl 7  _·_
infix  9  `_
infixr 5  Λ_
infix  5  _[_]
infix  5  _⦂_

infix  9  ‶_
infixr 8  _`→_
infixr 8  `∀_

variable
  m n m' : ℕ


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

----------------------------------------------------------------------
--+                          Environments                          +--
----------------------------------------------------------------------

data Env : ℕ → ℕ → Set where
  ∅     : Env 0 0
  _,_   : Env n m → (A : Type m) → Env (1 + n) m
  _,∙   : Env n m → Env n (1 + m)
  _,=_  : Env n m → (A : Type m) → Env n (1 + m)

-- the n ensures we can find the type
lookup : Env n m → Fin n → Type m
lookup (Γ , A) #0     = A
lookup (Γ , A) (#S k) = lookup Γ k
lookup (Γ ,∙) k       = ↑ty0 (lookup Γ k)
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

-- unshift is just substing with a random type
↓ty0 : Type (1 + m) → Type m
↓ty0 A = [ Int ]ˢ A
