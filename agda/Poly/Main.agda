{-# OPTIONS --allow-unsolved-metas #-}
module Poly.Main where

open import Poly.Prelude

infixr 5  ƛ_
infixl 7  _·_
infix  9  `_
infixr 5  Λ_
infix  5  _⟦_⟧ₐ
infixl 4  _⦂_

infix  9 ‶_
infixr 8 _`→_
infixr 8 `∀_

data Type : Set where
  Int  : Type
  ‶_   : (X : ℕ) → Type -- tvar
  _`→_ : (A : Type) → (B : Type) → Type
  `∀_   : (A : Type) → Type

data Term : Set where
  lit      : (n : ℕ) → Term
  `_       : (x : ℕ) → Term
  ƛ_       : (e : Term) → Term
  _·_      : (e₁ : Term) → (e₂ : Term) → Term
  _⦂_      : (e : Term) → (A : Type) → Term
  Λ_       : (e : Term) → Term -- tabs
  _⟦_⟧ₐ     : (e : Term) → (A : Type) → Term -- tapp

tshift : ℕ → Type → Type
tshift x Int = Int
tshift x (‶ y) with x ≤? y
... | yes p = ‶ (suc y)
... | no ¬p = ‶ y
tshift x (A `→ B) = (tshift x A) `→ (tshift x B)
tshift x (`∀ A) = `∀ tshift (suc x) A

shift : ℕ → Term → Term
shift x (lit n) = lit n
shift x (` y) with x ≤? y
... | yes p = ` (suc y)
... | no ¬p = ` y
shift x (ƛ e) = ƛ shift (suc x) e
shift x (e₁ · e₂) = (shift x e₁) · (shift x e₂)
shift x (e ⦂ A) = (shift x e) ⦂ A
shift x (Λ e) = Λ (shift x e)
shift x (e ⟦ A ⟧ₐ) = (shift x e) ⟦ A ⟧ₐ

shift-type : ℕ → Term → Term
shift-type x (lit n) = lit n
shift-type x (` y) = ` y
shift-type x (ƛ e) = ƛ (shift-type x e)
shift-type x (e₁ · e₂) = (shift-type x e₁) · (shift-type x e₂)
shift-type x (Λ e) = Λ (shift-type (suc x) e)
shift-type x (e ⦂ A) = (shift-type x e) ⦂ (tshift x A)
shift-type x (e ⟦ A ⟧ₐ) = (shift-type x e) ⟦ tshift x A ⟧ₐ

tsubst : Type → ℕ → Type → Type
tsubst Int X T' = Int
tsubst (‶ Y) X T' with <-cmp Y X
... | tri< a ¬b ¬c = ‶ Y
... | tri≈ ¬a b ¬c = T'
... | tri> ¬a ¬b c = ‶ (pred Y)
tsubst (A `→ B) X T' = (tsubst A X T') `→ (tsubst B X T')
tsubst (`∀ T) X T' = `∀ (tsubst T (suc X) (tshift 0 T'))

infix 6 ⟦_⟧s_
⟦_⟧s_ : Type → Type → Type
⟦ A ⟧s B = tsubst B 0 A

infixl  5 _,_
infixl  5 _,∙

data Context : Set where
  ∅     : Context
  _,_   : Context → (A : Type) → Context
  _,∙   : Context → Context

_ : Context
_ = ∅ ,∙ , ‶ 0

get-var : Context → ℕ → Maybe Type
get-var ∅ x = nothing
get-var (Γ , A) zero = just A
get-var (Γ , A) (suc x) = get-var Γ x
get-var (Γ ,∙) x = mmap (tshift 0) (get-var Γ x)

data Counter : Set where
  ∞ : Counter
  Z : Counter
  S : Counter → Counter

infix 3 _⊢_#_⦂_
infix 3 _⊢_#_≤_

data _⊢_#_≤_ : Context → Counter → Type → Type → Set where

  ≤refl : ∀ {Γ A}
    → Γ ⊢ Z # A ≤ A

  ≤int : ∀ {Γ}
    → Γ ⊢ ∞ # Int ≤ Int

  ≤var : ∀ {Γ X}
    → Γ ⊢ ∞ # ‶ X ≤ ‶ X

  ≤arr-∞ : ∀ {Γ A B C D}
    → Γ ⊢ ∞ # C ≤ A
    → Γ ⊢ ∞ # B ≤ D
    → Γ ⊢ ∞ # A `→ B ≤ C `→ D

  ≤∀ : ∀ {Γ A B}
    → Γ ⊢ ∞ # A ≤ B
    → Γ ⊢ ∞ # `∀ A ≤ `∀ B

  ≤∀L : ∀ {Γ A C j} B
    → Γ ⊢ j # (⟦ B ⟧s A) ≤ C -- B is gussed
    → Γ ⊢ S j # `∀ A ≤ C


data _⊢_#_⦂_ : Context → Counter → Term → Type → Set where

  ⊢lit : ∀ {Γ n}
    → Γ ⊢ Z # (lit n) ⦂ Int

  ⊢var : ∀ {Γ x A}
    → (x∈Γ : get-var Γ x ≡ just A)
    → Γ ⊢ Z # ` x ⦂ A

  ⊢ann : ∀ {Γ e A}
    → Γ ⊢ ∞ # e ⦂ A
    → Γ ⊢ Z # (e ⦂ A) ⦂ A

  ⊢abs-∞ : ∀ {Γ e A B}
    → Γ , A ⊢ ∞ # e ⦂ B
    → Γ ⊢ ∞ # ƛ e ⦂ A `→ B

  ⊢abs-n : ∀ {Γ e A B j}
    → Γ , A ⊢ j # e ⦂ B
    → Γ ⊢ S j # ƛ e ⦂ A `→ B

  ⊢app₁ : ∀ {Γ e₁ e₂ A B}
    → Γ ⊢ Z # e₁ ⦂ A `→ B
    → Γ ⊢ ∞ # e₂ ⦂ A
    → Γ ⊢ Z # e₁ · e₂ ⦂ B

  ⊢app₂ : ∀ {Γ e₁ e₂ A B j}
    → Γ ⊢ (S j) # e₁ ⦂ A `→ B
    → Γ ⊢ Z # e₂ ⦂ A
    → Γ ⊢ j # e₁ · e₂ ⦂ B

  ⊢sub : ∀ {Γ e A A' j}
    → Γ ⊢ Z # e ⦂ A
    → (A≤A' : Γ ⊢ j # A ≤ A')
    → (j≢Z : j ≢ Z)
    → Γ ⊢ j # e ⦂ A'

  ⊢tabs : ∀ {Γ e A}
    → Γ ,∙ ⊢ Z # e ⦂ A
    → Γ ⊢ Z # Λ e ⦂ `∀ A

  ⊢tapp : ∀ {Γ e A B}
    → Γ ⊢ Z # e ⦂ `∀ B
    → Γ ⊢ Z # e ⟦ A ⟧ₐ ⦂ (⟦ A ⟧s B)


----------------------------------------------------------------------
--+                                                                +--
--+                      General Subsumption                       +--
--+                                                                +--
----------------------------------------------------------------------

⊢sub' : ∀ {Γ e A A' j}
  → Γ ⊢ Z # e ⦂ A
  → Γ ⊢ j # A ≤ A'
  → Γ ⊢ j # e ⦂ A'
⊢sub' {j = ∞} ⊢e A≤A' = ⊢sub ⊢e A≤A' λ ()
⊢sub' {j = Z} ⊢e ≤refl = ⊢e
⊢sub' {j = S j} ⊢e A≤A' = ⊢sub ⊢e A≤A' λ ()

≤refl-∞ : ∀ {Γ A}
  → Γ ⊢ ∞ # A ≤ A
≤refl-∞ {A = Int} = ≤int
≤refl-∞ {A = ‶ X} = ≤var
≤refl-∞ {A = A `→ B} = ≤arr-∞ ≤refl-∞ ≤refl-∞
≤refl-∞ {A = `∀ A} = ≤∀ ≤refl-∞

-- trans

----------------------------------------------------------------------
--+                                                                +--
--+                         Decl. Examples                         +--
--+                                                                +--
----------------------------------------------------------------------

id : Term
id = Λ (ƛ ` 0 ⦂ (‶ 0 `→ ‶ 0))

_ : ∅ ⊢ Z # id · (lit 1) ⦂ Int
_ = ⊢app₂ (⊢sub' (⊢tabs (⊢ann (⊢abs-∞ (⊢sub' (⊢var refl) ≤refl-∞))))
                 (≤∀L Int ≤refl)) ⊢lit


----------------------------------------------------------------------
--+                                                                +--
--+                             Algo.                              +--
--+                                                                +--
----------------------------------------------------------------------

infixr 8 ⟦_⟧⇒_

data Hint : Set where
  □ : Hint
  τ : Type → Hint
  ⟦_⟧⇒_ : Term → Hint → Hint

infixl 7 _⇧
_⇧ : Hint → Hint
τ A ⇧ = τ A
□ ⇧ = □
(⟦ e ⟧⇒ H) ⇧ = ⟦ shift 0 e ⟧⇒ (H ⇧)

infix 3 _⊢_⇒_⇒_
infix 3 _⊢_≤_⊣_↪_

data _⊢_≤_⊣_↪_ : Context → Type → Hint → Context → Type → Set where

  ≤-case1 : ∀ {Γ A}
    → Γ ⊢ A ≤ τ A ⊣ Γ ↪ A

data _⊢_⇒_⇒_ : Context → Hint → Term → Type → Set where

  ⊢lit : ∀ {Γ n}
    → Γ ⊢ □ ⇒ lit n ⇒ Int

  ⊢var : ∀ {Γ A x}
    → (x∈Γ : get-var Γ x ≡ just A)
    → Γ ⊢ □ ⇒ ` x ⇒ A

  ⊢ann : ∀ {Γ e A}
    → Γ ⊢ τ A ⇒ e ⇒ A
    → Γ ⊢ □ ⇒ e ⦂ A ⇒ A

  ⊢tabs : ∀ {Γ e A}
    → Γ ,∙ ⊢ □ ⇒ e ⇒ A
    → Γ ⊢ □ ⇒ Λ e ⇒ `∀ A
    
  ⊢app : ∀ {Γ e₁ e₂ H A B}
    → Γ ⊢ ⟦ e₂ ⟧⇒ H ⇒ e₁ ⇒ A `→ B
    → Γ ⊢ H ⇒ e₁ · e₂ ⇒ B

  ⊢lam₁ : ∀ {Γ e A B C}
    → Γ , A ⊢ τ B ⇒ e ⇒ C
    → Γ ⊢ τ (A `→ B) ⇒ ƛ e ⇒ A `→ C

  ⊢lam₂ : ∀ {Γ e₁ e A B H}
    → Γ ⊢ □ ⇒ e₁ ⇒ A
    → Γ , A ⊢ (H ⇧) ⇒ e ⇒ B
    → Γ ⊢ ⟦ e₁ ⟧⇒ H ⇒ ƛ e ⇒ A `→ B

  ⊢sub : ∀ {Γ e A A' H}
    → Γ ⊢ □ ⇒ e ⇒ A
    → (A≤H : Γ ⊢ A ≤ H ⊣ Γ ↪ A')
    → (H≢□ : H ≢ □)
    → Γ ⊢ H ⇒ e ⇒ A'

  ⊢tapp : ∀ {Γ e A B}
    → Γ ⊢ □ ⇒ e ⇒ `∀ B
    → Γ ⊢ □ ⇒ e ⟦ A ⟧ₐ ⇒ ⟦ A ⟧s B

----------------------------------------------------------------------
--+                                                                +--
--+                   Soundness                                    +--
--+                                                                +--
----------------------------------------------------------------------

_▻_ : Term → List Term → Term
e ▻ [] = e
e₁ ▻ (e₂ ∷ es) = (e₁ · e₂) ▻ es

infix 3 ⟦_,_⟧→⟦_,_,_,_⟧

data ⟦_,_⟧→⟦_,_,_,_⟧ : Hint → Type → List Term → Hint → List Type → Type → Set where

  none□ : ∀ {A}
    → ⟦ □ , A ⟧→⟦ [] , □ , [] , A ⟧

  noneτ : ∀ {A B}
    → ⟦ τ A , B ⟧→⟦ [] , τ A , [] , B ⟧

  have : ∀ {e H A B es A' B' Bs}
    → ⟦ H , B ⟧→⟦ es , A' , Bs , B' ⟧
    → ⟦ ⟦ e ⟧⇒ H , A `→ B ⟧→⟦ (e ∷ es) , A' , (A ∷ Bs) , B' ⟧

sound-inf : ∀ {Γ e H A es As A'}
  → Γ ⊢ H ⇒ e ⇒ A
  → ⟦ H , A ⟧→⟦ es , □ , As , A' ⟧
  → Γ ⊢ Z # e ▻ es ⦂ A'

sound-chk : ∀ {Γ e H A es T As A'}
  → Γ ⊢ H ⇒ e ⇒ A
  → ⟦ H , A ⟧→⟦ es , τ T , As , A' ⟧
  → Γ ⊢ ∞ # e ▻ es ⦂ T

sound-inf-0 : ∀ {Γ e A}
  → Γ ⊢ □ ⇒ e ⇒ A
  → Γ ⊢ Z # e ⦂ A
sound-inf-0 ⊢e = sound-inf ⊢e none□

sound-chk-0 : ∀ {Γ e A}
  → Γ ⊢ τ A ⇒ e ⇒ A
  → Γ ⊢ ∞ # e ⦂ A
sound-chk-0 ⊢e = sound-chk ⊢e noneτ

sound-inf ⊢lit none□ = ⊢lit
sound-inf (⊢var x∈Γ) spl = {!!}
sound-inf (⊢ann ⊢e) spl = {!!}
sound-inf (⊢tabs ⊢e) spl = {!!}
sound-inf (⊢app ⊢e) spl = {!!}
sound-inf (⊢lam₂ ⊢e ⊢e₁) spl = {!!}
sound-inf (⊢sub ⊢e A≤H H≢□) spl = {!sound-inf-0 ⊢e!}
sound-inf (⊢tapp ⊢e) spl = sound-inf {!!} {!x!}

sound-chk (⊢app ⊢e) spl = sound-chk ⊢e (have spl)
sound-chk (⊢lam₁ ⊢e) spl = {!!}
sound-chk (⊢lam₂ ⊢e ⊢e₁) spl = {!!}
sound-chk (⊢sub ⊢e x x') spl = {!!}


