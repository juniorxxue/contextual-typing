module Record.Annotatability.Target where

open import Record.Prelude
open import Record.PreCommon

infixr 5  ƛ_
infixl 7  _·_
infix  9  `_
infix  2 𝕣_
infixr 5 r⟦_↦_⟧_


data Term : Set
data Record : Set

data Term where
  𝕔_       : Constant → Term
  `_       : ℕ → Term
  ƛ_       : Term → Term
  _·_      : Term → Term → Term
--  _⦂_      : Term → Type → Term
  𝕣_       : Record → Term
  _𝕡_      : Term → Label → Term

data Record where
  rnil : Record
  r⟦_↦_⟧_ : Label → Term → Record → Record
