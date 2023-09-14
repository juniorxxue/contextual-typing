module STLC.Completeness where

open import STLC.Prelude hiding (_≤?_) renaming (_≤_ to _≤n_)
open import STLC.Common
open import STLC.Decl
open import STLC.Algo
open import STLC.Algo.Properties

----------------------------------------------------------------------
--+                                                                +--
--+                            Chaining                            +--
--+                                                                +--
----------------------------------------------------------------------

infix 4 _⇴_≗_

data _⇴_≗_ : List Type → Type → Type → Set where
  cht-none : ∀ {T}
    → [] ⇴ T ≗ T

  cht-cons : ∀ {A As T T'}
    → As ⇴ T ≗ T'
    → (A ∷ As) ⇴ T ≗ (A ⇒ T')
    
----------------------------------------------------------------------
--+                                                                +--
--+                          Subsumption                           +--
--+                                                                +--
----------------------------------------------------------------------


----------------------------------------------------------------------
--+                                                                +--
--+                          Completeness                          +--
--+                                                                +--
----------------------------------------------------------------------

infix 4 _↪_❪_,_,_❫

data _↪_❪_,_,_❫ : Type → Counter → Counter → List Type → Type → Set where

  j-none : ∀ {A}
    → A ↪ Z ❪ Z , [] , A ❫

  j-infi : ∀ {A}
    → A ↪ ∞ ❪ ∞ , [] , A ❫

  j-cons : ∀ {A B T j j' Bs}
    → B ↪ j ❪ j' , Bs , T ❫
    → (A ⇒ B) ↪ S j ❪ j' ,  A ∷ Bs , T ❫
  
complete-chk : ∀ {Γ e A}
  → Γ ⊢d ∞ # e ⦂ A
  → ∃[ B ] (Γ ⊢a τ A ⇛ e ⇛ B)

complete-inf : ∀ {Γ e A j As T J}
  → Γ ⊢d j # e ⦂ A
  → A ↪ j ❪ Z , As , T ❫
  → As ⇴ J ≗ J
  → Γ ⊢a τ J ⇛ e ⇛ T
