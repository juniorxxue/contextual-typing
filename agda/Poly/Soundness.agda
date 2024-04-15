module Poly.Soundness where

open import Poly.Common
open import Poly.Decl
open import Poly.Algo

----------------------------------------------------------------------
--+                              Roll                              +--
----------------------------------------------------------------------

data Apps : ℕ → ℕ → Set where
  [] : Apps n m
  _∷a_ : Term n m → Apps n m → Apps n m
  _∷t_ : Type m → Apps n m → Apps n m

data AppsType : ℕ → Set where
  [] : AppsType m
  _∷a_ : Type m → AppsType m → AppsType m
  _∷t_ : Type m → AppsType m → AppsType m

_▻_ : Term n m → Apps n m → Term n m
e ▻ [] = e
e ▻ (e' ∷a es) = (e · e') ▻ es
e ▻ (A  ∷t es) = (e [ A ]) ▻ es

infix 4 ⟦_,_⟧→⟦_,_,_,_⟧

data ⟦_,_⟧→⟦_,_,_,_⟧ : Context n m → Type m → Apps n m → Context n m → AppsType m → Type m → Set where

  none-□ : ∀ {A}
    → ⟦ (Context n m ∋⦂ □) , A ⟧→⟦ [] , □ , [] , A ⟧

  none-τ : ∀ {A B}
    → ⟦ (Context n m ∋⦂ τ A) , B ⟧→⟦ [] , τ A , [] , B ⟧

  have-a : ∀ {Σ : Context n m} {e A B es A' B' Bs}
    → ⟦ Σ , B ⟧→⟦ es , A' , Bs , B' ⟧
    → ⟦ ([ e ]↝ Σ) , A `→ B ⟧→⟦ e ∷a es , A' , A ∷a Bs , B' ⟧

  have-t : ∀ {Σ : Context n m} {B A es A' B' Bs}
    → ⟦ Σ , B ⟧→⟦ es , A' , Bs , B' ⟧
    → ⟦ ⟦ A ⟧↝ Σ , B ⟧→⟦ A ∷t es , A' , Bs , B' ⟧

----------------------------------------------------------------------
--+                             Subst                              +--
----------------------------------------------------------------------

size-apps : Apps n m → ℕ
size-apps [] = 0
size-apps (_ ∷a as) = 1 + size-apps as
size-apps (_ ∷t as) = 1 + size-apps as

size-counter : Counter → ℕ
size-counter Z = 0
size-counter ∞ = 1
size-counter (S j) = 1 + size-counter j
size-counter (Sτ j) = 1 + size-counter j




----------------------------------------------------------------------
--+                             Typing                             +--
----------------------------------------------------------------------

sound-i : ∀ {Γ : Env n m} {Σ e e̅ A A' A̅}
  → Γ ⊢ Σ ⇒ e ⇒ A
  → ⟦ Σ , A ⟧→⟦ e̅ , □ , A̅ , A' ⟧
  → Γ ⊢ Z # e ▻ e̅ ⦂ A'

sound-c : ∀ {Γ : Env n m} {Σ e e̅ A A' A̅ T}
  → Γ ⊢ Σ ⇒ e ⇒ A
  → ⟦ Σ , A ⟧→⟦ e̅ , τ T , A̅ , A' ⟧
  → Γ ⊢ ∞ # e ▻ e̅ ⦂ T

sound-i-0 : ∀ {Γ : Env n m} {e A}
  → Γ ⊢ □ ⇒ e ⇒ A
  → Γ ⊢ Z # e ⦂ A
sound-i-0 ⊢e = sound-i ⊢e none-□

sound-c-0 : ∀ {Γ : Env n m} {e A B}
  → Γ ⊢ τ B ⇒ e ⇒ A
  → Γ ⊢ ∞ # e ⦂ B
sound-c-0 ⊢e = sound-c ⊢e none-τ

sound-i ⊢lit none-□ = ⊢lit
sound-i (⊢var x∈Γ) none-□ = ⊢var x∈Γ
sound-i (⊢ann ⊢e) none-□ = ⊢ann (sound-c-0 ⊢e)
sound-i (⊢app ⊢e) spl = sound-i ⊢e (have-a spl)
sound-i (⊢lam₂ ⊢e ⊢e₁) (have-a spl) = {!!}
sound-i (⊢sub ⊢e x) spl = {!!}
sound-i (⊢tabs₁ ⊢e) none-□ = ⊢tabs₁ (sound-i-0 ⊢e)
sound-i (⊢tapp ⊢e) spl = sound-i ⊢e (have-t spl)

sound-c (⊢app ⊢e) spl = sound-c ⊢e (have-a spl)
sound-c (⊢lam₁ ⊢e) none-τ = ⊢lam₁ (sound-c-0 ⊢e)
sound-c (⊢lam₂ ⊢e ⊢e₁) (have-a spl) = {!!}
sound-c (⊢sub ⊢e x) spl = {!!}
sound-c (⊢tapp ⊢e) spl = sound-c ⊢e (have-t spl)
