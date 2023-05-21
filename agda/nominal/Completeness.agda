{-# OPTIONS --allow-unsolved-metas #-}
module Completeness where

open import Data.Nat using (ℕ; zero; suc; _+_; _*_; _^_; _∸_; _≤?_; z≤n; s≤s) renaming (_≤_ to _≤n_)
open import Data.String using (String; _≟_)
open import Relation.Binary.PropositionalEquality
open import Data.Product using (_×_; proj₁; proj₂; ∃; ∃-syntax) renaming (_,_ to ⟨_,_⟩)
open import Data.Sum using (_⊎_; inj₁; inj₂) renaming ([_,_] to case-⊎)
open import Data.Empty using (⊥; ⊥-elim)
open import Relation.Nullary

open import Data.List using (List; []; _∷_; _++_; reverse; map; foldr; downFrom)

open import Common
open import Dec
open import Algo

----------------------------------------------------------------------
--+                                                                +--
--+                            Chaining                            +--
--+                                                                +--
----------------------------------------------------------------------

data chain : List Term → Hint → Hint → Set where
  ch-none : ∀ {H}
    → chain [] H H

  ch-cons : ∀ {H e es H'}
    → chain es H H'
    → chain (e ∷ es) H (⟦ e ⟧⇒ H')

infix 4 _⇴_≗_

data _⇴_≗_ : List Type → Type → Type → Set where
  cht-none : ∀ {T}
    → [] ⇴ T ≗ T

  cht-cons : ∀ {A As T T'}
    → As ⇴ T ≗ T'
    → (A ∷ As) ⇴ T ≗ (A ⇒ T')
    
----------------------------------------------------------------------
--+                                                                +--
--+                           Subtyping                            +--
--+                                                                +--
----------------------------------------------------------------------

≤d-to-≤a : ∀ {Γ A B}
  → B ≤d A
  → Γ ⊢a B ≤ τ A
≤d-to-≤a ≤d-int = ≤a-int
≤d-to-≤a ≤d-top = ≤a-top
≤d-to-≤a (≤d-arr ≤d ≤d₁) = ≤a-arr (≤d-to-≤a ≤d) (≤d-to-≤a ≤d₁)

----------------------------------------------------------------------
--+                                                                +--
--+                  Weakening and Strengthening                   +--
--+                                                                +--
----------------------------------------------------------------------

ext : ∀ {Γ Δ}
  → (∀ {x A} → Γ ∋ x ⦂ A → Δ ∋ x ⦂ A)
  → (∀ {x y A B} → Γ , y ⦂ B ∋ x ⦂ A → Δ , y ⦂ B ∋ x ⦂ A)
ext ρ Z           =  Z
ext ρ (S x≢y ∋x)  =  S x≢y (ρ ∋x)

≤a-rename : ∀ {Γ Δ}
  → (∀ {x A} → Γ ∋ x ⦂ A → Δ ∋ x ⦂ A)
  → (∀ {A H} → Γ ⊢a A ≤ H → Δ ⊢a A ≤ H)

⊢a-rename : ∀ {Γ Δ}
  → (∀ {x A} → Γ ∋ x ⦂ A → Δ ∋ x ⦂ A)
  → (∀ {e A H} → Γ ⊢a H ⇛ e ⇛ A → Δ ⊢a H ⇛ e ⇛ A)

≤a-rename ρ ≤a-int = ≤a-int
≤a-rename ρ ≤a-top = ≤a-top
≤a-rename ρ (≤a-arr C≤A B≤D) = ≤a-arr (≤a-rename ρ C≤A) (≤a-rename ρ B≤D)
≤a-rename ρ (≤a-hint ⊢e A≤H) = ≤a-hint (⊢a-rename ρ ⊢e) (≤a-rename ρ A≤H)

⊢a-rename ρ (⊢a-lit x) = ⊢a-lit (≤a-rename ρ x)
⊢a-rename ρ (⊢a-var x∈Γ A≤H) = ⊢a-var (ρ x∈Γ) (≤a-rename ρ A≤H)
⊢a-rename ρ (⊢a-app ⊢e) = ⊢a-app (⊢a-rename ρ ⊢e)
⊢a-rename ρ (⊢a-ann ⊢e A≤H) = ⊢a-ann (⊢a-rename ρ ⊢e) (≤a-rename ρ A≤H)
⊢a-rename ρ (⊢a-lam₁ ⊢e) = ⊢a-lam₁ (⊢a-rename (ext ρ) ⊢e)
⊢a-rename ρ (⊢a-lam₂ ⊢e ⊢e₁ x) = ⊢a-lam₂ (⊢a-rename ρ ⊢e) (⊢a-rename (ext ρ) ⊢e₁) x

test : ∀ {x y} → ¬ free (` x) y → x ≢ y
test nf eq rewrite eq = nf fr-var

test' : ∀ {x y e} → x ≢ y → ¬ free (ƛ y ⇒ e) x → ¬ free e x
test' neq nf = λ x₁ → nf (fr-lam x₁ neq)

infix 6 _>>_
_>>_ : Context → Context → Context
Γ₁ >> ∅ = Γ₁
Γ₁ >> (Γ₂ , x ⦂ A) = (Γ₁ >> Γ₂) , x ⦂ A

ρ-remove : ∀ {Γ₁ Γ₂ x A y B}
  → (Γ₁ , x ⦂ A) >> Γ₂ ∋ y ⦂ B
  → x ≢ y
  → Γ₁ >> Γ₂ ∋ y ⦂ B
ρ-remove {Γ₂ = ∅} Z neq = ⊥-elim (neq refl)
ρ-remove {Γ₂ = ∅} (S x y∈Γ) neq = y∈Γ
ρ-remove {Γ₂ = Γ₂ , z ⦂ C} Z neq = Z
ρ-remove {Γ₂ = Γ₂ , z ⦂ C} (S neq₁ y∈Γ) neq₂ = S neq₁ (ρ-remove y∈Γ neq₂)

ρ-drop-gen : ∀ {Γ₁ Γ₂ x A B z D}
  → (Γ₁ , x ⦂ A) >> Γ₂ ∋ z ⦂ D
  → Γ₂ ∋ x ⦂ B
  → (Γ₁ >> Γ₂) ∋ z ⦂ D
ρ-drop-gen {Γ₂ = Γ₂ , y ⦂ C} {x = x} {z = .y} Z x∈Γ = Z
ρ-drop-gen {Γ₂ = Γ₂ , y ⦂ C} {x = .y} {z = z} (S neq z∈Γ) Z = S neq (ρ-remove z∈Γ (≢-sym neq))
ρ-drop-gen {Γ₂ = Γ₂ , y ⦂ C} {x = x} {z = z} (S neq₁ z∈Γ) (S neq₂ x∈Γ) = S neq₁ (ρ-drop-gen z∈Γ x∈Γ)

ρ-drop : ∀ {Γ₁ Γ₂ x A B z D}
  → (Γ₁ , x ⦂ A) >> Γ₂ , x ⦂ B   ∋ z ⦂ D
  → Γ₁ >> Γ₂ , x ⦂ B             ∋ z ⦂ D
ρ-drop {Γ₂ = Γ₂} {x = x} {B = B} z∈Γ = ρ-drop-gen {Γ₂ = Γ₂ , x ⦂ B} z∈Γ Z

⊢a-drop : ∀ {Γ₁ Γ₂ x e H A B C}
  → (Γ₁ , x ⦂ A) >> Γ₂ , x ⦂ B ⊢a H ⇛ e ⇛ C
  → Γ₁ >> Γ₂ , x ⦂ B ⊢a H ⇛ e ⇛ C
⊢a-drop {Γ₁} {Γ₂} {x} {e} {H} {A} {B} {C} ⊢e = ⊢a-rename ρ ⊢e
  where
  ρ : ∀ {z D} 
    → (Γ₁ , x ⦂ A) >> Γ₂ , x ⦂ B ∋ z ⦂ D
    → Γ₁ >> Γ₂ , x ⦂ B ∋ z ⦂ D
  ρ = ρ-drop

ρ-add : ∀ {Γ₁ Γ₂ x A y B}
  → Γ₁ >> Γ₂ ∋ y ⦂ B
  → x ≢ y
  → (Γ₁ , x ⦂ A) >> Γ₂ ∋ y ⦂ B
ρ-add {Γ₂ = ∅} y∈Γ neq = S (≢-sym neq) y∈Γ
ρ-add {Γ₂ = Γ₂ , z ⦂ C} Z neq = Z
ρ-add {Γ₂ = Γ₂ , z ⦂ C} (S neq₁ y∈Γ) neq₂ = S neq₁ (ρ-add y∈Γ neq₂)

ρ-insert-gen : ∀ {Γ₁ Γ₂ x A B z D}
  → (Γ₁ >> Γ₂) ∋ z ⦂ D
  → Γ₂ ∋ x ⦂ B
  → (Γ₁ , x ⦂ A) >> Γ₂ ∋ z ⦂ D
ρ-insert-gen {Γ₂ = Γ₂ , x ⦂ C} Z x∈Γ = Z
ρ-insert-gen {Γ₂ = Γ₂ , x ⦂ C} (S neq z∈Γ) Z = S neq (ρ-add z∈Γ (≢-sym neq))
ρ-insert-gen {Γ₂ = Γ₂ , x ⦂ C} (S neq₁ z∈Γ) (S neq₂ x∈Γ) = S neq₁ (ρ-insert-gen z∈Γ x∈Γ)

ρ-insert : ∀ {Γ₁ Γ₂ x A B z D}
  → Γ₁ >> Γ₂ , x ⦂ B             ∋ z ⦂ D
  → (Γ₁ , x ⦂ A) >> Γ₂ , x ⦂ B   ∋ z ⦂ D
ρ-insert {Γ₂ = Γ₂} {x = x} {B = B} z∈Γ = ρ-insert-gen {Γ₂ = Γ₂ , x ⦂ B} z∈Γ Z

⊢a-insert : ∀ {Γ₁ Γ₂ x e H A B C}
  → Γ₁ >> Γ₂ , x ⦂ B ⊢a H ⇛ e ⇛ C
  → (Γ₁ , x ⦂ A) >> Γ₂ , x ⦂ B ⊢a H ⇛ e ⇛ C
⊢a-insert {Γ₁} {Γ₂} {x} {e} {H} {A} {B} {C} ⊢e = ⊢a-rename ρ ⊢e
  where
  ρ : ∀ {z D} 
    → Γ₁ >> Γ₂ , x ⦂ B ∋ z ⦂ D
    → (Γ₁ , x ⦂ A) >> Γ₂ , x ⦂ B ∋ z ⦂ D
  ρ = ρ-insert

≤a-weaken : ∀ {Γ₁ Γ₂ H x A B}
  → Γ₁ >> Γ₂ ⊢a B ≤ H
  → ¬ freeH H x
  → (Γ₁ , x ⦂ A) >> Γ₂ ⊢a B ≤ H
  
⊢a-weaken : ∀ {Γ₁ Γ₂ H e x A B}
  → Γ₁ >> Γ₂ ⊢a H ⇛ e ⇛ B
  → ¬ freeH H x
  → ¬ free e x
  → (Γ₁ , x ⦂ A) >> Γ₂ ⊢a H ⇛ e ⇛ B

≤a-weaken ≤a-int nf = ≤a-int
≤a-weaken ≤a-top nf = ≤a-top
≤a-weaken (≤a-arr B≤H B≤H₁) nf = ≤a-arr (≤a-weaken B≤H (λ ())) (≤a-weaken B≤H₁ (λ ()))
≤a-weaken (≤a-hint x B≤H) nf = ≤a-hint (⊢a-weaken x (λ ()) (¬freeH-inv₁ nf)) (≤a-weaken B≤H (¬freeH-inv₂ nf))
  where
  ¬freeH-inv₁ : ∀ {e H x}
    → ¬ freeH (⟦ e ⟧⇒ H) x
    → ¬ free e x
  ¬freeH-inv₁ neh = λ x₃ → neh (fr-e x₃)
  ¬freeH-inv₂ : ∀ {e H x}
    → ¬ freeH (⟦ e ⟧⇒ H) x
    → ¬ freeH H x
  ¬freeH-inv₂ neh = λ x₃ → neh (fr-H x₃)   

⊢a-weaken (⊢a-lit x) nh ne = ⊢a-lit (≤a-weaken x nh)
⊢a-weaken (⊢a-var x x₁) nh ne = ⊢a-var (ρ-add x (≢-sym (test ne))) (≤a-weaken x₁ nh)
⊢a-weaken (⊢a-app ⊢e) nh ne = ⊢a-app (⊢a-weaken ⊢e (¬freeH (¬free-app-inv₂ ne) nh) (¬free-app-inv₁ ne))
  where
  ¬free-app-inv₁ : ∀ {e₁ e₂ x}
    → ¬ free (e₁ · e₂) x
    → ¬ free e₁ x
  ¬free-app-inv₁ neq fre₁ = neq (fr-app-l fre₁)
  ¬free-app-inv₂ : ∀ {e₁ e₂ x}
    → ¬ free (e₁ · e₂) x
    → ¬ free e₂ x
  ¬free-app-inv₂ neq fre₂ = neq (fr-app-r fre₂)
  ¬freeH : ∀ {e H x}
    → ¬ free e x
    → ¬ freeH H x
    → ¬ freeH (⟦ e ⟧⇒ H) x
  ¬freeH nex nHx (fr-e fex) = ⊥-elim (nex fex)
  ¬freeH nex nHx (fr-H fHx) = ⊥-elim (nHx fHx)
  
⊢a-weaken (⊢a-ann ⊢e B≤H) nh ne = ⊢a-ann (⊢a-weaken ⊢e (λ ()) (¬free-ann-inv ne)) (≤a-weaken B≤H nh)
  where
  ¬free-ann-inv : ∀ {e A x}
    → ¬ free (e ⦂ A) x
    → ¬ free e x
  ¬free-ann-inv nfe fe = ⊥-elim (nfe (free-ann fe))
  
⊢a-weaken {Γ₁ = Γ₁} {Γ₂ = Γ₂} {x = x} (⊢a-lam₁ {x = y} {A = B} ⊢e) nh ne with x ≟ y
... | yes p rewrite p = ⊢a-lam₁ (⊢a-insert ⊢e)
... | no ¬p = ⊢a-lam₁ (⊢a-weaken {Γ₁ = Γ₁} {Γ₂ = Γ₂ , y ⦂ B} ⊢e (λ ()) (test' ¬p ne))

⊢a-weaken {Γ₁ = Γ₁} {Γ₂ = Γ₂} {x = x} (⊢a-lam₂ {x = y} {A = B} ⊢e ⊢f nf) nh ne with x ≟ y
... | yes p rewrite p = ⊢a-lam₂ (⊢a-weaken ⊢e (λ ()) (¬freeH-inv₁ nh)) (⊢a-insert ⊢f) nf
  where
  ¬freeH-inv₁ : ∀ {e H x}
    → ¬ freeH (⟦ e ⟧⇒ H) x
    → ¬ free e x
  ¬freeH-inv₁ neh = λ x₃ → neh (fr-e x₃)
... | no ¬p = ⊢a-lam₂ (⊢a-weaken ⊢e (λ ()) (¬freeH-inv₁ nh)) (⊢a-weaken {Γ₂ = Γ₂ , y ⦂ B} ⊢f (¬freeH-inv₂ nh) (test' ¬p ne)) nf
  where
  ¬freeH-inv₁ : ∀ {e H x}
    → ¬ freeH (⟦ e ⟧⇒ H) x
    → ¬ free e x
  ¬freeH-inv₁ neh = λ x₃ → neh (fr-e x₃)
  ¬freeH-inv₂ : ∀ {e H x}
    → ¬ freeH (⟦ e ⟧⇒ H) x
    → ¬ freeH H x
  ¬freeH-inv₂ neh = λ x₃ → neh (fr-H x₃)   

≤a-strengthen : ∀ {Γ₁ Γ₂ H x A B}
  → (Γ₁ , x ⦂ A) >> Γ₂ ⊢a B ≤ H
  → ¬ freeH H x
  → Γ₁ >> Γ₂ ⊢a B ≤ H
  
⊢a-strengthen : ∀ {Γ₁ Γ₂ H e x A B}
  → (Γ₁ , x ⦂ A) >> Γ₂ ⊢a H ⇛ e ⇛ B
  → ¬ freeH H x
  → ¬ free e x
  → Γ₁ >> Γ₂ ⊢a H ⇛ e ⇛ B
  
≤a-strengthen ≤a-int nh = ≤a-int
≤a-strengthen ≤a-top nh = ≤a-top
≤a-strengthen (≤a-arr B≤H B≤H₁) nh = ≤a-arr (≤a-strengthen B≤H (λ ())) (≤a-strengthen B≤H₁ (λ ()))
≤a-strengthen (≤a-hint ⊢e B≤H) nh = ≤a-hint (⊢a-strengthen ⊢e (λ ()) (¬freeH-inv₁ nh)) (≤a-strengthen B≤H (¬freeH-inv₂ nh))
  where
  ¬freeH-inv₁ : ∀ {e H x}
    → ¬ freeH (⟦ e ⟧⇒ H) x
    → ¬ free e x
  ¬freeH-inv₁ neh = λ x₃ → neh (fr-e x₃)
  ¬freeH-inv₂ : ∀ {e H x}
    → ¬ freeH (⟦ e ⟧⇒ H) x
    → ¬ freeH H x
  ¬freeH-inv₂ neh = λ x₃ → neh (fr-H x₃)    

⊢a-strengthen (⊢a-lit A≤H) nh ne = ⊢a-lit (≤a-strengthen A≤H nh)
⊢a-strengthen (⊢a-var x∈Γ B≤H) nh ne = ⊢a-var (∋-drop x∈Γ (≢-sym (test ne))) (≤a-strengthen B≤H nh)
  where
  ∋-drop : ∀ {Γ₁ Γ₂ x y A B}
    → (Γ₁ , x ⦂ A) >> Γ₂ ∋ y ⦂ B
    → x ≢ y
    → Γ₁ >> Γ₂ ∋ y ⦂ B
  ∋-drop = ρ-remove
  
⊢a-strengthen (⊢a-app ⊢e) nh ne = ⊢a-app (⊢a-strengthen ⊢e (¬freeH (¬free-app-inv₂ ne) nh) (¬free-app-inv₁ ne))
  where
  ¬free-app-inv₁ : ∀ {e₁ e₂ x}
    → ¬ free (e₁ · e₂) x
    → ¬ free e₁ x
  ¬free-app-inv₁ neq fre₁ = neq (fr-app-l fre₁)
  ¬free-app-inv₂ : ∀ {e₁ e₂ x}
    → ¬ free (e₁ · e₂) x
    → ¬ free e₂ x
  ¬free-app-inv₂ neq fre₂ = neq (fr-app-r fre₂)
  ¬freeH : ∀ {e H x}
    → ¬ free e x
    → ¬ freeH H x
    → ¬ freeH (⟦ e ⟧⇒ H) x
  ¬freeH nex nHx (fr-e fex) = ⊥-elim (nex fex)
  ¬freeH nex nHx (fr-H fHx) = ⊥-elim (nHx fHx)
 
    
⊢a-strengthen (⊢a-ann ⊢e B≤H) nh ne = ⊢a-ann (⊢a-strengthen ⊢e (λ ()) (¬free-ann-inv ne)) (≤a-strengthen B≤H nh)
  where
  ¬free-ann-inv : ∀ {e A x}
    → ¬ free (e ⦂ A) x
    → ¬ free e x
  ¬free-ann-inv nfe fe = ⊥-elim (nfe (free-ann fe))
  
⊢a-strengthen {Γ₁} {Γ₂} {x = x} (⊢a-lam₁ {x = y} {A = B} ⊢e) nh ne with x ≟ y
... | yes x≡y rewrite x≡y = ⊢a-lam₁ (⊢a-drop ⊢e)
... | no  x≢y = ⊢a-lam₁ (⊢a-strengthen {Γ₁ = Γ₁} {Γ₂ = Γ₂ , y ⦂ B} ⊢e (λ ()) (test' x≢y ne))

⊢a-strengthen {Γ₁} {Γ₂} {x = x} (⊢a-lam₂ {x = y} {A = B} ⊢e ⊢e₁ nnh) nh ne with x ≟ y
... | yes p rewrite p = ⊢a-lam₂ (⊢a-strengthen ⊢e (λ ()) (¬freeH-inv₁ nh)) (⊢a-drop ⊢e₁) nnh
  where
  ¬freeH-inv₁ : ∀ {e H x}
    → ¬ freeH (⟦ e ⟧⇒ H) x
    → ¬ free e x
  ¬freeH-inv₁ neh = λ x₃ → neh (fr-e x₃)
... | no ¬p = ⊢a-lam₂ (⊢a-strengthen ⊢e (λ ()) (¬freeH-inv₁ nh)) (⊢a-strengthen {Γ₁ = Γ₁} {Γ₂ = Γ₂ , y ⦂ B} ⊢e₁ (¬freeH-inv₂ nh) (test' ¬p ne )) nnh
  where
  ¬freeH-inv₁ : ∀ {e H x}
    → ¬ freeH (⟦ e ⟧⇒ H) x
    → ¬ free e x
  ¬freeH-inv₁ neh = λ x₃ → neh (fr-e x₃)
  ¬freeH-inv₂ : ∀ {e H x}
    → ¬ freeH (⟦ e ⟧⇒ H) x
    → ¬ freeH H x
  ¬freeH-inv₂ neh = λ x₃ → neh (fr-H x₃)


--- corollaries
≤a-weaken-1 : ∀ {Γ H x A B}
  → Γ ⊢a B ≤ H
  → ¬ freeH H x
  → Γ , x ⦂ A ⊢a B ≤ H
≤a-weaken-1 = ≤a-weaken {Γ₂ = ∅}  
  
⊢a-weaken-1 : ∀ {Γ H e x A B}
  → Γ ⊢a H ⇛ e ⇛ B
  → ¬ freeH H x
  → ¬ free e x
  → Γ ,  x ⦂ A ⊢a H ⇛ e ⇛ B
⊢a-weaken-1 = ⊢a-weaken {Γ₂ = ∅}

≤a-strengthen-1 : ∀ {Γ H x A B}
  → Γ , x ⦂ A ⊢a B ≤ H
  → ¬ freeH H x
  → Γ ⊢a B ≤ H
≤a-strengthen-1 = ≤a-strengthen {Γ₂ = ∅}  
  
⊢a-strengthen-1 : ∀ {Γ H e x A B}
  → Γ , x ⦂ A ⊢a H ⇛ e ⇛ B
  → ¬ freeH H x
  → ¬ free e x
  → Γ ⊢a H ⇛ e ⇛ B
⊢a-strengthen-1 = ⊢a-strengthen {Γ₂ = ∅}  

----------------------------------------------------------------------
--+                                                                +--
--+                          Subsumption                           +--
--+                                                                +--
----------------------------------------------------------------------

¬freeH-chain : ∀ {H H' H'' x es A As A'}
  → ¬ freeH H x
  → ❪ H , A ❫↣❪ es , Top , As , A' ❫
  → chain es H'' H'
  → ¬ freeH H' x
¬freeH-chain nfH none ch-none = {!!}
¬freeH-chain nfH (have spl) ch fH' = ⊥-elim (nfH {!!})


⊢a-to-≤a : ∀ {Γ e H A}
  → Γ ⊢a H ⇛ e ⇛ A
  → Γ ⊢a A ≤ H

subsumption : ∀ {Γ H e A H' H'' es As A'}
  → Γ ⊢a H ⇛ e ⇛ A
  → ❪ H , A ❫↣❪ es , Top , As , A' ❫
  → chain es H'' H'
  → Γ ⊢a A ≤ H'
  → Γ ⊢a H' ⇛ e ⇛ A

⊢a-to-≤a (⊢a-lit x) = x
⊢a-to-≤a (⊢a-var x x₁) = x₁
⊢a-to-≤a (⊢a-app ⊢a) with ⊢a-to-≤a ⊢a
... | ≤a-hint x A≤H = A≤H
⊢a-to-≤a (⊢a-ann ⊢a x) = x
⊢a-to-≤a (⊢a-lam₁ ⊢a) = ≤a-arr ≤a-refl-h (≤a-strengthen-1 (⊢a-to-≤a ⊢a) (λ ()))
⊢a-to-≤a (⊢a-lam₂ ⊢a ⊢a₁ nf) = ≤a-hint (rebase ⊢a ≤a-refl-h) (≤a-strengthen-1 (⊢a-to-≤a ⊢a₁) nf)
  where
    rebase : ∀ {Γ e A B}
      → Γ ⊢a τ Top ⇛ e ⇛ B
      → Γ ⊢a B ≤ τ A
      → Γ ⊢a τ A ⇛ e ⇛ B
    rebase ⊢f B≤A = subsumption ⊢f none ch-none B≤A

subsumption (⊢a-lit x) spl ch sub = ⊢a-lit sub
subsumption (⊢a-var x x₁) spl ch sub = ⊢a-var x sub
subsumption (⊢a-app ⊢e) spl ch sub with ⊢a-to-≤a ⊢e
... | ≤a-hint ⊢e₂ res = ⊢a-app (subsumption ⊢e (have spl) (ch-cons ch) (≤a-hint ⊢e₂ sub))

subsumption (⊢a-ann ⊢e x) spl ch sub = ⊢a-ann ⊢e sub
subsumption (⊢a-lam₂ ⊢e ⊢f nf) (have spl) (ch-cons ch) (≤a-hint x sub) = ⊢a-lam₂ ⊢e (subsumption ⊢f spl ch {!!}) {!!}

rebase-≤ : ∀ {Γ A A' As H H' e es T₁ T₂}
  → Γ ⊢a A ≤ H
  → ❪ H , A ❫↣❪ es , T₁ ⇒ T₂ , As , A' ❫
  → chain es (⟦ e ⟧⇒ τ T₂) H'
  → Γ ⊢a τ Top ⇛ e ⇛ T₁
  → Γ ⊢a A ≤ H'
rebase-≤ (≤a-arr A≤H A≤H₁) none ch-none ⊢e = ≤a-hint (rebase ⊢e A≤H) A≤H₁
    where
       rebase : ∀ {Γ e A B}
         → Γ ⊢a τ Top ⇛ e ⇛ B
         → Γ ⊢a B ≤ τ A
         → Γ ⊢a τ A ⇛ e ⇛ B
       rebase ⊢f B≤A = subsumption ⊢f none ch-none B≤A
      
rebase-≤ (≤a-hint x A≤H) (have spl) (ch-cons ch) ⊢e = ≤a-hint x (rebase-≤ A≤H spl ch ⊢e)

rebase-gen : ∀ {Γ e₁ e₂ H A es T₁ T₂ As A' H'}
  → Γ ⊢a H ⇛ e₁ ⇛ A
  → ❪ H , A ❫↣❪ es , T₁ ⇒ T₂ , As , A' ❫
  → Γ ⊢a τ Top ⇛ e₂ ⇛ T₁
  → chain es (⟦ e₂ ⟧⇒ (τ T₂)) H'
  → Γ ⊢a H' ⇛ e₁ ⇛ A
rebase-gen (⊢a-lit ()) none ⊢e ch-none
rebase-gen (⊢a-var x∈Γ A≤H) spl ⊢e ch = ⊢a-var x∈Γ (rebase-≤ A≤H spl ch ⊢e)
rebase-gen (⊢a-app ⊢f) spl ⊢e ch = ⊢a-app (rebase-gen ⊢f (have spl) ⊢e (ch-cons ch))
rebase-gen (⊢a-ann ⊢f A≤H) spl ⊢e ch = ⊢a-ann ⊢f (rebase-≤ A≤H spl ch ⊢e)
rebase-gen (⊢a-lam₁ ⊢f) none ⊢e ch-none = ⊢a-lam₂ ⊢e ⊢f (λ ())
rebase-gen (⊢a-lam₂ ⊢f ⊢a nf) (have spl) ⊢e (ch-cons ch) = ⊢a-lam₂ ⊢f (rebase-gen ⊢a spl (⊢a-weaken-1 ⊢e (λ ()) {!!}) ch) {!!}

rebase-gen-1 : ∀ {Γ e₁ e₂ A B C D}
  → Γ ⊢a τ (A ⇒ B) ⇛ e₁ ⇛ C ⇒ D
  → Γ ⊢a τ Top ⇛ e₂ ⇛ A
  → Γ ⊢a ⟦ e₂ ⟧⇒ τ B ⇛ e₁ ⇛ C ⇒ D
rebase-gen-1 ⊢f ⊢e = rebase-gen ⊢f none ⊢e ch-none

----------------------------------------------------------------------
--+                                                                +--
--+                          Completeness                          +--
--+                                                                +--
----------------------------------------------------------------------

infix 4 _↪_❪_,_❫

data _↪_❪_,_❫ : Type → ℕ → List Type → Type → Set where

  n-none : ∀ {A}
    → A ↪ 0 ❪ [] , A ❫

  n-cons : ∀ {A B T n Bs}
    → B ↪ n ❪ Bs , T ❫
    → (A ⇒ B) ↪ (suc n) ❪ A ∷ Bs , T ❫


  
complete-chk : ∀ {Γ e A}
  → Γ ⊢d ∞ ╏ e ⦂ A
  → ∃[ B ] (Γ ⊢a τ A ⇛ e ⇛ B)

complete-inf : ∀ {Γ e A n As T J}
  → Γ ⊢d c n ╏ e ⦂ A
  → A ↪ n ❪ As , T ❫
  → As ⇴ Top ≗ J
  → Γ ⊢a τ J ⇛ e ⇛ A

complete-chk (⊢d-lam₁ {A = A} ⊢d) with complete-chk ⊢d
... | ⟨ C , ⊢e ⟩ = ⟨ A ⇒ C , ⊢a-lam₁ ⊢e ⟩

complete-chk (⊢d-app₃ ⊢f ⊢e) with complete-chk ⊢f
... | ⟨ Int , ind-f ⟩ = ⊥-elim (inv-absurd ind-f)
  where
    inv-absurd : ∀ {Γ e A B}
      → Γ ⊢a τ (A ⇒ B) ⇛ e ⇛ Int → ⊥
    inv-absurd ⊢e with ⊢a-to-≤a ⊢e
    ... | ()

... | ⟨ Top , ind-f ⟩ = ⊥-elim (inv-absurd ind-f)
  where
    inv-absurd : ∀ {Γ e A B}
      → Γ ⊢a τ (A ⇒ B) ⇛ e ⇛ Top → ⊥
    inv-absurd ⊢e with ⊢a-to-≤a ⊢e
    ... | ()
    
... | ⟨ C ⇒ D , ind-f ⟩ = ⟨ D , ⊢a-app (rebase ind-f ind-e) ⟩
  where
    ind-e = complete-inf ⊢e n-none cht-none
    rebase : ∀ {Γ e₁ e₂ A B C D}
      → Γ ⊢a τ (A ⇒ B) ⇛ e₁ ⇛ C ⇒ D
      → Γ ⊢a τ Top ⇛ e₂ ⇛ A
      → Γ ⊢a ⟦ e₂ ⟧⇒ τ B ⇛ e₁ ⇛ C ⇒ D
    rebase ⊢f ⊢e = rebase-gen-1 ⊢f ⊢e

complete-chk (⊢d-sub {B = B} ⊢e B≤A) = ⟨ B , rebase ind-e (≤d-to-≤a B≤A) ⟩
  where
    ind-e = complete-inf ⊢e n-none cht-none
    rebase : ∀ {Γ e A B}
      → Γ ⊢a τ Top ⇛ e ⇛ B
      → Γ ⊢a B ≤ τ A
      → Γ ⊢a τ A ⇛ e ⇛ B
    rebase ⊢e B≤A = subsumption ⊢e none ch-none B≤A

complete-inf ⊢d-int n-none cht-none = ⊢a-lit ≤a-top
complete-inf (⊢d-var x∈Γ) spl JA = ⊢a-var x∈Γ (≤d-to-≤a (≤d-n-spl spl JA))
  where
    ≤d-n-spl : ∀ {A As J T n}
      → A ↪ n ❪ As , T ❫
      → As ⇴ Top ≗ J
      → A ≤d J
    ≤d-n-spl n-none cht-none = ≤d-top
    ≤d-n-spl (n-cons nspl) (cht-cons newJ) = ≤d-arr ≤d-refl (≤d-n-spl nspl newJ)
      
 
complete-inf (⊢d-lam₂ ⊢e) (n-cons spl) (cht-cons AJ) = ⊢a-lam₁ (complete-inf ⊢e spl AJ)

complete-inf (⊢d-app₁ ⊢f ⊢e) n-none cht-none = ⊢a-app (rebase ind-f (proj₂ (complete-chk ⊢e)))
  where
    ind-f = complete-inf ⊢f n-none cht-none
    rebase : ∀ {Γ e₁ e₂ A B C}
      → Γ ⊢a τ Top ⇛ e₁ ⇛ A ⇒ B
      → Γ ⊢a τ A ⇛ e₂ ⇛ C
      → Γ ⊢a ⟦ e₂ ⟧⇒ τ Top ⇛ e₁ ⇛ A ⇒ B
    rebase ⊢f ⊢e = subsumption ⊢f none ch-none (≤a-hint ⊢e ≤a-top)

complete-inf (⊢d-app₂ ⊢f ⊢e) spl JA = ⊢a-app (rebase ind-f (complete-inf ⊢e n-none cht-none))
  where
    ind-f = complete-inf ⊢f (n-cons spl) (cht-cons JA)
    rebase : ∀ {Γ e₁ e₂ A B J}
      → Γ ⊢a τ (A ⇒ J) ⇛ e₁ ⇛ A ⇒ B
      → Γ ⊢a τ Top ⇛ e₂ ⇛ A
      → Γ ⊢a ⟦ e₂ ⟧⇒ τ J ⇛ e₁ ⇛ A ⇒ B
    rebase ⊢f ⊢e = rebase-gen-1 ⊢f ⊢e

complete-inf (⊢d-ann ⊢e) spl JA = ⊢a-ann (proj₂ (complete-chk ⊢e)) (≤d-to-≤a (≤d-n-spl spl JA))
  where
    ≤d-n-spl : ∀ {A As J T n}
      → A ↪ n ❪ As , T ❫
      → As ⇴ Top ≗ J
      → A ≤d J
    ≤d-n-spl n-none cht-none = ≤d-top
    ≤d-n-spl (n-cons nspl) (cht-cons newJ) = ≤d-arr ≤d-refl (≤d-n-spl nspl newJ)
