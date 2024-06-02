module Trad where

open import Data.Nat using (ℕ; zero; suc; _+_; _*_; _^_; _∸_)
open import Data.String using (String)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl)
open import Data.Product using (_×_; proj₁; proj₂; ∃; ∃-syntax) renaming (_,_ to ⟨_,_⟩)

open import Common
open import Dec

infix 4 _⊢d_∙_∙_

data _⊢d_∙_∙_ : Context → Term → Mode → Type → Set where
  ⊢dd-int : ∀ {Γ n}
    → Γ ⊢d (lit n) ∙ ⇛ ∙ Int

  ⊢dd-var : ∀ {Γ x A}
    → Γ ∋ x ⦂ A
    → Γ ⊢d ` x ∙ ⇛ ∙ A

  ⊢dd-lam : ∀ {Γ x e A B}
    → Γ , x ⦂ A ⊢d e ∙ ⇚ ∙ B
    → Γ ⊢d (ƛ x ⇒ e) ∙ ⇚ ∙ A ⇒ B

  ⊢dd-app₁ : ∀ {Γ e₁ e₂ A B}
    → Γ ⊢d e₁ ∙ ⇛ ∙ A ⇒ B
    → Γ ⊢d e₂ ∙ ⇚ ∙ A
    → Γ ⊢d e₁ · e₂ ∙ ⇛ ∙ B

  ⊢dd-app₂ : ∀ {Γ e₁ e₂ A B}
    → Γ ⊢d e₁ ∙ ⇚ ∙ A ⇒ B
    → Γ ⊢d e₂ ∙ ⇛ ∙ A
    → Γ ⊢d e₁ · e₂ ∙ ⇛ ∙ B

  ⊢dd-ann : ∀ {Γ e A}
    → Γ ⊢d e ∙ ⇚ ∙ A
    → Γ ⊢d e ⦂ A ∙ ⇛ ∙ A

  ⊢dd-sub : ∀ {Γ e A B}
    → Γ ⊢d e ∙ ⇛ ∙ B
    → B ≤d A
    → Γ ⊢d e ∙ ⇚ ∙ A

----------------------------------------------------------------------
--+                                                                +--
--+                           Soundness                            +--
--+                                                                +--
----------------------------------------------------------------------

-- we know that declarative with counters should be weaker than
--   traditional bidirectional type system with a special app rule
--   since counter will exclude some cases

sound : ∀ {Γ cc e ⇔ A}
  → Γ ⊢d cc ╏ e ∙ ⇔ ∙ A
  → Γ ⊢d e ∙ ⇔ ∙ A
sound ⊢d-int = ⊢dd-int
sound (⊢d-var x) = ⊢dd-var x
sound (⊢d-lam₁ ⊢d) = ⊢dd-lam (sound ⊢d)
sound (⊢d-lam₂ ⊢d) = ⊢dd-lam (sound ⊢d)
sound (⊢d-app₁ ⊢d ⊢d₁) = ⊢dd-app₁ (sound ⊢d) (sound ⊢d₁)
sound (⊢d-app₂ ⊢d ⊢d₁) = ⊢dd-app₂ (sound ⊢d) (sound ⊢d₁)
sound (⊢d-ann ⊢d) = ⊢dd-ann (sound ⊢d)
sound (⊢d-sub ⊢d x) = ⊢dd-sub (sound ⊢d) x -- fully generated

----------------------------------------------------------------------
--+                                                                +--
--+                          Completeness                          +--
--+                                                                +--
----------------------------------------------------------------------

{-

feel like this statement is not meaningful

complete : ∀ {Γ e ⇔ A}
  → Γ ⊢d e ∙ ⇔ ∙ A
  → ∃[ cc ] Γ ⊢d cc ╏ e ∙ ⇔ ∙ A
complete ⊢dd-int = ⟨ c 0 , ⊢d-int ⟩
complete (⊢dd-var x) = ⟨ c 0 , ⊢d-var x ⟩
complete (⊢dd-lam ⊢d) with complete ⊢d
... | ⟨ ∘ , ⊢e ⟩ = ⟨ ∘ , ⊢d-lam₁ ⊢e ⟩
... | ⟨ c n , ⊢e ⟩ = ⟨ c (suc n) , ⊢d-lam₂ ⊢e ⟩
complete (⊢dd-app₁ ⊢d ⊢d₁) = ⟨ (c 0) , ⊢d-app₁ {!!} {!!} ⟩
complete (⊢dd-app₂ ⊢d ⊢d₁) = {!!}
complete (⊢dd-ann ⊢d) = {!!}
complete (⊢dd-sub ⊢d x) = {!!}

-}
