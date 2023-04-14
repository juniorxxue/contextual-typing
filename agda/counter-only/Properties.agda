module Properties where

open import Data.Nat using (ℕ; zero; suc; _+_; _*_; _^_; _∸_)
open import Data.String using (String)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl)
open import Data.Product using (_×_; proj₁; proj₂; ∃; ∃-syntax) renaming (_,_ to ⟨_,_⟩)
open import Data.Sum using (_⊎_; inj₁; inj₂) renaming ([_,_] to case-⊎)
open import Data.Empty using (⊥; ⊥-elim)
open import Relation.Nullary using (¬_)

open import Data.List using (List; []; _∷_; _++_; length; reverse; map; foldr; downFrom)

open import Common
open import Dec
open import Algo

----------------------------------------------------------------------
--+                                                                +--
--+                           Soundness                            +--
--+                                                                +--
----------------------------------------------------------------------

infix 4 _⊩_⇚_
data _⊩_⇚_ : Context → List Term → List Type → Set where
  ⊩-empty : ∀ {Γ}
    → Γ ⊩ [] ⇚ []

  ⊩-cons : ∀ {Γ es As e A}
    → Γ ⊩ es ⇚ As
    → Γ ⊢d ∞ ╏ e ⦂ A
    → Γ ⊩ (e ∷ es) ⇚ (A ∷ As)

⊩-elim : ∀ {Γ e H A es T As A'}
  → Γ ⊢d c 0 ╏ e ⦂ A
  → Γ ⊩ es ⇚ As
  → ❪ H , A ❫↣❪ es , T , As , A' ❫ 
  → Γ ⊢d c 0 ╏ e ▻ es ⦂ A'
⊩-elim ⊢d ⊩-empty none = ⊢d
⊩-elim ⊢d (⊩-cons ⊩es ⊢e) (have spl) = ⊩-elim (⊢d-app₁ ⊢d ⊢e) ⊩es spl
  

sound-≤ : ∀ {Γ H A es T As A'}
  → Γ ⊢a A ≤ H
  → ❪ H , A ❫↣❪ es , T , As , A' ❫
  → (A' ≤d T) × (Γ ⊩ es ⇚ As)

sound : ∀ {Γ e H A es T As A'}
  → Γ ⊢a H ⇛ e ⇛ A
  → ❪ H , A ❫↣❪ es , T , As , A' ❫
  → (T ≡ Top → Γ ⊢d c 0 ╏ e ▻ es ⦂ A') × (Γ ⊢d ∞ ╏ e ▻ es ⦂ T)

sound-inf : ∀ {Γ e A}
  → Γ ⊢a τ Top ⇛ e ⇛ A
  → Γ ⊢d c 0 ╏ e ⦂ A
sound-inf ⊢a = proj₁ (sound ⊢a none) refl

sound-chk : ∀ {Γ e A B}
  → Γ ⊢a τ A ⇛ e ⇛ B
  → Γ ⊢d ∞ ╏ e ⦂ A
sound-chk ⊢a = proj₂ (sound ⊢a none)

----------------------------------------------------------------------
--+                                                                +--
--+                          Completeness                          +--
--+                                                                +--
----------------------------------------------------------------------

-- subtyping complete

≤d-to-≤a : ∀ {Γ A B}
  → B ≤d A
  → Γ ⊢a B ≤ τ A
≤d-to-≤a ≤d-int = ≤a-int
≤d-to-≤a ≤d-top = ≤a-top
≤d-to-≤a (≤d-arr ≤d ≤d₁) = ≤a-arr (≤d-to-≤a ≤d) (≤d-to-≤a ≤d₁)

-- weakening


⊢a-weaken : ∀ {Γ e A B C}
  → Γ , B ⊢a τ A ⇛ 1 ↑ e ⇛ C
  → Γ ⊢a τ A ⇛ e ⇛ C
⊢a-weaken ⊢a = {!!}

≤a-weaken : ∀ {Γ A B H}
  → Γ , A ⊢a B ≤ (1 ↥ H)
  → Γ ⊢a B ≤ H
≤a-weaken {H = τ Int} ≤ = {!!}
≤a-weaken {H = τ Top} ≤ = {!!}
≤a-weaken {H = τ (x ⇒ x₁)} ≤ = {!!}
≤a-weaken {H = ⟦ e ⟧⇒ H} (≤a-hint ⊢e ≤) = {!!}

-- subsumption

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

subsumption : ∀ {Γ H e A H' H'' es As A'}
  → Γ ⊢a H ⇛ e ⇛ A
  → (Γ ⊢a A ≤ H)
  × (❪ H , A ❫↣❪ es , Top , As , A' ❫ → chain es H'' H' → Γ ⊢a A ≤ H' → Γ ⊢a H' ⇛ e ⇛ A)
subsumption (⊢a-lit x) = ⟨ x , (λ x x₁ → ⊢a-lit) ⟩
subsumption (⊢a-var x x₁) = ⟨ x₁ , (λ _ _ → ⊢a-var x) ⟩

subsumption {H' = H'} {H''} {es} {As} {A'} (⊢a-app ⊢e) with (≤a-hint-inv₁ (proj₁ (subsumption {H' = H'} {H'' = H''} {es = es} {As = As} {A' = A'} ⊢e)))
... | ⟨ fst , snd ⟩ = ⟨ ≤a-hint-inv₂ (proj₁ (subsumption {H' = H'} {H'' = H''} {es = es} {As = As} {A' = A'} ⊢e))
                      , (λ spl ch A≤H' → ⊢a-app ((proj₂ (subsumption ⊢e)) (have spl) (ch-cons ch) (≤a-hint snd A≤H'))) ⟩


subsumption (⊢a-ann ⊢e x) = {!!}
subsumption (⊢a-lam₁ ⊢e) = {!!}
subsumption (⊢a-lam₂ ⊢e ⊢e₁) = ⟨ ≤a-hint ((proj₂ (subsumption ⊢e)) none ch-none ≤a-refl-h ) {!!} , (λ spl ch A≤H' → {!!}) ⟩

-- several corollaries
⊢a-to-≤a : ∀ {Γ e H A}
  → Γ ⊢a H ⇛ e ⇛ A
  → Γ ⊢a A ≤ H
⊢a-to-≤a ⊢e = proj₁ (subsumption {H' = τ Top} {H'' = τ Top} {es = []} {As = []} {A' = Top} ⊢e)

sub : ∀ {Γ H e A H' H'' es As A'}
  → Γ ⊢a H ⇛ e ⇛ A
  → ❪ H , A ❫↣❪ es , Top , As , A' ❫
  → chain es H'' H'
  → Γ ⊢a A ≤ H'
  → Γ ⊢a H' ⇛ e ⇛ A
sub = {!!}

sub-top : ∀ {Γ e A B}
  → Γ ⊢a τ Top ⇛ e ⇛ A
  → Γ ⊢a A ≤ τ B
  → Γ ⊢a τ B ⇛ e ⇛ A
sub-top ⊢e A≤B = sub ⊢e none ch-none A≤B  

-- completeness theorem

infix 4 _⊩a_⇛_⇛_

data _⊩a_⇛_⇛_ : Context → Hint → List Term → List Type → Set where
  ⊩a-none : ∀ {Γ}
    → Γ ⊩a τ Top ⇛ [] ⇛ []

  ⊩a-cons : ∀ {Γ e es A As}
    → Γ ⊩a τ Top ⇛ es ⇛ As
    → Γ ⊢a τ Top ⇛ e ⇛ A
    → Γ ⊩a τ Top ⇛ (e ∷ es) ⇛ (A ∷ As)

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

complete-chk (⊢d-app₃ ⊢f ⊢e) = {!!}

complete-chk (⊢d-sub {B = B} ⊢e B≤A) = ⟨ B , sub-top (complete-inf ⊢e n-none cht-none) {!!} ⟩

complete-inf ⊢d-int n-none cht-none = ⊢a-lit ≤a-top

complete-inf (⊢d-var x∋Γ) spl AJ = ⊢a-var x∋Γ {!!} -- easy

complete-inf (⊢d-lam₂ ⊢e) (n-cons spl) (cht-cons AJ) = ⊢a-lam₁ (complete-inf ⊢e spl AJ)

complete-inf (⊢d-app₁ ⊢f ⊢e) spl AJ = ⊢a-app (sub ⊢a-f none ch-none {!!}) -- easy
  where ⊢a-f = complete-inf ⊢f n-none cht-none

complete-inf (⊢d-app₂ ⊢f ⊢e) spl AJ = ⊢a-app {! !}
  where
    ⊢a-f = complete-inf ⊢f (n-cons spl) (cht-cons AJ)
    ⊢a-e = complete-inf ⊢e n-none cht-none
    args-app : ∀ {Γ A J B e e'}
      → Γ ⊢a τ (A ⇒ J) ⇛ e ⇛ B
      → Γ ⊢a τ Top ⇛ e' ⇛ A
      → Γ ⊢a ⟦ e' ⟧⇒ τ J ⇛ e ⇛ B
    args-app (⊢a-var x (≤a-arr x₁ x₂)) ⊢e' = ⊢a-var x (≤a-hint {!!} x₂) -- sub
    args-app (⊢a-app ⊢e) ⊢e' = {!!}
    args-app (⊢a-ann ⊢e x) ⊢e' = {!!}
    args-app (⊢a-lam₁ ⊢e) ⊢e' = {!!}

complete-inf (⊢d-ann ⊢e) spl AJ = ⊢a-ann (proj₂ (complete-chk ⊢e)) {!!} -- easy
