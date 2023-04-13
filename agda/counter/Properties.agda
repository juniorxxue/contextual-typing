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
    → Γ ⊢d ∞ ╏ e ∙ ⇚ ∙ A
    → Γ ⊩ (e ∷ es) ⇚ (A ∷ As)

⊩-elim : ∀ {Γ e H A es T As A'}
  → Γ ⊢d c 0 ╏ e ∙ ⇛ ∙ A
  → Γ ⊩ es ⇚ As
  → ❪ H , A ❫↣❪ es , T , As , A' ❫ 
  → Γ ⊢d c 0 ╏ e ▻ es ∙ ⇛ ∙ A'
⊩-elim ⊢d ⊩-empty none = ⊢d
⊩-elim ⊢d (⊩-cons ⊩es ⊢e) (have spl) = ⊩-elim (⊢d-app₁ ⊢d ⊢e) ⊩es spl
  

sound-≤ : ∀ {Γ H A es T As A'}
  → Γ ⊢a A ≤ H
  → ❪ H , A ❫↣❪ es , T , As , A' ❫
  → (A' ≤d T) × (Γ ⊩ es ⇚ As)

sound : ∀ {Γ e H A es T As A'}
  → Γ ⊢a H ⇛ e ⇛ A
  → ❪ H , A ❫↣❪ es , T , As , A' ❫
  → (T ≡ Top → Γ ⊢d c 0 ╏ e ▻ es ∙ ⇛ ∙ A') × (Γ ⊢d ∞ ╏ e ▻ es ∙ ⇚ ∙ T)

sound-≤ ≤a-int none = ⟨ ≤d-int , ⊩-empty ⟩
sound-≤ ≤a-top none = ⟨ ≤d-top , ⊩-empty ⟩
sound-≤ (≤a-arr ≤a ≤a₁) none = ⟨ ≤d-arr (proj₁ (sound-≤ ≤a none)) (proj₁ (sound-≤ ≤a₁ none)) , ⊩-empty ⟩
sound-≤ (≤a-hint ⊢e ≤a) (have spl) = ⟨ proj₁ (sound-≤ ≤a spl) , ⊩-cons (proj₂ (sound-≤ ≤a spl)) (proj₂ (sound ⊢e none)) ⟩

sound (⊢a-lit ≤a-int) none = ⟨ (λ T≡Top → ⊢d-int) , ⊢d-sub ⊢d-int ≤d-int ⟩
sound (⊢a-lit ≤a-top) none = ⟨ (λ T≡Top → ⊢d-int) , ⊢d-sub ⊢d-int ≤d-top ⟩

sound (⊢a-var Γ∋x A≤H) spl = ⟨ (λ T≡Top → ⊩-elim (⊢d-var Γ∋x) (proj₂ (sound-≤ A≤H spl)) spl)
                             , ⊢d-sub (⊩-elim (⊢d-var Γ∋x) (proj₂ (sound-≤ A≤H spl)) spl) (proj₁ (sound-≤ A≤H spl)) ⟩                             
                             
sound (⊢a-app ⊢a ) spl = sound ⊢a (have spl)

sound (⊢a-ann ⊢a A≤H) spl = ⟨ (λ T≡Top → ⊩-elim (⊢d-ann ( proj₂ (sound ⊢a none))) ( proj₂ (sound-≤ A≤H spl)) spl)
                            , ⊢d-sub (⊩-elim (⊢d-ann ( proj₂ (sound ⊢a none))) ( proj₂ (sound-≤ A≤H spl)) spl) ((proj₁ (sound-≤ A≤H spl))) ⟩
                            
sound (⊢a-lam₁ ⊢e) none = ⟨ (λ ()) , ⊢d-lam₁ (proj₂ (sound ⊢e none)) ⟩

sound (⊢a-lam₂ ⊢e ⊢e₁) (have spl) = ⟨ (λ T≡Top → {!!}) , {!!} ⟩

sound-inf : ∀ {Γ e A}
  → Γ ⊢a τ Top ⇛ e ⇛ A
  → Γ ⊢d c 0 ╏ e ∙ ⇛ ∙ A
sound-inf ⊢a = proj₁ (sound ⊢a none) refl

sound-chk : ∀ {Γ e A B}
  → Γ ⊢a τ A ⇛ e ⇛ B
  → Γ ⊢d ∞ ╏ e ∙ ⇚ ∙ A
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

infix 4 _↪_❪_,_❫

data _↪_❪_,_❫ : Type → ℕ → List Type → Type → Set where

  n-none : ∀ {A}
    → A ↪ 0 ❪ [] , A ❫

  n-cons : ∀ {A B T n Bs}
    → B ↪ n ❪ Bs , T ❫
    → (A ⇒ B) ↪ (suc n) ❪ A ∷ Bs , T ❫

  
complete : ∀ {Γ e ⇔ A cc}
  → Γ ⊢d cc ╏ e ∙ ⇔ ∙ A
  → ((⇔ ≡ ⇚) → (cc ≡ ∞) → ∃[ B ] (Γ ⊢a τ A ⇛ e ⇛ B))
--  × ((⇔ ≡ ⇚) → (cc ≡ c n) → (A ↪ n ❪ As , T ❫) → ∃[ B ] (Γ ⊢a τ Top ⇛ e ⇛ B))
  × ((⇔ ≡ ⇛) → Γ ⊢a τ Top ⇛ e ⇛ A)

complete ⊢d-int = ⟨ (λ ()) , (λ _ → ⊢a-lit ≤a-top) ⟩
complete (⊢d-var ∋) = ⟨ (λ ()) , (λ _ → ⊢a-var ∋ ≤a-top) ⟩

complete (⊢d-lam₁ {A = A} {B = B} ⊢e) with (proj₁ (complete ⊢e)) refl refl
... | ⟨ C , ⊢e' ⟩ = ⟨ (λ _ _ → ⟨ A ⇒ C , ⊢a-lam₁ ⊢e' ⟩) , (λ ()) ⟩

complete (⊢d-lam₂ {A = A} {B = B} ⊢e) = ⟨ (λ _ ()) , (λ ()) ⟩

-- the lam1 and lam2 share the same proof,
-- I'm concerned with that why it doesn't include reasoning of counters
-- perhaps it should happen in the soundness proof

complete (⊢d-app₁ ⊢f ⊢e) with proj₁ (complete ⊢e) refl refl
... | ⟨ C , ⊢a-e ⟩ = ⟨ (λ ()) , (λ _ → complete-app ind-f ⊢a-e) ⟩
  where
    complete-app : ∀ {Γ e₁ e₂ A B C}
      → Γ ⊢a τ Top ⇛ e₁ ⇛ A ⇒ B
      → Γ ⊢a τ A ⇛ e₂ ⇛ C
      → Γ ⊢a τ Top ⇛ e₁ · e₂ ⇛ B
    complete-app ⊢f ⊢e = ⊢a-app (sub ⊢f none ch-none {!!}) --trivial
    ind-f = proj₂ (complete ⊢f) refl

complete (⊢d-app₂ ⊢f ⊢e) = ⟨ (λ ()) , (λ _ → {!!}) ⟩

complete (⊢d-ann ⊢d) with (proj₁ (complete ⊢d)) refl refl
... | ⟨ B , ⊢a-e ⟩ = ⟨ (λ ()) , (λ _ → ⊢a-ann ⊢a-e ≤a-top) ⟩

complete (⊢d-sub {B = B} ⊢d x) with (proj₂ (complete ⊢d)) refl
... | ⊢e = ⟨ (λ _ _ → ⟨ B , sub-top ⊢e {!!} ⟩) , (λ ()) ⟩ -- trivial
