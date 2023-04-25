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

infix 4 _⊩_⇛_
data _⊩_⇛_ : Context → List Term → List Type → Set where
  ⊩-empty' : ∀ {Γ}
    → Γ ⊩ [] ⇛ []

  ⊩-cons' : ∀ {Γ es As e A}
    → Γ ⊩ es ⇛ As
    → Γ ⊢d c 0 ╏ e ⦂ A
    → Γ ⊩ (e ∷ es) ⇛ (A ∷ As)

⊩-elim' : ∀ {Γ e H A es T As A'}
  → Γ ⊢d ∞ ╏ e ⦂ A
  → Γ ⊩ es ⇛ As
  → ❪ H , A ❫↣❪ es , T , As , A' ❫ 
  → Γ ⊢d ∞ ╏ e ▻ es ⦂ T
⊩-elim' ⊢d ⊩-empty' none = {!!}
⊩-elim' ⊢d (⊩-cons' ⊩es ⊢e) (have spl) = ⊩-elim' (⊢d-app₃ ⊢d ⊢e) ⊩es spl 

sound-≤ : ∀ {Γ H A es T As A'}
  → Γ ⊢a A ≤ H
  → ❪ H , A ❫↣❪ es , T , As , A' ❫
  → (A' ≤d T) × (Γ ⊩ es ⇚ As)

sound-inf : ∀ {Γ e H A es As A'}
  → Γ ⊢a H ⇛ e ⇛ A
  → ❪ H , A ❫↣❪ es , Top , As , A' ❫
  → Γ ⊢d c 0 ╏ e ▻ es ⦂ A'

sound-chk : ∀ {Γ e H A es T As A'}
  → Γ ⊢a H ⇛ e ⇛ A
  → ❪ H , A ❫↣❪ es , T , As , A' ❫
  → Γ ⊢d ∞ ╏ e ▻ es ⦂ T

-- looks like we haven't used new 2 apps rules in soundness proof so far (1 essential case left)

sound-≤ ≤a-int none = ⟨ ≤d-int , ⊩-empty ⟩
sound-≤ ≤a-top none = ⟨ ≤d-top , ⊩-empty ⟩
sound-≤ (≤a-arr C≤A B≤D) none = ⟨ (≤d-arr ΓC≤A ΓB≤D) , ⊩-empty ⟩
  where ΓB≤D = proj₁ (sound-≤ B≤D none)
        ΓC≤A = proj₁ (sound-≤ C≤A none)
sound-≤ (≤a-hint ⊢e A≤H) (have spl) = ⟨ (proj₁ (sound-≤ A≤H spl)) , ⊩-cons (proj₂ (sound-≤ A≤H spl)) (sound-chk ⊢e none) ⟩

sound-inf (⊢a-lit _) none = ⊢d-int
sound-inf (⊢a-var ∋ A≤H) spl = ⊩-elim (⊢d-var ∋) arg-chks spl
  where arg-chks = proj₂ (sound-≤ A≤H spl)
sound-inf (⊢a-app ⊢e) spl = sound-inf ⊢e (have spl)
sound-inf (⊢a-ann ⊢e A≤H) spl = ⊩-elim (⊢d-ann (sound-chk ⊢e none)) arg-chks spl
  where arg-chks = proj₂ (sound-≤ A≤H spl)
sound-inf (⊢a-lam₂ ⊢e ⊢f) (have none) = ⊢d-app₂ (⊢d-lam₂ (sound-inf ⊢f none)) (sound-inf ⊢e none)
sound-inf (⊢a-lam₂ ⊢e ⊢f) (have (have spl)) = {!sound-inf ⊢f ?!}

sound-chk (⊢a-lit ≤a-int) none = ⊢d-sub ⊢d-int ≤d-refl
sound-chk (⊢a-lit ≤a-top) none = ⊢d-sub ⊢d-int ≤d-top
sound-chk (⊢a-var ∋ A≤H) spl = ⊢d-sub elims A'≤T
  where arg-chks = proj₂ (sound-≤ A≤H spl)
        elims = ⊩-elim (⊢d-var ∋) arg-chks spl
        A'≤T = proj₁ (sound-≤ A≤H spl)
sound-chk (⊢a-app ⊢e) spl = sound-chk ⊢e (have spl)
sound-chk (⊢a-ann ⊢e A≤H) spl = ⊢d-sub elims A'≤T
  where arg-chks = proj₂ (sound-≤ A≤H spl)
        elims = ⊩-elim (⊢d-ann (sound-chk ⊢e none)) arg-chks spl
        A'≤T = proj₁ (sound-≤ A≤H spl)        
sound-chk (⊢a-lam₁ ⊢e) none = ⊢d-lam₁ (sound-chk ⊢e none)
sound-chk (⊢a-lam₂ ⊢e ⊢f) (have spl) = {!!}

{-

sound-inf : ∀ {Γ e A}
  → Γ ⊢a τ Top ⇛ e ⇛ A
  → Γ ⊢d c 0 ╏ e ⦂ A
sound-inf ⊢a = proj₁ (sound ⊢a none) refl

sound-chk : ∀ {Γ e A B}
  → Γ ⊢a τ A ⇛ e ⇛ B
  → Γ ⊢d ∞ ╏ e ⦂ A
sound-chk ⊢a = proj₂ (sound ⊢a none)

-}

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

⊢a-strengthen : ∀ {Γ e H A B}
  → Γ , A ⊢a 1 ↥ H ⇛ 1 ↑ e ⇛ B
  → Γ ⊢a H ⇛ e ⇛ B
⊢a-strengthen {e = lit x} ⊢e = {!!}
⊢a-strengthen {e = ` x} ⊢e = {!!}
⊢a-strengthen {e = ƛ e} ⊢e = {!!}
⊢a-strengthen {e = e · e₁} (⊢a-app ⊢e) = ⊢a-app (⊢a-strengthen ⊢e)
⊢a-strengthen {e = e ⦂ x} ⊢e = {!!}

≤a-strengthen : ∀ {Γ A B H}
  → Γ , A ⊢a B ≤ (1 ↥ H)
  → Γ ⊢a B ≤ H
≤a-strengthen {H = τ Int} ≤ = {!!}
≤a-strengthen {H = τ Top} ≤ = {!!}
≤a-strengthen {H = τ (x ⇒ x₁)} ≤ = {!!}
≤a-strengthen {H = ⟦ e ⟧⇒ H} (≤a-hint ⊢e ≤) = {!!}

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
⊢a-to-≤a (⊢a-lam₁ ⊢a) = ≤a-arr ≤a-refl-h {!⊢a-to-≤a ⊢a!} -- trivial
⊢a-to-≤a (⊢a-lam₂ ⊢a ⊢a₁) = ≤a-hint (subsumption ⊢a none ch-none ≤a-refl-h) {!⊢a-to-≤a ⊢a₁!} -- depends on above shift-reasoning lemma

subsumption (⊢a-lit x) spl ch sub = ⊢a-lit sub
subsumption (⊢a-var x x₁) spl ch sub = ⊢a-var x sub
subsumption (⊢a-app ⊢e) spl ch sub with ⊢a-to-≤a ⊢e
... | ≤a-hint ⊢e₂ res = ⊢a-app (subsumption ⊢e (have spl) (ch-cons ch) (≤a-hint ⊢e₂ sub))

subsumption (⊢a-ann ⊢e x) spl ch sub = ⊢a-ann ⊢e sub
subsumption (⊢a-lam₂ ⊢e ⊢f) (have spl) (ch-cons ch) sub = ⊢a-lam₂ ⊢e (subsumption ⊢f {!!} {!!} {!!})

-- several corollaries

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

complete-chk (⊢d-app₃ ⊢f ⊢e) with complete-chk ⊢f
... | ⟨ C ⇒ D , ind-f ⟩ = ⟨ {!!} , (⊢a-app (subsumption ind-f {!!} {!!} {!!})) ⟩
-- needs a sumsumption not limited to Top

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
