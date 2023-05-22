module Completeness where

open import Prelude hiding (_≤?_; length) renaming (_≤_ to _≤n_)

open import Common
open import Dec
open import Algo
open import Algo.Properties

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

spl-weaken : ∀ {H A es T As A' n}
  → ❪ H , A ❫↣❪ es , T , As , A' ❫
  → ❪ H ⇧ n , A ❫↣❪ map (_↑ n) es , T , As , A' ❫
spl-weaken {T = T} none = none
spl-weaken (have spl) = have (spl-weaken spl)

ch-weaken : ∀ {es H' H n}
  → chain es H' H
  → chain (map (_↑ n) es) (H' ⇧ n) (H ⇧ n)
ch-weaken ch-none = ch-none
ch-weaken (ch-cons ch) = ch-cons (ch-weaken ch)
    
≤a-strengthen-τ : ∀ {Γ A B C}
  → Γ , A ⊢a B ≤ τ C
  → Γ ⊢a B ≤ τ C
≤a-strengthen-τ ≤a-int = ≤a-int
≤a-strengthen-τ ≤a-top = ≤a-top
≤a-strengthen-τ (≤a-arr C≤A B≤D) = ≤a-arr (≤a-strengthen-τ C≤A) (≤a-strengthen-τ B≤D)

----------------------------------------------------------------------
--+                                                                +--
--+                          Subsumption                           +--
--+                                                                +--
----------------------------------------------------------------------

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
⊢a-to-≤a (⊢a-lam₁ ⊢a) = ≤a-arr ≤a-refl-τ (≤a-strengthen-τ (⊢a-to-≤a ⊢a))
⊢a-to-≤a (⊢a-lam₂ ⊢a ⊢a₁) = ≤a-hint (rebase ⊢a ≤a-refl-τ) (≤a-strengthen-0 (⊢a-to-≤a ⊢a₁))
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
subsumption (⊢a-lam₂ ⊢e ⊢f) (have spl) (ch-cons ch) (≤a-hint x sub) = ⊢a-lam₂ ⊢e (subsumption ⊢f (spl-weaken spl) (ch-weaken ch) (≤a-weaken {n≤l = z≤n} sub))

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
rebase-gen (⊢a-lam₁ ⊢f) none ⊢e ch-none = ⊢a-lam₂ ⊢e ⊢f
rebase-gen (⊢a-lam₂ ⊢f ⊢a) (have spl) ⊢e (ch-cons ch) = ⊢a-lam₂ ⊢f (rebase-gen ⊢a (spl-weaken spl) (⊢a-weaken {n≤l = z≤n} ⊢e) (ch-weaken ch))

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
