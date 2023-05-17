module Completeness where

open import Prelude hiding (_≤?_; length) renaming (_≤_ to _≤n_)

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
--+                             Shift                              +--
--+                                                                +--
----------------------------------------------------------------------

length : Context → ℕ
length ∅        =  zero
length (Γ , _)  =  suc (length Γ)

↑Γ : (Γ : Context) → (n : ℕ) → (n ≤n length Γ) → Type → Context
↑Γ Γ zero n≤l T = Γ , T
↑Γ ∅ (suc n) () T
↑Γ (Γ , A) (suc n) (s≤s n≤l) T = (↑Γ Γ n n≤l T) , A

↓Γ : (Γ : Context) → (n : ℕ) → (n ≤n length Γ) → Context
↓Γ ∅ .zero z≤n = ∅
↓Γ (Γ , A) zero n≤l = Γ
↓Γ (Γ , A) (suc n) (s≤s n≤l) = (↓Γ Γ n n≤l) , A

↑Γ-var₁ : ∀ {Γ n A B x n≤l}
  → Γ ∋ x ⦂ B
  → n ≤n x
  → ↑Γ Γ n n≤l A ∋ suc x ⦂ B
↑Γ-var₁ {n = zero} x∈Γ n≤x = S x∈Γ
↑Γ-var₁ {n = suc n} {n≤l = s≤s n≤l} (S x∈Γ) (s≤s n≤x) = S (↑Γ-var₁ x∈Γ n≤x)

↑Γ-var₂ : ∀ {Γ n A B x n≤l}
  → Γ ∋ x ⦂ B
  → ¬ n ≤n x
  → ↑Γ Γ n n≤l A ∋ x ⦂ B
↑Γ-var₂ {n = zero} {x = zero} x∈Γ n>x = ⊥-elim (n>x z≤n)
↑Γ-var₂ {n = zero} {x = suc x} x∈Γ n>x = ⊥-elim (n>x z≤n)
↑Γ-var₂ {n = suc n} {x = zero} {s≤s n≤l} Z n>x = Z
↑Γ-var₂ {Γ , C} {n = suc n} {x = suc x} {s≤s n≤l} (S x∈Γ) n>x = S (↑Γ-var₂ x∈Γ λ n≤x → n>x (s≤s n≤x))

∋-weaken : ∀ {Γ A n x B}
  → Γ ∋ x ⦂ B
  → (n≤l : n ≤n length Γ)
  → ↑Γ Γ n n≤l A ∋ ↑-var n x ⦂ B
∋-weaken {Γ = Γ} {n = n} {x = x} x∈Γ n≤l with n ≤? x
... | yes p = ↑Γ-var₁ x∈Γ p
... | no ¬p = ↑Γ-var₂ x∈Γ ¬p

⇧-⇧-comm : ∀ H m n → m ≤n n → H ⇧ m ⇧ suc n ≡ H ⇧ n ⇧ m
⇧-⇧-comm (τ A) m n m≤n = refl
⇧-⇧-comm (⟦ e ⟧⇒ H) m n m≤n rewrite ↑-↑-comm e m n m≤n | ⇧-⇧-comm H m n m≤n = refl

postulate

{-
⊢a-strengthen : ∀ {Γ e A B n}
  → Γ , A ⊢a H ⇛ e ⇛ B
  → ¬ (e ≡ var n)
  → Γ ⊢a H ⇩ n ⇛ e ↓ n ⇛ B
-}
  ⊢a-strengthen : ∀ {Γ e H A B}
    → Γ , A ⊢a H ⇧ 0 ⇛ e ↑ 0 ⇛ B
    → Γ ⊢a H ⇛ e ⇛ B
    
  ≤a-strengthen : ∀ {Γ A B H}
    → Γ , A ⊢a B ≤ (H ⇧ 0)
    → Γ ⊢a B ≤ H

  ≤a-weaken : ∀ {Γ A B H}
    → Γ ⊢a B ≤ H
    → Γ , A ⊢a B ≤ (H ⇧ 0)

  ⊢a-weaken : ∀ {Γ e H A B}
    → Γ ⊢a H ⇛ e ⇛ B
    → Γ , A ⊢a H ⇧ 0 ⇛ e ↑ 0 ⇛ B

≤a-strengthen-gen : ∀ {Γ A B H n n≤l}
  → ↑Γ Γ n n≤l A ⊢a B ≤ (H ⇧ n)
  → Γ ⊢a B ≤ H
≤a-strengthen-gen B≤H = {!!}

≤a-strengthen-gen' : ∀ {Γ A H n n≤l}
  → Γ ⊢a A ≤ H
  → ↓Γ Γ n n≤l ⊢a A ≤ (H ⇩ n)
  
⊢a-strengthen-gen' : ∀ {Γ A H n n≤l e}
  → Γ ⊢a H ⇛ e ⇛ A
  → ↓Γ Γ n n≤l ⊢a (H ⇩ n) ⇛ e ↓ n ⇛ A

≤a-strengthen-gen' ≤a-int = ≤a-int
≤a-strengthen-gen' ≤a-top = ≤a-top
≤a-strengthen-gen' (≤a-arr A≤H A≤H₁) = ≤a-arr (≤a-strengthen-gen' A≤H) (≤a-strengthen-gen' A≤H₁)
≤a-strengthen-gen' (≤a-hint ⊢e A≤H) = ≤a-hint (⊢a-strengthen-gen' ⊢e) (≤a-strengthen-gen' A≤H)

⊢a-strengthen-gen' (⊢a-lit x) = ⊢a-lit (≤a-strengthen-gen' x)
⊢a-strengthen-gen' (⊢a-var x∈Γ A≤H) = ⊢a-var {!!} (≤a-strengthen-gen' A≤H)
⊢a-strengthen-gen' (⊢a-app ⊢e) = {!!}
⊢a-strengthen-gen' (⊢a-ann ⊢e x) = {!!}
⊢a-strengthen-gen' (⊢a-lam₁ ⊢e) = ⊢a-lam₁ (⊢a-strengthen-gen' ⊢e)
⊢a-strengthen-gen' (⊢a-lam₂ ⊢e ⊢e₁) = ⊢a-lam₂ (⊢a-strengthen-gen' ⊢e) {!⊢a-strengthen-gen' ⊢e₁!}

↓Γ-var₁ : ∀ {Γ n x A n≤l}
  → Γ ∋ x ⦂ A
  → suc n ≤n x
  → ↓Γ Γ n n≤l ∋ pred x ⦂ A
↓Γ-var₁ {Γ , B} {zero} (S x∈Γ) (s≤s n+1≤x) = {!!}
↓Γ-var₁ {Γ , B} {suc n} {n≤l = s≤s n≤l} (S x∈Γ) (s≤s n+1≤x) = {!↓Γ-var₁ x∈Γ n+1≤x!}


∋-strenghthen : ∀ {Γ n x A}
  → Γ ∋ x ⦂ A
  → (n≤l : n ≤n length Γ)
  → ↓Γ Γ n n≤l ∋ ↓-var n x ⦂ A
∋-strenghthen {Γ , B} {n} {x} {A} x∈Γ n≤l with suc n ≤? x
... | yes p = {!!}
... | no ¬p = {!!}

≤a-weaken-gen : ∀ {Γ A B H n n≤l}
  → Γ ⊢a B ≤ H
  → ↑Γ Γ n n≤l A ⊢a B ≤ (H ⇧ n)
  
⊢a-weaken-gen : ∀ {Γ e H A B n n≤l}
  → Γ ⊢a H ⇛ e ⇛ B
  → ↑Γ Γ n n≤l A ⊢a H ⇧ n ⇛ e ↑ n ⇛ B

≤a-weaken-gen ≤a-int = ≤a-int
≤a-weaken-gen ≤a-top = ≤a-top
≤a-weaken-gen (≤a-arr B≤H B≤H₁) = ≤a-arr (≤a-weaken-gen B≤H) (≤a-weaken-gen B≤H₁)
≤a-weaken-gen (≤a-hint ⊢e B≤H) = ≤a-hint (⊢a-weaken-gen ⊢e) (≤a-weaken-gen B≤H)

eq-sample : ∀ H n
  → H ⇧ n ⇧ 0 ≡ H ⇧ 0 ⇧ (suc n)
eq-sample H n rewrite ⇧-⇧-comm H 0 n z≤n = refl

⊢a-weaken-gen (⊢a-lit B≤H) = ⊢a-lit (≤a-weaken-gen B≤H)
⊢a-weaken-gen {n = n} {n≤l} (⊢a-var {x = x} x∈Γ B≤H) = ⊢a-var (∋-weaken x∈Γ n≤l) (≤a-weaken-gen B≤H)
⊢a-weaken-gen (⊢a-app ⊢e) = ⊢a-app (⊢a-weaken-gen ⊢e)
⊢a-weaken-gen (⊢a-ann ⊢e B≤H) = ⊢a-ann (⊢a-weaken-gen ⊢e) (≤a-weaken-gen B≤H)
⊢a-weaken-gen {n≤l = n≤l} (⊢a-lam₁ ⊢e) = ⊢a-lam₁ (⊢a-weaken-gen {n≤l = s≤s n≤l} ⊢e)
⊢a-weaken-gen {H = ⟦ _ ⟧⇒ H} {A = A} {n = n} {n≤l = n≤l} (⊢a-lam₂ ⊢e ⊢f) with ⊢a-weaken-gen {A = A} {n = suc n} {n≤l = s≤s n≤l} ⊢f
... | ind-f rewrite sym (eq-sample H n) = ⊢a-lam₂ (⊢a-weaken-gen ⊢e) ind-f

{-

-- we need to gen the weakening, possibly to alter context into a list

≤a-weaken ≤a-int = ≤a-int
≤a-weaken ≤a-top = ≤a-top
≤a-weaken (≤a-arr {A = A} C≤A B≤D) = ≤a-arr (≤a-weaken C≤A) (≤a-weaken B≤D)
≤a-weaken (≤a-hint {A = A} ⊢e B≤H) = ≤a-hint (⊢a-weaken ⊢e) (≤a-weaken B≤H)

⊢a-weaken (⊢a-lit ≤a-int) = ⊢a-lit ≤a-int
⊢a-weaken (⊢a-lit ≤a-top) = ⊢a-lit ≤a-top
⊢a-weaken (⊢a-var {x = x} x∈Γ B≤H) = ⊢a-var (S x∈Γ) (≤a-weaken B≤H)
⊢a-weaken (⊢a-app ⊢e) = ⊢a-app (⊢a-weaken ⊢e)
⊢a-weaken (⊢a-ann ⊢e B≤H) = ⊢a-ann (⊢a-weaken ⊢e) (≤a-weaken B≤H)
⊢a-weaken (⊢a-lam₁ ⊢e) = ⊢a-lam₁ {!⊢a-weaken ⊢e!}
⊢a-weaken (⊢a-lam₂ ⊢e ⊢f) = ⊢a-lam₂ (⊢a-weaken ⊢e) {!⊢a-weaken ⊢f!}

-}

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
⊢a-to-≤a (⊢a-lam₂ ⊢a ⊢a₁) = ≤a-hint (rebase ⊢a ≤a-refl-τ) (≤a-strengthen (⊢a-to-≤a ⊢a₁))
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
subsumption (⊢a-lam₂ ⊢e ⊢f) (have spl) (ch-cons ch) (≤a-hint x sub) = ⊢a-lam₂ ⊢e (subsumption ⊢f (spl-weaken spl) (ch-weaken ch) (≤a-weaken sub))

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
rebase-gen (⊢a-lam₂ ⊢f ⊢a) (have spl) ⊢e (ch-cons ch) = ⊢a-lam₂ ⊢f (rebase-gen ⊢a (spl-weaken spl) (⊢a-weaken ⊢e) (ch-weaken ch))

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
