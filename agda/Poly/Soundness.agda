module Poly.Soundness where

open import Poly.Common
open import Poly.Decl
open import Poly.Decl.Subst
open import Poly.Decl.Properties
open import Poly.Algo

----------------------------------------------------------------------
--+                             Split                              +--
----------------------------------------------------------------------

infix 4 ⟦_,_⟧→⟦_,_,_,_⟧

data ⟦_,_⟧→⟦_,_,_,_⟧ : Context n m → Type m → Apps n m → Context n m → AppsType m → Type m → Set where

  none-□ : ∀ {A}
    → ⟦ (Context n m ∋⦂ □) , A ⟧→⟦ nil , □ , nil , A ⟧

  none-τ : ∀ {A B}
    → ⟦ (Context n m ∋⦂ τ A) , B ⟧→⟦ nil , τ A , nil , B ⟧

  have-a : ∀ {Σ : Context n m} {e A B es A' B' Bs}
    → ⟦ Σ , B ⟧→⟦ es , A' , Bs , B' ⟧
    → ⟦ ([ e ]↝ Σ) , A `→ B ⟧→⟦ e ∷a es , A' , A ∷a Bs , B' ⟧

  have-t : ∀ {Σ : Context n m} {B A es A' B' Bs}
    → ⟦ Σ , B ⟧→⟦ es , A' , Bs , B' ⟧
    → ⟦ ⟦ A ⟧↝ Σ , B ⟧→⟦ A ∷t es , A' , Bs , B' ⟧

spl-weaken : ∀ {Σ Σ' : Context n m} {A e̅ A̅ A' k}
  → ⟦ Σ , A ⟧→⟦ e̅ , Σ' , A̅ , A' ⟧
  → ⟦ ↑Σ k Σ , A ⟧→⟦ up k e̅ , ↑Σ k Σ' , A̅ , A' ⟧
spl-weaken = {!!}  
  
----------------------------------------------------------------------
--+                             Typing                             +--
----------------------------------------------------------------------

record Log : Set where
  field
    s-counter   : Counter
    check-terms : List (Term n m) -- along with a proof
    infer-terms : List (Term n m)

f' : ∀ {Ψ : SEnv n m} {Ψ' A Σ A'} → (Ψ ⊢ A ≤ Σ ⊣ Ψ' ↪ A') → Log
f' s-int = record { s-counter = ∞ ; check-terms = [] ; infer-terms = [] }
f' (s-empty p) = {!!}
f' s-var = {!!}
f' (s-ex-l^ x x₁ x₂) = {!!}
f' (s-ex-l= x x₁ s s₁) = {!!}
f' (s-ex-r^ x x₁ x₂) = {!!}
f' (s-ex-r= x x₁ s s₁) = {!!}
f' (s-arr s s₁) = {!!}
f' (s-term-c x x₁ s) = {!!}
f' (s-term-o x x₁ s s₁) = {!!}
f' (s-∀ s) = {!!}
f' (s-∀l-^ s) = {!!}
f' (s-∀l-eq s) = {!!}
f' (s-∀-t s) = {!!}

f : ∀ {Ψ : SEnv n m} {Ψ' A Σ A'} → (Ψ ⊢ A ≤ Σ ⊣ Ψ' ↪ A') → Counter
f s-int = ∞
f (s-empty p) = Z
f s-var = ∞
f (s-ex-l^ x x₁ x₂) = ∞
f (s-ex-l= x x₁ s s₁) = ∞
f (s-ex-r^ x x₁ x₂) = ∞
f (s-ex-r= x x₁ s s₁) = ∞
f (s-arr s s₁) = ∞
f (s-term-c x x₁ s) = f s
f (s-term-o x x₁ s s₁) = S (f s₁)
f (s-∀ s) = ∞
f (s-∀l-^ s) = f s
f (s-∀l-eq s) = f s
f (s-∀-t s) = Sτ (f s)

sound-≤ : ∀ {Ψ Ψ' : SEnv n m} {Σ A A'}
  → (s : Ψ ⊢ A ≤ Σ ⊣ Ψ' ↪ A')
  → (Ψ→Γ Ψ) ⊢ (f s) # A ≤ A'
sound-≤ s-int = s-int
sound-≤ (s-empty p) = {!!}
sound-≤ s-var = {!!}
sound-≤ (s-ex-l^ x x₁ x₂) = {!!}
sound-≤ (s-ex-l= x x₁ s s₁) = {!!}
sound-≤ (s-ex-r^ x x₁ x₂) = {!!}
sound-≤ (s-ex-r= x x₁ s s₁) = {!!}
sound-≤ (s-arr s s₁) = s-arr₁ {!sound-≤ s!} {!sound-≤ s₁!}
sound-≤ (s-term-c x x₁ s) = {!!}
sound-≤ (s-term-o x x₁ s s₁) = {!!}
sound-≤ (s-∀ s) = {!!}
sound-≤ (s-∀l-^ s) = {!!}
sound-≤ (s-∀l-eq s) = {!!}
sound-≤ (s-∀-t s) = s-∀lτ {!sound-≤ s!}

app-elim : ∀ {Γ : Env n m} {A₁ Σ Ψ A e}
  → (s : 𝕓 Γ ⊢ A₁ ≤ Σ ⊣ Ψ ↪ A)
  → Γ ⊢ Z # e ⦂ A₁
  → Γ ⊢ (f s) # e ⦂ A
app-elim s-int ⊢e = ⊢sub' ⊢e s-int
app-elim (s-empty p) ⊢e = {!!}
app-elim s-var ⊢e = {!!}
app-elim (s-arr s s₁) ⊢e = ⊢sub' ⊢e (s-arr₁ {!!} {!!}) -- implied by soundness of sub
app-elim (s-term-c x x₁ s) ⊢e = ⊢sub' ⊢e {!!}
app-elim (s-term-o x x₁ s s₁) ⊢e = ⊢sub' ⊢e {!!}
app-elim (s-∀ s) ⊢e = {!!}
app-elim (s-∀l-^ s) ⊢e = {!!}
app-elim (s-∀l-eq s) ⊢e = {!!}
app-elim (s-∀-t s) ⊢e = {!!}

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
sound-i {e̅ = e ∷a e̅} (⊢lam₂ ⊢e ⊢e₁) (have-a spl) = subst e̅ (sound-i ⊢e₁ (spl-weaken spl)) (sound-i-0 ⊢e)

sound-i (⊢sub ⊢e s) spl = {!!}

{- let ind-e = sound-i-0 ⊢e
                              ind-s = sound-≤ s
                          in {!⊢sub' ind-e ind-s!}
-}                          

{-
sound-i (⊢sub ⊢e (s-empty p)) none-□ = {!sound-i-0 ⊢e!} -- obvious
sound-i (⊢sub ⊢e (s-term-c x x₁ s)) (have-a spl) = {!!} -- ok
sound-i (⊢sub ⊢e (s-term-o x x₁ s s₁)) (have-a spl) = {!!}
sound-i (⊢sub ⊢e (s-∀l-^ s)) (have-a spl) = {!!}
sound-i (⊢sub ⊢e (s-∀l-eq s)) (have-a spl) = {!!}
sound-i (⊢sub ⊢e (s-∀-t s)) (have-t spl) = {!!}
-}

-- (𝕓 Γ ⊢ A₁ ≤ Σ ⊣ Ψ ↪ A) ~ j
sound-i (⊢tabs₁ ⊢e) none-□ = ⊢tabs₁ (sound-i-0 ⊢e)
sound-i (⊢tapp ⊢e) spl = sound-i ⊢e (have-t spl)

sound-c (⊢app ⊢e) spl = sound-c ⊢e (have-a spl)
sound-c (⊢lam₁ ⊢e) none-τ = ⊢lam₁ (sound-c-0 ⊢e)
sound-c {e̅ = e ∷a e̅} (⊢lam₂ ⊢e ⊢e₁) (have-a spl) = subst e̅ (sound-c ⊢e₁ (spl-weaken spl)) (sound-i-0 ⊢e)
sound-c (⊢sub ⊢e s) spl = {!!}
sound-c (⊢tapp ⊢e) spl = sound-c ⊢e (have-t spl)

-- j <= length Σ


-- f : ∀a. a -> a -> a

-- f 1 2

-- f 1 2

-- f => ∀a. a -> a -> a
-- ∀a. a -> a -> a <: [1] -> [2] -> [] ~> Int -> Int -> Int
-- [1] -> [2] -> [] => f => Int

{-
|- (S 0) # f => Int -> Int -> Int
1  => Int
---------------
f 1 => Int -> Int     2 <= Int
------------------------------------ App1
f 1 2
-}

{-
∀a. a -> a -> a <:(S 0) Int -> Int -> Int


1 => Int a= Int
--------------------------------------------------------
∀a. a -> a -> a <: [1] -> [2] -> [] ~> Int -> Int -> Int
-}


{-
suppose I have j         -- j     App2
suppose lengh e̅ = k      -- k - j App1 (go first)

the j is related to the environments Ψ

-}
