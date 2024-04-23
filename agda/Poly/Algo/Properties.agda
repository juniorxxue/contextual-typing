module Poly.Algo.Properties where

open import Poly.Common
open import Poly.Algo

-- open import Relation.Binary.PropositionalEquality.≡-Reasoning
-- why does it not work?

data Γext : SEnv n m → SEnv n m → SEnv n' m' → SEnv n' m' → Set where
  base : ∀ {Γ : Env n m} {Ψ}
    → Γext (𝕓 Γ) Ψ (𝕓 Γ) Ψ
  uvar : ∀ {Ψ Ψ' : SEnv n m} {Γ : Env n' m'} {Ψ''}
    → Γext Ψ Ψ' (𝕓 Γ) Ψ''
    → Γext (Ψ ,∙) (Ψ' ,∙) (𝕓 Γ) Ψ'' 
  evar : ∀ {Ψ Ψ' : SEnv n m} {Γ : Env n' m'} {Ψ''}
    → Γext Ψ Ψ' (𝕓 Γ) Ψ''
    → Γext (Ψ ,^) (Ψ' ,^) (𝕓 Γ) Ψ''
  svar : ∀ {Ψ Ψ' : SEnv n m} {A} {Γ : Env n' m'} {Ψ''}
    → Γext Ψ Ψ' (𝕓 Γ) Ψ''
    → Γext (Ψ ,^) (Ψ' ,= A) (𝕓 Γ) Ψ''
  

s-closed-gen : ∀ {Ψ Ψ' : SEnv n m} {Γ : Env n' m'} {A B Σ Ψ''}
  → Ψ ⊢ A ≤ Σ ⊣ Ψ' ↪ B
  → Γext Ψ Ψ' (𝕓 Γ) Ψ''
  → (𝕓 Γ) ≡ Ψ''
s-closed-gen s-int ext = {!!}
s-closed-gen (s-empty p) ext = {!!}
s-closed-gen s-var ext = {!!}
s-closed-gen (s-ex-l^ x x₁ x₂) ext = {!!}
s-closed-gen (s-ex-l= x x₁ s s₁) ext = {!!}
s-closed-gen (s-ex-r^ x x₁ x₂) ext = {!!}
s-closed-gen (s-ex-r= x x₁ s s₁) ext = {!!}
s-closed-gen (s-arr s s₁) ext = {!!}
s-closed-gen (s-term-c x x₁ s) ext = s-closed-gen s {!!}
s-closed-gen (s-term-o x x₁ s s₁) ext = s-closed-gen s {!!}
s-closed-gen (s-∀ s) ext = s-closed-gen s (uvar ext)
s-closed-gen (s-∀l-^ s) ext = s-closed-gen s (evar ext)
s-closed-gen (s-∀l-eq s) ext = s-closed-gen s (svar ext)
s-closed-gen (s-∀-t s) ext = s-closed-gen s ext

s-closed : ∀ {Γ : Env n m} {Ψ A B Σ}
  → 𝕓 Γ ⊢ A ≤ Σ ⊣ Ψ ↪ B
  → Ψ ≡ 𝕓 Γ
  
s-closed s-int = refl
s-closed (s-empty p) = refl
s-closed s-var = refl
s-closed (s-arr s s₁) rewrite s-closed s = s-closed s₁
s-closed (s-term-c x x₁ s) = s-closed s
s-closed (s-term-o x x₁ s s₁) rewrite s-closed s = s-closed s₁
s-closed (s-∀ s) = {!!}
s-closed (s-∀l-^ s) = {!!}
s-closed (s-∀l-eq s) = {!!}
s-closed (s-∀-t s) = s-closed s
