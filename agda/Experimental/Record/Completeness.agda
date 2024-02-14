module Record.Completeness where

open import Record.Prelude hiding (_≤?_) renaming (_≤_ to _≤n_)
open import Record.Common
open import Record.Decl
open import Record.Properties
open import Record.Algo
open import Record.Algo.Properties

infix 3 _⊢_~_
infix 3 _⊢_~i_
infix 3 _⊢_~j_

data _⊢_~_ : Context → Counter × Type → Hint → Set
data _⊢_~i_ : Context → ICounter × Type → Hint → Set
data _⊢_~j_ : Context → CCounter × Type → Hint → Set

data _⊢_~_ where

  ~i : ∀ {Γ i A H}
    → Γ ⊢ ⟨ i , A ⟩ ~i H
    → Γ ⊢ ⟨ 𝕚 i , A ⟩ ~ H

  ~∞ : ∀ {Γ A}
    → Γ ⊢ ⟨ ∞ , A ⟩ ~ τ A

  ~∞⇒ : ∀ {Γ A B e H}
    → Γ ⊢a τ A ⇛ e ⇛ A
    → Γ ⊢ ⟨ ∞ , B ⟩ ~ H
    → Γ ⊢ ⟨ ∞ , A ⇒ B ⟩ ~ ⟦ e ⟧⇒ H

data _⊢_~i_ where

  ~j : ∀ {Γ j A H}
    → Γ ⊢ ⟨ j , A ⟩ ~j H
    → Γ ⊢ ⟨ 𝕓 j , A ⟩ ~i H

  ~S⇒ : ∀ {Γ i A B H e}
    → Γ ⊢a □ ⇛ e ⇛ A
    → Γ ⊢ ⟨ i , B ⟩ ~i H
    → Γ ⊢ ⟨ S⇒ i , A ⇒ B ⟩ ~i (⟦ e ⟧⇒ H)
    
data _⊢_~j_ where

  ~Z : ∀ {Γ A}
    → Γ ⊢ ⟨ Z , A ⟩ ~j □

  ~S⇐ : ∀ {Γ j A B e H}
    → Γ ⊢a τ A ⇛ e ⇛ A
    → Γ ⊢ ⟨ j , B ⟩ ~j H
    → Γ ⊢ ⟨ S⇐ j , A ⇒ B ⟩ ~j (⟦ e ⟧⇒ H)

  ~Sl : ∀ {Γ j A l H}
    → Γ ⊢ ⟨ j , A ⟩ ~j H
    → Γ ⊢ ⟨ Sl j , τ⟦ l ↦ A ⟧ ⟩ ~j (⌊ l ⌋⇒ H)

~weaken : ∀ {Γ A i B H n n≤l}
  → Γ ⊢ ⟨ i , B ⟩ ~ H
  → (Γ ↑ n [ n≤l ] A) ⊢ ⟨ i , B ⟩ ~ (H ⇧ n)

~iweaken : ∀ {Γ A i B H n n≤l}
  → Γ ⊢ ⟨ i , B ⟩ ~i H
  → (Γ ↑ n [ n≤l ] A) ⊢ ⟨ i , B ⟩ ~i (H ⇧ n)
  
~jweaken : ∀ {Γ A j B H n n≤l}
  → Γ ⊢ ⟨ j , B ⟩ ~j H
  → (Γ ↑ n [ n≤l ] A) ⊢ ⟨ j , B ⟩ ~j (H ⇧ n)

~weaken (~i x) = ~i (~iweaken x)
~weaken ~∞ = ~∞
~weaken (~∞⇒ ⊢e' i~H) = ~∞⇒ (⊢a-weaken ⊢e') (~weaken i~H)

~iweaken (~j x) = ~j (~jweaken x)
~iweaken (~S⇒ x i~H) = ~S⇒ (⊢a-weaken x) (~iweaken i~H)

~jweaken ~Z = ~Z
~jweaken (~S⇐ x j~H) = ~S⇐ (⊢a-weaken x) (~jweaken j~H)
~jweaken (~Sl j~H) = ~Sl (~jweaken j~H)

H≢□→i≢Z : ∀ {Γ H i A}
  → i ≢ 𝕫
  → Γ ⊢ ⟨ i , A ⟩ ~ H
  → H ≢ □

complete : ∀ {Γ H i e A}
  → Γ ⊢d i # e ⦂ A
  → Γ ⊢ ⟨ i , A ⟩ ~ H
  → Γ ⊢a H ⇛ e ⇛ A

complete-≤ : ∀ {Γ H i A B}
  → B ≤d i # A
  → Γ ⊢ ⟨ i , A ⟩ ~ H
  → Γ ⊢a B ≤ H ⇝ A

complete-r : ∀ {Γ rs A}
  → Γ ⊢r 𝕫 # rs ⦂ A
  → Γ ⊢r □ ⇛ rs ⇛ A
complete-r ⊢r-nil = ⊢a-nil
complete-r (⊢r-one x) = ⊢a-one (complete x (~i (~j ~Z)))
complete-r (⊢r-cons x ⊢r) = ⊢a-cons (complete x (~i (~j ~Z))) (complete-r ⊢r)

complete-≤ B≤A i~H = {!!}

complete ⊢d-c (~i (~j ~Z)) = ⊢a-c
complete (⊢d-var x) (~i (~j ~Z)) = ⊢a-var x
complete (⊢d-ann ⊢e) (~i (~j ~Z)) = ⊢a-ann (complete ⊢e ~∞)
complete (⊢d-lam₁ ⊢e) ~∞ = ⊢a-lam₁ (complete ⊢e ~∞)
complete (⊢d-lam₁ ⊢e) (~∞⇒ x i~H) = {!!}
complete (⊢d-lam₂ ⊢e) (~i (~S⇒ ⊢e' i~H)) = ⊢a-lam₂ ⊢e' (complete ⊢e (~weaken {n≤l = z≤n} (~i i~H)))
complete (⊢d-app⇐ ⊢e ⊢e₁) (~i (~j x)) = ⊢a-app (complete ⊢e (~i (~j (~S⇐ (complete ⊢e₁ ~∞) x))))
complete (⊢d-app∞∞ ⊢e ⊢e₁) ~∞ = ⊢a-app (complete ⊢e {!!})
complete (⊢d-app∞∞ ⊢e ⊢e₁) (~∞⇒ x i~H) = ⊢a-app (complete ⊢e (~∞⇒ (complete ⊢e₁ ~∞) (~∞⇒ x i~H)))
complete (⊢d-app∞ ⊢e ⊢e₁) i~H = {!!}
complete (⊢d-app⇒ ⊢e ⊢e₁) i~H = {!!}
complete (⊢d-sub ⊢e x x₁) i~H = {!!}
complete (⊢d-& ⊢e ⊢e₁) i~H = {!!}
complete (⊢d-rcd x) i~H = {!!}
complete (⊢d-prj ⊢e) i~H = {!!}
complete (⊢d-prj∞ ⊢e) i~H = {!!}
