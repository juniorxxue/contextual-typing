open import Data.Nat 
open import Data.List
open import Data.Product renaming (_,_ to ⟨_,_⟩)
open import Relation.Binary.PropositionalEquality
open import Relation.Nullary

data Term : Set where
  num : ℕ → Term
  add : Term → Term → Term

_+s_ : Term → List Term → Term
_+s_ n [] = n
_+s_ n (n' ∷ ns) = (add n n') +s ns

lst-destruct-rev : ∀ (l : List Term)
  → 0 < length l
  → ∃[ x ] (∃[ xs ] (l ≡ (xs ++ x ∷ [])))
lst-destruct-rev (x ∷ []) (s≤s z≤n) = ⟨ x , ⟨ [] , refl ⟩ ⟩
lst-destruct-rev (x ∷ y ∷ l) (s≤s z≤n) with lst-destruct-rev (y ∷ l) (s≤s z≤n)
... | ⟨ x' , ⟨ xs' , eq ⟩ ⟩ rewrite eq = ⟨ x' , ⟨ x ∷ xs' , refl ⟩ ⟩

data Property : Term → Set where
  anything : ∀ {t} → Property t

lemma : ∀ e es → Property (e +s es)
lemma e es with length es >? 0
... | yes p with lst-destruct-rev es p
... | ⟨ fst , ⟨ fst₁ , eq ⟩ ⟩ rewrite eq = {!!} 
lemma e es | no ¬p = {!!}

