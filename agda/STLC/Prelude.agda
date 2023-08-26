module STLC.Prelude where

open import Data.Nat public
open import Data.Nat.Properties public
open import Data.String using (String) public
open import Relation.Nullary using (yes; no; Dec; ¬_) public
open import Relation.Nullary.Decidable using (True; toWitness; fromWitness) public
open import Function.Base using (case_of_; case_return_of_) public
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl; cong; sym; ≢-sym) public
open import Data.Empty public
open import Data.Product using (_×_; proj₁; proj₂; ∃; ∃-syntax) renaming (_,_ to ⟨_,_⟩) public
open import Data.List using (List; []; _∷_; _++_; reverse; map; foldr; downFrom) public

m+1≤n→m≤n : ∀ {m n}
  → suc m ≤ n
  → m ≤ n
m+1≤n→m≤n (s≤s m+1≤n) = m≤n⇒m≤1+n m+1≤n

n-1+1≡n+1-1 : ∀ {n}
  → 0 < n
  → suc (pred n) ≡ pred (suc n)
n-1+1≡n+1-1 (s≤s 0<n) = refl

m+1≰n+1⇒m≰n : ∀ {m n}
  → suc m ≰ suc n
  → m ≰ n
m+1≰n+1⇒m≰n m+1≰n+1 = λ m≤n → m+1≰n+1 (s≤s m≤n)  
  
m≰n⇒n<m : ∀ {m n}
  → m ≰ n
  → n < m
m≰n⇒n<m {zero} {zero} m≰n = ⊥-elim (m≰n z≤n)
m≰n⇒n<m {zero} {suc n} m≰n = ⊥-elim (m≰n z≤n)
m≰n⇒n<m {suc m} {zero} m≰n = s≤s z≤n
m≰n⇒n<m {suc m} {suc n} m≰n = s≤s (m≰n⇒n<m {m} {n} (m+1≰n+1⇒m≰n m≰n))

n<m⇒m≰n : ∀ {m n}
  → n < m
  → m ≰ n
n<m⇒m≰n {suc m} {zero} n<m = λ ()
n<m⇒m≰n {suc m} {suc n} (s≤s n<m) (s≤s m≤n) = n<m⇒m≰n {m} {n} n<m m≤n
