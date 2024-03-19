module Record.Algo.Sizes where

open import Record.Prelude hiding (_≤?_) renaming (_≤_ to _≤n_)

open ≤-Reasoning

sz-case-1 : ∀ {m n o k} → m + suc (n + o) < k → n + 0 < k
sz-case-1 {m} {n} {o} {k} m+1+n+o<k = begin-strict
  n + 0               ≤⟨ m≤m+n (n + 0) (suc m + o)  ⟩
  n + 0 + (suc m + o) ≡⟨ solve (n ∷ m ∷ o ∷ []) ⟩
  m + suc (n + o)     <⟨ m+1+n+o<k ⟩
  k                   ∎
  
sz-case-2 : ∀ {m n o k}
  → suc (m + n + o) < k
  → m + suc (n + o) < k
sz-case-2 {m} {n} {o} {k} sz = begin-strict
  m + suc (n + o)     ≡⟨ solve ⟦ n , m , o ⟧ ⟩
  suc (m + n + o)     <⟨ sz ⟩
  k                   ∎

sz-case-3' : ∀ {m n o k}
  → m + (1 + n + o) < k
  → m + o < k
sz-case-3' {m} {n} {o} {k} sz = begin-strict
  m + o              <⟨ m<m+n (m + o) (s≤s z≤n) ⟩
  m + o + (1 + n)    ≡⟨ solve ⟦ n , m , o ⟧ ⟩
  m + (1 + n + o)    <⟨ sz ⟩
  k                  ∎  

sz-case-4 : ∀ n {m o k}
  → n + m + o < k
  → n + o < k
sz-case-4 n {m} {o} {k} sz = begin-strict
  n + o         ≤⟨ m≤m+n (n + o) m ⟩
  n + o + m     ≡⟨ solve ⟦ n , m , o ⟧ ⟩
  n + m + o     <⟨ sz ⟩
  k             ∎

sz-case-5 : ∀ m {n o k}
  → n + m + o < k
  → m + o < k
sz-case-5 m {n} {o} {k} sz = begin-strict
  m + o         ≤⟨ m≤m+n (m + o) n ⟩
  m + o + n     ≡⟨ solve ⟦ n , m , o ⟧ ⟩
  n + m + o     <⟨ sz ⟩
  k             ∎

sz-case-6 : ∀ {m n o k}
  → m + (1 + (n + o)) ≤n k
  → m + n < k
sz-case-6 {m} {n} {o} {k} sz = begin-strict
  m + n              <⟨ m<m+n (m + n) (s≤s z≤n) ⟩
  m + n + (1 + o)    ≡⟨ solve ⟦ n , m , o ⟧ ⟩
  m + (1 + (n + o))  ≤⟨ sz ⟩
  k                  ∎
  
sz-case-7 : ∀ {m n o k}
  → m + (1 + (n + o)) ≤n k
  → m + o < k
sz-case-7 {m} {n} {o} {k} sz = begin-strict
  m + o              <⟨ m<m+n (m + o) (s≤s z≤n) ⟩
  m + o + (1 + n)    ≡⟨ solve ⟦ n , m , o ⟧ ⟩
  m + (1 + (n + o))  ≤⟨ sz ⟩
  k                  ∎

sz-case-8 : ∀ o m{n p k}
  → m + n + (1 + (o + p)) < k
  → o + m < k
sz-case-8 o m {n} {p} {k} sz = begin-strict
  o + m                 <⟨ m<m+n (o + m) (s≤s z≤n) ⟩
  o + m + (1 + n + p)   ≡⟨ solve ⟦ n , m , p , o ⟧ ⟩
  m + n + (1 + (o + p)) <⟨ sz ⟩
  k                     ∎

sz-case-9 : ∀ n p {m o  k}
  → m + n + (1 + (o + p)) < k
  → n + p < k
sz-case-9 n p {m} {o} {k} sz = begin-strict
  n + p                 <⟨ m<m+n (n + p) (s≤s z≤n) ⟩
  n + p + (1 + m + o)   ≡⟨ solve ⟦ n , m , p , o ⟧ ⟩
  m + n + (1 + (o + p)) <⟨ sz ⟩
  k                     ∎
                                
sz-case-10 : ∀ {m o k}
  → o + m < k
  → m < 1 + k
sz-case-10 {m} {o} {k} sz = ≤-trans (s≤s (m≤n+m m o)) (<-trans sz (s≤s m≤m))

sz-case-11 : ∀ {m o k}
  → m + o < k
  → m + 0 < k
sz-case-11 {m} {o} {k} sz rewrite +-comm m 0 = ≤-trans (s≤s (m≤m+n m o)) sz

sz-case-12 : ∀ {m n k}
  → 1 + (m + (1 + (1 + n))) < k
  → m + n < k
sz-case-12 {m} {n} {k} sz = begin-strict
  m + n                   <⟨ m<m+n (m + n) (s≤s z≤n) ⟩
  m + n + (1 + 1 + 1)     ≡⟨ solve ⟦ m , n ⟧ ⟩
  1 + (m + (1 + (1 + n))) <⟨ sz ⟩
  k                       ∎

sz-case-13 : ∀ {m n k}
  → 1 + (m + (1 + n)) < k
  → m + n < k
sz-case-13 {m} {n} {k} sz rewrite +-comm 1 n | sym (+-assoc m n 1) = ≤-trans (s≤s (m≤n⇒m≤1+n (m≤m+n (m + n) 1))) sz

sz-case-14 : ∀ {m n k}
  → 1 + (m + n) < k
  → m + (1 + n) < k
sz-case-14 {m} {n} {k} sz rewrite +-comm 1 n | sym (+-assoc m n 1) | +-comm (m + n) 1 | +-comm m n = sz  

sz-case-15 : ∀ {m k}
  → m + 1 < k
  → m + 0 < k
sz-case-15 {m} {k} sz rewrite +-comm m 0 = ≤-trans (s≤s (m≤m+n m 1)) sz

sz-case-16 : ∀ m n {o k}
  → m + (1 + (n + o)) < k
  → m + 0 < k
sz-case-16 m n {o} {k} sz rewrite +-comm m 0 = ≤-trans (s≤s (m≤m+n m (1 + (n + o)))) sz

sz-case-17 : ∀ {m n o k}
  → m + (1 + (n + o)) < k
  → (1 + (n + o)) < k
sz-case-17 {m} {n} {o} {k} sz = ≤-trans (s≤s (m≤n+m (1 + (n + o)) m)) sz  
