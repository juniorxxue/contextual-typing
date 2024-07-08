module STLC.Decl where

open import STLC.Prelude
open import STLC.Common

----------------------------------------------------------------------
--+                                                                +--
--+                             Typing                             +--
--+                                                                +--
----------------------------------------------------------------------

-- counter, different from n in paper, we use j to represent
data Counter : Set where
  ∞ : Counter
  Z : Counter
  S : Counter → Counter

-- nonZero counter, used in subsumption rule
data ¬Z : Counter → Set where
  ¬Z-∞ : ¬Z ∞
  ¬Z-S : ∀ {j} → ¬Z (S j)

infix 4 _⊢_#_⦂_

data _⊢_#_⦂_ : Env → Counter → Term → Type → Set where

  ⊢int : ∀ {Γ i}
    → Γ ⊢ Z # (lit i) ⦂ Int

  ⊢var : ∀ {Γ x A}
    → Γ ∋ x ⦂ A
    → Γ ⊢ Z # ` x ⦂ A

  ⊢ann : ∀ {Γ e A}
    → Γ ⊢ ∞ # e ⦂ A
    → Γ ⊢ Z # (e ⦂ A) ⦂ A

  -- instead of meta-operations on paper, we split it into two rules in Agda
  -- to make it more structrual
  ⊢lam-∞ : ∀ {Γ e A B}
    → Γ , A ⊢ ∞ # e ⦂ B
    → Γ ⊢ ∞ # (ƛ e) ⦂ A `→ B

  ⊢lam-n : ∀ {Γ e A B j}
    → Γ , A ⊢ j # e ⦂ B
    → Γ ⊢ S j # (ƛ e) ⦂ A `→ B

  ⊢app₁ : ∀ {Γ e₁ e₂ A B}
    → Γ ⊢ Z # e₁ ⦂ A `→ B
    → Γ ⊢ ∞ # e₂ ⦂ A
    → Γ ⊢ Z # e₁ · e₂ ⦂ B

  ⊢app₂ : ∀ {Γ e₁ e₂ A B j}
    → Γ ⊢ (S j) # e₁ ⦂ A `→ B
    → Γ ⊢ Z # e₂ ⦂ A
    → Γ ⊢ j # e₁ · e₂ ⦂ B

  ⊢sub : ∀ {Γ e A j}
    → Γ ⊢ Z # e ⦂ A
    → ¬Z j
    → Γ ⊢ j # e ⦂ A

----------------------------------------------------------------------
--+                            Examples                            +--
----------------------------------------------------------------------

-- let-binding encoding
infix 4 𝕝𝕖𝕥_𝕚𝕟_

𝕝𝕖𝕥_𝕚𝕟_ : Term → Term → Term
𝕝𝕖𝕥 e₁ 𝕚𝕟 e₂ = (ƛ e₂) · e₁

ex-part1 : Term
ex-part1 = (ƛ ((` 0) · (lit 1))) ⦂ ((Int `→ Int) `→ Int)

ex-part2 : Term
ex-part2 = 𝕝𝕖𝕥 ` 0 𝕚𝕟 ƛ (` 0)

ex : Term
ex = 𝕝𝕖𝕥 (lit 1) 𝕚𝕟 (ex-part1 · ex-part2)

⊢let : ∀ {Γ j e₁ e₂ A B}
  → Γ ⊢ Z # e₁ ⦂ A
  → Γ , A ⊢ j # e₂ ⦂ B
  → Γ ⊢ j # 𝕝𝕖𝕥 e₁ 𝕚𝕟 e₂ ⦂ B
⊢let ⊢e₁ ⊢e₂ = ⊢app₂ (⊢lam-n ⊢e₂) ⊢e₁  

ex-derivation : ∀ {Γ} → Γ ⊢ Z # ex ⦂ Int
ex-derivation = ⊢let ⊢int
                     (⊢app₁ (⊢ann (⊢lam-∞ (⊢app₂ (⊢sub (⊢var Z) ¬Z-S) ⊢int)))
                            (⊢let (⊢var Z) (⊢lam-∞ (⊢sub (⊢var Z) ¬Z-∞))))


ex2-env : Env
ex2-env = ∅ , (Int `→ Int) `→ Int `→ Int

ex2-exp : Term
ex2-exp = (ƛ ` 1) · (lit 1) · (ƛ ` 0) · (lit 2)

ex2-derivation : ex2-env ⊢ Z # ex2-exp ⦂ Int
ex2-derivation = ⊢app₁
                  (⊢app₁ (⊢app₂ (⊢lam-n (⊢var (S Z))) ⊢int)
                   (⊢lam-∞ (⊢sub (⊢var Z) ¬Z-∞)))
                  (⊢sub ⊢int ¬Z-∞)
