module Record.Dec where

-- conclude the decidability of QTAS via
-- soundness, completeness and decidiblity of algorithmic formulation

open import Record.Prelude
open import Record.Common
open import Record.Decl
open import Record.Decl.Properties
open import Record.Algo
open import Record.Algo.Properties
open import Record.Algo.WellFormed
open import Record.Algo.Decidable
open import Record.Soundness
open import Record.Completeness

qtas-dec-0 : ∀ Γ e
  → WFG Γ → WFE e
  → Dec (∃[ A ](Γ ⊢d ♭ Z # e ⦂ A))
qtas-dec-0 Γ e wfg wfe with ⊢a-dec-0 wfg wfh-□ wfe
... | yes ⟨ A' , ⊢e ⟩ = yes ⟨ A' , (sound-inf-0 ⊢e) ⟩
... | no ¬p = no λ where
  ⟨ A' , ⊢e' ⟩ → ¬p ⟨ A' , (complete ⊢e' (~j ~Z)) ⟩
