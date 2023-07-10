module Bot.Decl.Properties where

open import Bot.Prelude
open import Bot.Common
open import Bot.Decl
open import Bot.Properties

----------------------------------------------------------------------
--+                                                                +--
--+                           Weakening                            +--
--+                                                                +--
----------------------------------------------------------------------

⊢d-weaken :
    Γ ⊢d ∞/n # e ⦂ B
  → (n≤l : n ≤ length Γ)
  → Γ ↑ n [ n≤l ] A ⊢d ∞/n # (e ↑ n) ⦂ B
⊢d-weaken ⊢d-int n≤l = ⊢d-int
⊢d-weaken (⊢d-var x∈Γ) n≤l = ⊢d-var (∋-weaken x∈Γ n≤l)
⊢d-weaken (⊢d-lam₁ ⊢e) n≤l = ⊢d-lam₁ (⊢d-weaken ⊢e (s≤s n≤l))
⊢d-weaken (⊢d-lam₂ ⊢e) n≤l = ⊢d-lam₂ (⊢d-weaken ⊢e (s≤s n≤l))
⊢d-weaken (⊢d-lam₃ ⊢e) n≤l = ⊢d-lam₃ (⊢d-weaken ⊢e (s≤s n≤l))
⊢d-weaken (⊢d-app₁ ⊢f ⊢e) n≤l = ⊢d-app₁ (⊢d-weaken ⊢f n≤l) (⊢d-weaken ⊢e n≤l)
⊢d-weaken (⊢d-app₂ ⊢f ⊢e) n≤l = ⊢d-app₂ (⊢d-weaken ⊢f n≤l) (⊢d-weaken ⊢e n≤l)
⊢d-weaken (⊢d-app₃ ⊢f ⊢e) n≤l = ⊢d-app₃ (⊢d-weaken ⊢f n≤l) (⊢d-weaken ⊢e n≤l)
⊢d-weaken (⊢d-ann ⊢e) n≤l = ⊢d-ann (⊢d-weaken ⊢e n≤l)
⊢d-weaken (⊢d-sub ⊢e A≤B) n≤l = ⊢d-sub (⊢d-weaken ⊢e n≤l) A≤B

⊢d-weaken-0 :
    Γ ⊢d ∞/n # e ⦂ B
  → Γ , A ⊢d ∞/n # e ↑ 0 ⦂ B
⊢d-weaken-0 ⊢e = ⊢d-weaken ⊢e z≤n  

----------------------------------------------------------------------
--+                                                                +--
--+                         Strengthening                          +--
--+                                                                +--
----------------------------------------------------------------------

⊢d-strengthen :
    Γ ⊢d ∞/n # e ⦂ A
  → e ~↑~ n
  → (n≤l : n ≤ length Γ)
  → Γ ↓ n [ n≤l ] ⊢d ∞/n # e ↓ n ⦂ A
⊢d-strengthen ⊢d-int sd n≤l = ⊢d-int
⊢d-strengthen (⊢d-var x∈Γ) sd n≤l = ⊢d-var (∋-strenghthen x∈Γ sd n≤l)
⊢d-strengthen (⊢d-lam₁ ⊢e) (sd-lam sd) n≤l = ⊢d-lam₁ (⊢d-strengthen ⊢e sd (s≤s n≤l))
⊢d-strengthen (⊢d-lam₂ ⊢e) (sd-lam sd) n≤l = ⊢d-lam₂ (⊢d-strengthen ⊢e sd (s≤s n≤l))
⊢d-strengthen (⊢d-lam₃ ⊢e) (sd-lam sd) n≤l = ⊢d-lam₃ (⊢d-strengthen ⊢e sd (s≤s n≤l))
⊢d-strengthen (⊢d-app₁ ⊢f ⊢e) (sd-app sd sd₁) n≤l = ⊢d-app₁ (⊢d-strengthen ⊢f sd n≤l) (⊢d-strengthen ⊢e sd₁ n≤l)
⊢d-strengthen (⊢d-app₂ ⊢f ⊢e) (sd-app sd sd₁) n≤l = ⊢d-app₂ (⊢d-strengthen ⊢f sd n≤l) (⊢d-strengthen ⊢e sd₁ n≤l)
⊢d-strengthen (⊢d-app₃ ⊢f ⊢e) (sd-app sd sd₁) n≤l = ⊢d-app₃ (⊢d-strengthen ⊢f sd n≤l) (⊢d-strengthen ⊢e sd₁ n≤l)
⊢d-strengthen (⊢d-ann ⊢e) (sd-ann sd) n≤l = ⊢d-ann (⊢d-strengthen ⊢e sd n≤l)
⊢d-strengthen (⊢d-sub ⊢e A≤B) sd n≤l = ⊢d-sub (⊢d-strengthen ⊢e sd n≤l) A≤B

⊢d-strengthen-0 :
    Γ , A ⊢d ∞/n # e ↑ 0 ⦂ B
  → Γ ⊢d ∞/n # e ⦂ B
⊢d-strengthen-0 {e = e} ⊢e with ⊢d-strengthen ⊢e ↑-shifted z≤n
... | ind-e rewrite ↑-↓-id e 0 = ind-e

----------------------------------------------------------------------
--+                                                                +--
--+                       Check Subsumption                        +--
--+                                                                +--
----------------------------------------------------------------------

⊢d-app-2 :
    Γ ⊢d (c (suc n)) # e₁ ⦂ A ⇒ B
  → Γ ⊢d c 0 # e₂ ⦂ A'
  → ∃[ B' ] Γ ⊢d (c n) # e₁ · e₂ ⦂ B' × B' ≤d B
⊢d-app-2 (⊢d-var x∈Γ) ⊢e₂ = {!!}
⊢d-app-2 (⊢d-lam₂ ⊢e₁) ⊢e₂ = {!!}
⊢d-app-2 (⊢d-app₂ ⊢e₁ ⊢e₃) ⊢e₂ = {!!}
⊢d-app-2 (⊢d-ann ⊢e₁) ⊢e₂ = {!!}

infix 6 _>>_
_>>_ : Context → Context → Context
Γ₁ >> ∅ = Γ₁
Γ₁ >> (Γ₂ , A) = (Γ₁ >> Γ₂) , A

narrow-var :
    (Γ₁ , A) >> Γ₂ ∋ n ⦂ B
  → C ≤d A
  → ∃[ D ] (((Γ₁ , C) >> Γ₂ ∋ n ⦂ D) × (D ≤d B))
narrow-var {Γ₁} {Γ₂ = ∅} {C = C} Z C≤A = ⟨ C , ⟨ Z , C≤A ⟩ ⟩
narrow-var {Γ₁} {Γ₂ = ∅} {B = B} (S n∈Γ) C≤A = ⟨ B , ⟨ S n∈Γ , ≤d-refl ⟩ ⟩
narrow-var {Γ₁} {Γ₂ = Γ₂ , E} Z C≤A = ⟨ E , ⟨ Z , ≤d-refl ⟩ ⟩
narrow-var {Γ₁} {Γ₂ = Γ₂ , E} (S n∈Γ) C≤A with narrow-var {Γ₁} {Γ₂ = Γ₂} n∈Γ C≤A
... | ⟨ D , ⟨ n∈Γ' , D≤B ⟩ ⟩ = ⟨ D , ⟨ S n∈Γ' , D≤B ⟩ ⟩

narrow :
    (Γ₁ , A) >> Γ₂ ⊢d ∞/n # e ⦂ B
  → C ≤d A
  → ∃[ D ] (((Γ₁ , C) >> Γ₂ ⊢d ∞/n # e ⦂ D) × (D ≤d B))

narrow-1 :
    Γ , A ⊢d ∞/n # e ⦂ B
  → C ≤d A
  → ∃[ D ](Γ , C ⊢d ∞/n # e ⦂ D × D ≤d B)

chk-sub :
    Γ ⊢d ∞ # e ⦂ A
  → A ≤d B
  → Γ ⊢d ∞ # e ⦂ B
 
narrow {Γ₁ = Γ₁} {Γ₂ = Γ₂} ⊢d-int C≤A = {!!}
narrow {Γ₁ = Γ₁} {Γ₂ = Γ₂} (⊢d-var x) C≤A = {!!}
narrow {Γ₁ = Γ₁} {Γ₂ = Γ₂} (⊢d-lam₁ ⊢e) C≤A = {!!}
narrow {Γ₁ = Γ₁} {Γ₂ = Γ₂} (⊢d-lam₂ ⊢e) C≤A = {!!}
narrow {Γ₁ = Γ₁} {Γ₂ = Γ₂} (⊢d-lam₃ ⊢e) C≤A = {!!}

narrow {Γ₁ = Γ₁} {Γ₂ = Γ₂} (⊢d-app₁ ⊢f ⊢e) C≤A with narrow ⊢f C≤A | narrow ⊢e C≤A
... | ⟨ .Bot , ⟨ ⊢f' , ≤d-bot ⟩ ⟩ | ⟨ D , ⟨ ⊢e' , B≤D ⟩ ⟩ = ⟨ Bot , ⟨ (⊢d-app₁-bot ⊢f' ⊢e') , ≤d-bot ⟩ ⟩
... | ⟨ A' ⇒ B' , ⟨ ⊢f' , ≤d-arr ≤₁ ≤₂ ⟩ ⟩ | ⟨ D , ⟨ ⊢e' , B≤D ⟩ ⟩ = ⟨ B' , ⟨ (⊢d-app₁ ⊢f' (chk-sub ⊢e' (≤d-trans B≤D ≤₁))) , ≤₂ ⟩ ⟩

narrow {Γ₁ = Γ₁} {Γ₂ = Γ₂} (⊢d-app₁-bot ⊢f ⊢e) C≤A with narrow ⊢f C≤A | narrow ⊢e C≤A
... | ⟨ .Bot , ⟨ ⊢f' , ≤d-bot ⟩ ⟩ | ⟨ D , ⟨ ⊢e' , B≤D ⟩ ⟩ = ⟨ Bot , ⟨ (⊢d-app₁-bot ⊢f' ⊢e') , ≤d-bot ⟩ ⟩

narrow {Γ₁ = Γ₁} {Γ₂ = Γ₂} (⊢d-app₂ ⊢f ⊢e) C≤A with narrow ⊢f C≤A | narrow ⊢e C≤A
... | ⟨ .Bot , ⟨ ⊢f' , ≤d-bot ⟩ ⟩ | ⟨ D , ⟨ ⊢e' , B≤D ⟩ ⟩ = ⟨ Bot , ⟨ (⊢d-app₂-bot ⊢f' ⊢e') , ≤d-bot ⟩ ⟩
... | ⟨ A' ⇒ B' , ⟨ ⊢f' , ≤d-arr ≤₁ ≤₂ ⟩ ⟩ | ⟨ D , ⟨ ⊢e' , B≤D ⟩ ⟩ = ⟨ B' , ⟨ (⊢d-app₂ {!!} {!!}) , ≤₂ ⟩ ⟩

narrow {Γ₁ = Γ₁} {Γ₂ = Γ₂} (⊢d-app₂-bot ⊢f ⊢e) C≤A = {!!}

narrow {Γ₁ = Γ₁} {Γ₂ = Γ₂} (⊢d-app₃ ⊢f ⊢e) C≤A with narrow ⊢f C≤A | narrow ⊢e C≤A
... | ⟨ .Bot , ⟨ ⊢f' , ≤d-bot ⟩ ⟩ | ⟨ D , ⟨ ⊢e' , B≤D ⟩ ⟩ = ⟨ Bot , ⟨ (⊢d-app₃ (chk-sub ⊢f' ≤d-bot) ⊢e') , ≤d-bot ⟩ ⟩
... | ⟨ A' ⇒ B' , ⟨ ⊢f' , ≤d-arr ≤₁ ≤₂ ⟩ ⟩ | ⟨ D , ⟨ ⊢e' , B≤D ⟩ ⟩ = ⟨ B' , ⟨ (⊢d-app₃ (chk-sub ⊢f' (≤d-arr (≤d-trans B≤D ≤₁) ≤d-refl)) ⊢e') , ≤₂ ⟩ ⟩

narrow {Γ₁ = Γ₁} {Γ₂ = Γ₂} (⊢d-ann ⊢e) C≤A = {!!}
narrow {Γ₁ = Γ₁} {Γ₂ = Γ₂} (⊢d-sub ⊢e x) C≤A = {!!}

narrow-1 ⊢e C≤A = narrow {Γ₂ = ∅} ⊢e C≤A

chk-sub (⊢d-lam₁ ⊢e) ≤d-top with narrow-1 ⊢e ≤d-bot
... | ⟨ D , ⟨ ⊢e , A≤D ⟩ ⟩ = ⊢d-lam₃ (chk-sub ⊢e ≤d-top)
chk-sub (⊢d-lam₁ ⊢e) (≤d-arr C≤A B≤D) with narrow-1 ⊢e C≤A
... | ⟨ D , ⟨ ⊢e , A≤D ⟩ ⟩ = ⊢d-lam₁ (chk-sub ⊢e (≤d-trans A≤D B≤D))
chk-sub (⊢d-lam₃ ⊢e) ≤d-top = ⊢d-lam₃ ⊢e
chk-sub (⊢d-app₃ ⊢f ⊢e) A≤B = {!!}
chk-sub (⊢d-sub ⊢e A≤B') A≤B = ⊢d-sub ⊢e (≤d-trans A≤B' A≤B)


-- check subsumption /  may take a different view
-- Γ ⊢d ∞/n # e ⦂ A where ∞/n parts of the A comes from other

-- A ~> ∞/n As → T
-- As can be replaced by As'
-- then ∃T', Γ ⊢d ∞/n # e ⦂ As' → T' and T' ≤ T
