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

⊢d-weaken : ∀ {Γ cc e A B n}
  → Γ ⊢d cc ╏ e ⦂ B
  → (n≤l : n ≤ length Γ)
  → Γ ↑ n [ n≤l ] A ⊢d cc ╏ (e ↑ n) ⦂ B
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

⊢d-weaken-0 : ∀ {Γ cc e A B}
  → Γ ⊢d cc ╏ e ⦂ B
  → Γ , A ⊢d cc ╏ e ↑ 0 ⦂ B
⊢d-weaken-0 ⊢e = ⊢d-weaken ⊢e z≤n  

----------------------------------------------------------------------
--+                                                                +--
--+                         Strengthening                          +--
--+                                                                +--
----------------------------------------------------------------------

⊢d-strengthen : ∀ {Γ cc e A n}
  → Γ ⊢d cc ╏ e ⦂ A
  → e ~↑~ n
  → (n≤l : n ≤ length Γ)
  → Γ ↓ n [ n≤l ] ⊢d cc ╏ e ↓ n ⦂ A
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

⊢d-strengthen-0 : ∀ {Γ cc e A B}
  → Γ , A ⊢d cc ╏ e ↑ 0 ⦂ B
  → Γ ⊢d cc ╏ e ⦂ B
⊢d-strengthen-0 {e = e} ⊢e with ⊢d-strengthen ⊢e ↑-shifted z≤n
... | ind-e rewrite ↑-↓-id e 0 = ind-e

----------------------------------------------------------------------
--+                                                                +--
--+                       Check Subsumption                        +--
--+                                                                +--
----------------------------------------------------------------------
infix 6 _>>_
_>>_ : Context → Context → Context
Γ₁ >> ∅ = Γ₁
Γ₁ >> (Γ₂ , A) = (Γ₁ >> Γ₂) , A

narrow : ∀ {Γ₁ Γ₂ e A B C}
  → (Γ₁ , A) >> Γ₂ ⊢d ∞ ╏ e ⦂ B
  → C ≤d A
  → ∃[ D ] (((Γ₁ , C) >> Γ₂ ⊢d ∞ ╏ e ⦂ D) × (D ≤d B))
narrow {Γ₁} {Γ₂} (⊢d-lam₁ {A = A} ⊢e) C≤A with narrow {Γ₁} {Γ₂ , A} ⊢e C≤A
... | ⟨ D , ⟨ ⊢e' , D≤B ⟩ ⟩ = ⟨ A ⇒ D , ⟨ ⊢d-lam₁ ⊢e' , ≤d-arr ≤d-refl D≤B ⟩ ⟩
narrow {Γ₁} {Γ₂} (⊢d-lam₃ ⊢e) C≤A with narrow {Γ₁} {Γ₂ , Bot} ⊢e C≤A
... | ⟨ D , ⟨ ⊢e' , D≤B ⟩ ⟩ = ⟨ Bot ⇒ D , ⟨ (⊢d-lam₁ ⊢e') , ≤d-top ⟩ ⟩
narrow (⊢d-app₃ ⊢f ⊢e) C≤A = {!!}
narrow (⊢d-sub ⊢e x) C≤A = {!!}

narrow-var : ∀ {Γ₁ Γ₂ n A B C}
  → (Γ₁ , A) >> Γ₂ ∋ n ⦂ B
  → C ≤d A
  → ∃[ D ] (((Γ₁ , C) >> Γ₂ ∋ n ⦂ D) × (D ≤d B))
narrow-var {Γ₁} {∅} {C = C} Z C≤A = ⟨ C , ⟨ Z , C≤A ⟩ ⟩
narrow-var {Γ₁} {∅} {B = B} (S n∈Γ) C≤A = ⟨ B , ⟨ S n∈Γ , ≤d-refl ⟩ ⟩
narrow-var {Γ₁} {Γ₂ , E} Z C≤A = ⟨ E , ⟨ Z , ≤d-refl ⟩ ⟩
narrow-var {Γ₁} {Γ₂ , E} (S n∈Γ) C≤A with narrow-var {Γ₁} {Γ₂} n∈Γ C≤A
... | ⟨ D , ⟨ n∈Γ' , D≤B ⟩ ⟩ = ⟨ D , ⟨ S n∈Γ' , D≤B ⟩ ⟩

narrow-gen : ∀ {Γ₁ Γ₂ e A B C cc}
  → (Γ₁ , A) >> Γ₂ ⊢d cc ╏ e ⦂ B
  → C ≤d A
  → ∃[ D ] (((Γ₁ , C) >> Γ₂ ⊢d cc ╏ e ⦂ D) × (D ≤d B))
narrow-gen {Γ₁} {Γ₂} ⊢d-int C≤A = ⟨ Int , ⟨ ⊢d-int , ≤d-int ⟩ ⟩
narrow-gen {Γ₁} {Γ₂} (⊢d-var x∈Γ) C≤A with narrow-var x∈Γ C≤A
... | ⟨ D , ⟨ x∈Γ' , D≤B ⟩ ⟩ = ⟨ D , ⟨ ⊢d-var x∈Γ' , D≤B ⟩ ⟩
narrow-gen {Γ₁} {Γ₂} (⊢d-lam₁ ⊢e) C≤A = {!!}
narrow-gen {Γ₁} {Γ₂} (⊢d-lam₂ ⊢e) C≤A = {!!}
narrow-gen {Γ₁} {Γ₂} (⊢d-lam₃ ⊢e) C≤A = {!!}
narrow-gen {Γ₁} {Γ₂} (⊢d-app₁ ⊢e ⊢e₁) C≤A = {!!}
narrow-gen {Γ₁} {Γ₂} (⊢d-app₂ ⊢e ⊢e₁) C≤A = {!!}
narrow-gen {Γ₁} {Γ₂} (⊢d-app₃ ⊢e ⊢e₁) C≤A = {!!}
narrow-gen {Γ₁} {Γ₂} (⊢d-ann ⊢e) C≤A = {!!}
narrow-gen {Γ₁} {Γ₂} (⊢d-sub ⊢e A≤B) C≤A with narrow-gen ⊢e C≤A
... | ⟨ D , ⟨ ⊢e' , B≤D ⟩ ⟩ = ⟨ D , ⟨ (⊢d-sub ⊢e' ≤d-refl) , {!!} ⟩ ⟩

chk-sub : ∀ {Γ e A B}
  → Γ ⊢d ∞ ╏ e ⦂ A
  → A ≤d B
  → Γ ⊢d ∞ ╏ e ⦂ B
chk-sub (⊢d-lam₁ ⊢e) ≤d-top = ⊢d-lam₃ {!!}
chk-sub (⊢d-lam₁ ⊢e) (≤d-arr A≤B A≤B₁) = {!!}
chk-sub (⊢d-lam₃ ⊢e) A≤B = {!!}
chk-sub (⊢d-app₃ ⊢e ⊢e₁) A≤B = {!!}
chk-sub (⊢d-sub ⊢e x) A≤B = {!!}
