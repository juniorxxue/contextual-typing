module Record.Annotatability.Elaboration where

open import Record.Prelude
open import Record.Common
import Record.Decl as S
import Record.Annotatability.Target as T

∥_∥ : Term → T.Term
∥_∥r : Record → T.Record
∥ 𝕔 x ∥ = T.𝕔 x
∥ ` x ∥ = T.` x
∥ ƛ e ∥ = T.ƛ ∥ e ∥
∥ e · e₁ ∥ = ∥ e ∥ T.· ∥ e₁ ∥
∥ e ⦂ x ∥ = ∥ e ∥
∥ 𝕣 x ∥ = T.𝕣 ∥ x ∥r
∥ e 𝕡 x ∥ = ∥ e ∥ T.𝕡 x

∥ rnil ∥r = T.rnil
∥ r⟦ x ⦂ x₁ ↦ x₂ ⟧ rs ∥r = T.r⟦ x ↦ (∥ x₂ ∥) ⟧ (∥ rs ∥r)

need : T.Term → S.Counter
need (T.𝕔 x) = S.♭ S.Z
need (T.` x) = S.♭ S.Z
need (T.ƛ e) = S.S⇒ (need e)
need (e₁ T.· e₂) with need e₁
... | S.♭ S.Z = S.♭ S.Z
... | S.♭ S.∞ = S.♭ S.Z
... | S.♭ (S.S⇐ j) = S.♭ j
... | S.♭ (S.Sl j) = S.♭ S.Z
... | S.S⇒ r = r
need (T.𝕣 rs) = S.♭ S.Z
need (e T.𝕡 l) = S.♭ S.Z

data plusS⇒ : S.Counter → Set where

  plusS⇒-base :
    plusS⇒ (S.♭ S.Z)

  plusS-S⇒ : ∀ {i}
    → plusS⇒ i
    → plusS⇒ (S.S⇒ i)

data plusS⇒∞ : S.Counter → Set where

  plusS⇒-base∞ :
    plusS⇒∞ (S.♭ S.∞)

  plusS-S⇒∞ : ∀ {i}
    → plusS⇒∞ i
    → plusS⇒∞ (S.S⇒ i)

data plusS⇒∞A : S.Counter → Type → Set where

  plusS⇒-base∞A : ∀ {A}
    → plusS⇒∞A (S.♭ S.∞) A

  plusS-S⇒∞A : ∀ {i A B}
    → plusS⇒∞A i B
    → plusS⇒∞A (S.S⇒ i) (A ⇒ B)


req-plusS⇒ : ∀ e
  → plusS⇒ (need e)
req-plusS⇒ (T.𝕔 x) = plusS⇒-base
req-plusS⇒ (T.` x) = plusS⇒-base
req-plusS⇒ (T.ƛ e) = plusS-S⇒ (req-plusS⇒ e)
req-plusS⇒ (e₁ T.· e₂) with need e₁ | req-plusS⇒ e₁ 
... | S.♭ S.Z | IH = IH
... | S.S⇒ r | plusS-S⇒ IH = IH
req-plusS⇒ (T.𝕣 x) = plusS⇒-base
req-plusS⇒ (e T.𝕡 x) = plusS⇒-base

≤d-refl∞' : ∀ {i A}
  → plusS⇒∞A i A
  → A S.≤d i # A
≤d-refl∞' plusS⇒-base∞A = S.≤d-refl∞
≤d-refl∞' (plusS-S⇒∞A ps) = S.≤d-arr-S⇒ S.≤d-refl∞ (≤d-refl∞' ps)

plusS∞-¬Z : ∀ {i A}
  → plusS⇒∞A i A
  → i ≢ S.♭ S.Z
plusS∞-¬Z plusS⇒-base∞A = λ ()
plusS∞-¬Z (plusS-S⇒∞A ps) = λ ()

≤d-∞-z-plus : ∀ {i i' B A}
  → B S.≤d i # A
  → plusS⇒ i
  → plusS⇒∞A i' A
  → B S.≤d i' # A
≤d-∞-z-plus S.≤d-Z plusS⇒-base ps' = ≤d-refl∞' ps'
≤d-∞-z-plus (S.≤d-arr-S⇒ B≤A B≤A₁) (plusS-S⇒ ps) plusS⇒-base∞A = S.≤d-arr-∞ (≤d-∞-z-plus S.≤d-Z plusS⇒-base plusS⇒-base∞A)
                                                                  (≤d-∞-z-plus B≤A₁ ps plusS⇒-base∞A)
≤d-∞-z-plus (S.≤d-arr-S⇒ B≤A B≤A₁) (plusS-S⇒ ps) (plusS-S⇒∞A ps') = S.≤d-arr-S⇒ B≤A (≤d-∞-z-plus B≤A₁ ps ps')
≤d-∞-z-plus (S.≤d-and₁ B≤A x) ps ps' = S.≤d-and₁ (≤d-∞-z-plus B≤A ps ps') (plusS∞-¬Z ps')
≤d-∞-z-plus (S.≤d-and₂ B≤A x) ps ps' = S.≤d-and₂ (≤d-∞-z-plus B≤A ps ps') (plusS∞-¬Z ps')

⊢d-sub-∞'' : ∀ {Γ i e A i'}
  → Γ S.⊢d i # e ⦂ A
  → plusS⇒ i
  → plusS⇒∞A i' A
  → Γ S.⊢d i' # e ⦂ A
⊢d-sub-∞'' ⊢e plusS⇒-base plusS⇒-base∞A = S.⊢d-sub ⊢e S.≤d-refl∞ (λ ())
⊢d-sub-∞'' ⊢e plusS⇒-base (plusS-S⇒∞A ps') = S.⊢d-sub ⊢e (S.≤d-arr-S⇒ S.≤d-refl∞ (≤d-refl∞' ps')) λ ()
⊢d-sub-∞'' (S.⊢d-lam₂ ⊢e) (plusS-S⇒ ps) plusS⇒-base∞A = S.⊢d-lam₁ (⊢d-sub-∞'' ⊢e ps plusS⇒-base∞A)
⊢d-sub-∞'' (S.⊢d-lam₂ ⊢e) (plusS-S⇒ ps) (plusS-S⇒∞A ps') = S.⊢d-lam₂ (⊢d-sub-∞'' ⊢e ps ps')
⊢d-sub-∞'' (S.⊢d-app⇒ ⊢e ⊢e₁) (plusS-S⇒ ps) plusS⇒-base∞A = S.⊢d-app⇒ (⊢d-sub-∞'' ⊢e (plusS-S⇒ (plusS-S⇒ ps)) (plusS-S⇒∞A plusS⇒-base∞A)) ⊢e₁
⊢d-sub-∞'' (S.⊢d-app⇒ ⊢e ⊢e₁) (plusS-S⇒ ps) (plusS-S⇒∞A ps') = S.⊢d-app⇒ (⊢d-sub-∞'' ⊢e (plusS-S⇒ (plusS-S⇒ ps)) (plusS-S⇒∞A (plusS-S⇒∞A ps'))) ⊢e₁
⊢d-sub-∞'' (S.⊢d-sub ⊢e x x₁) (plusS-S⇒ ps) ps' = S.⊢d-sub ⊢e (≤d-∞-z-plus x (plusS-S⇒ ps) ps') (plusS∞-¬Z ps')

⊢d-sub-∞ : ∀ {Γ i e A}
  → Γ S.⊢d i # e ⦂ A
  → plusS⇒ i
  → Γ S.⊢d S.♭ S.∞ # e ⦂ A
⊢d-sub-∞ ⊢e ps = ⊢d-sub-∞'' ⊢e ps plusS⇒-base∞A

infix 3 _⊢_⦂_⟶_
infix 3 _⊢r_⦂_⟶_

data _⊢_⦂_⟶_ : Context → T.Term → Type → Term → Set
data _⊢r_⦂_⟶_ : Context → T.Record → Type → Record → Set

data _⊢_⦂_⟶_  where

  e-con : ∀ {Γ c}
    → Γ ⊢ (T.𝕔 c) ⦂ c-τ c ⟶ (𝕔 c)

  e-var : ∀ {Γ x A}
    → Γ ∋ x ⦂ A
    → Γ ⊢ (T.` x) ⦂ A ⟶ (` x)

  e-lam : ∀ {Γ e A B e'}
    → Γ , A ⊢ e ⦂ B ⟶ e'
    → Γ ⊢ T.ƛ e ⦂ A ⇒ B ⟶ (ƛ e')

  e-app1 : ∀ {Γ e₁ e₂ A B e₁' e₂'}
    → need e₁ ≡ S.♭ S.Z ⊎ need e₂ ≡ S.♭ S.Z
    → Γ ⊢ e₁ ⦂ A ⇒ B ⟶ e₁'
    → Γ ⊢ e₂ ⦂ A ⟶ e₂'
    → Γ ⊢ e₁ T.· e₂ ⦂ B ⟶ e₁' · e₂'

  e-app2 : ∀ {Γ e₁ e₂ A B e₁' e₂' i₁ i₂}
    → need e₂ ≡ S.S⇒ i₁
    → need e₁ ≡ S.S⇒ i₂
    → Γ ⊢ e₁ ⦂ A ⇒ B ⟶ e₁'
    → Γ ⊢ e₂ ⦂ A ⟶ e₂'
    → Γ ⊢ e₁ T.· e₂ ⦂ B ⟶ e₁' · (e₂' ⦂ A)

  e-rcd : ∀ {Γ rs rs' As}
    → Γ ⊢r rs ⦂ As ⟶ rs'
    → Γ ⊢ (T.𝕣 rs) ⦂ As ⟶ (𝕣 rs')

  e-prj : ∀ {Γ e e' l A}
    → Γ ⊢ e ⦂ τ⟦ l ↦ A ⟧ ⟶ e'
    → Γ ⊢ e T.𝕡 l ⦂ A ⟶ e' 𝕡 l

data _⊢r_⦂_⟶_ where

  e-rnil : ∀ {Γ}
    → Γ ⊢r T.rnil ⦂ Top ⟶ rnil

  e-one : ∀ {Γ e e' A l}
    → Γ ⊢ e ⦂ A ⟶ e'
    → Γ ⊢r T.r⟦ l ↦ e ⟧ T.rnil ⦂ τ⟦ l ↦ A ⟧  ⟶  r⟦ l ⦂ A ↦ e' ⟧ rnil

  e-cons : ∀ {Γ l e e' rs rs' A As}
    → Γ ⊢ e ⦂ A ⟶ e'
    → Γ ⊢r rs ⦂ As ⟶ rs'
    → Γ ⊢r T.r⟦ l ↦ e ⟧ rs ⦂ (τ⟦ l ↦ A ⟧ & As) ⟶ r⟦ l ⦂ A ↦ e' ⟧ rs'

{-
data _<<_ : S.Counter → S.Counter → Set where
  <<-base1 : (S.♭ S.Z) << (S.♭ (S.Sl S.Z))
  <<-base2 : (S.♭ S.Z) << (S.♭ (S.S⇐ S.Z))
  <<-base3 : (S.♭ S.Z) << (S.S⇒ (S.♭ S.Z))
  <<-cons : ∀ {n n'} → n << n' → n << (S.S⇒ n')
  
need-< : ∀ {Γ e A m n}
  → Γ S.⊢d m # e ⦂ A
--  → (need ∥ e ∥) << n
  → n << (need ∥ e ∥)
  → Γ S.⊢d n # e ⦂ A
need-< ⊢e <<n = {!!}  
-}

data notlabel : Type → Set where

     nl-int : notlabel Int
     nl-flt : notlabel Float
     nl-top : notlabel Top
--     nl-arr : ∀ {A B} → notlabel (A ⇒ B)
     nl-and : ∀ {A B} → notlabel (A & B)

data counterShape : S.Counter → Type → Set where

  cs-rcd : ∀ {l A}
    → counterShape (S.♭ S.Z) (τ⟦ l ↦ A ⟧)

  cs-rcd-S : ∀ {l A j}
    → counterShape (S.♭ j) A
    → counterShape (S.♭ (S.Sl j)) (τ⟦ l ↦ A ⟧)
    
  cs-rcd-∞ : ∀ {l A}
    → counterShape (S.♭ S.∞) (τ⟦ l ↦ A ⟧)

  cs-arr-Z : ∀ {A B}
    → counterShape (S.♭ S.Z) (A ⇒ B)

  cs-arr-S⇒ : ∀ {A B i}
    → counterShape i B
    → counterShape (S.S⇒ i) (A ⇒ B)

  cs-arr-S⇐ : ∀ {A B j}
    → counterShape (S.♭ j) B
    → counterShape (S.♭ (S.S⇐ j)) (A ⇒ B)
    
  cs-arr-∞ : ∀ {A B}
    → counterShape (S.♭ S.∞) (A ⇒ B)
  
  cs-other : ∀ {A i}
    → notlabel A
    → counterShape i A

cannonical-sub : ∀ {B A i}
  → B S.≤d i # A
  → counterShape i A
cannonical-sub {Int} S.≤d-Z = cs-other nl-int
cannonical-sub {Float} S.≤d-Z = cs-other nl-flt
cannonical-sub {Top} S.≤d-Z = cs-other nl-top
cannonical-sub {B ⇒ B₁} S.≤d-Z = cs-arr-Z
cannonical-sub {B & B₁} S.≤d-Z = cs-other nl-and
cannonical-sub {τ⟦ x ↦ B ⟧} S.≤d-Z = cs-rcd
cannonical-sub S.≤d-int∞ = cs-other nl-int
cannonical-sub S.≤d-float∞ = cs-other nl-flt
cannonical-sub S.≤d-top = cs-other nl-top
cannonical-sub (S.≤d-arr-∞ BA BA₁) = cs-arr-∞
cannonical-sub (S.≤d-rcd∞ BA) = cs-rcd-∞
cannonical-sub (S.≤d-arr-S⇐ BA BA₁) = cs-arr-S⇐ (cannonical-sub BA₁)
cannonical-sub (S.≤d-arr-S⇒ BA BA₁) = cs-arr-S⇒ (cannonical-sub BA₁)
cannonical-sub (S.≤d-rcd-Sl BA) = cs-rcd-S (cannonical-sub BA)
cannonical-sub (S.≤d-and₁ BA x) = cannonical-sub BA
cannonical-sub (S.≤d-and₂ BA x) = cannonical-sub BA
cannonical-sub (S.≤d-and BA BA₁) = cs-other nl-and


cannonical : ∀ {Γ i e A}
  → Γ S.⊢d i # e ⦂ A
  → counterShape i A
cannonical (S.⊢d-c {c = lit x}) = cs-other nl-int
cannonical (S.⊢d-c {c = flt x}) = cs-other nl-flt
cannonical (S.⊢d-c {c = +s}) = cs-other nl-and
cannonical (S.⊢d-c {c = +i x}) = cs-arr-Z
cannonical (S.⊢d-c {c = +f x}) = cs-arr-Z
cannonical {A = Int} (S.⊢d-var x) = cs-other nl-int
cannonical {A = Float} (S.⊢d-var x) = cs-other nl-flt
cannonical {A = Top} (S.⊢d-var x) = cs-other nl-top
cannonical {A = A ⇒ A₁} (S.⊢d-var x) = cs-arr-Z
cannonical {A = A & A₁} (S.⊢d-var x) = cs-other nl-and
cannonical {A = τ⟦ x₁ ↦ A ⟧} (S.⊢d-var x) = cs-rcd
cannonical {A = Int} (S.⊢d-ann ⊢e) = cs-other nl-int
cannonical {A = Float} (S.⊢d-ann ⊢e) = cs-other nl-flt
cannonical {A = Top} (S.⊢d-ann ⊢e) = cs-other nl-top
cannonical {A = A ⇒ A₁} (S.⊢d-ann ⊢e) = cs-arr-Z
cannonical {A = A & A₁} (S.⊢d-ann ⊢e) = cs-other nl-and
cannonical {A = τ⟦ x ↦ A ⟧} (S.⊢d-ann ⊢e) = cs-rcd
cannonical (S.⊢d-lam₁ ⊢e) = cs-arr-∞
cannonical (S.⊢d-lam₂ ⊢e) = cs-arr-S⇒ (cannonical ⊢e)
cannonical (S.⊢d-app⇐ ⊢e ⊢e₁) with cannonical ⊢e
... | cs-arr-S⇐ cs = cs
cannonical (S.⊢d-app⇒ ⊢e ⊢e₁) with cannonical ⊢e
... | cs-arr-S⇒ r = r
cannonical (S.⊢d-sub ⊢e x x₁) = cannonical-sub x
cannonical {A = Top} (S.⊢d-rcd x) = cs-other nl-top
cannonical {A = A & A₁} (S.⊢d-rcd x) = cs-other nl-and
cannonical {A = τ⟦ x₁ ↦ A ⟧} (S.⊢d-rcd x) = cs-rcd
cannonical (S.⊢d-prj ⊢e) with cannonical ⊢e
... | cs-rcd-S r = r

inv-label : ∀ {Γ i e l A}
  → Γ S.⊢d i # e ⦂ τ⟦ l ↦ A ⟧
  → plusS⇒ i
  → i ≡ S.♭ S.Z
inv-label ⊢e ps with cannonical ⊢e
... | cs-rcd = refl

annotatability : ∀ {Γ e A e'}
  → Γ ⊢ e ⦂ A ⟶ e'
  → Γ S.⊢d (need e) # e' ⦂ A

annotatability-r : ∀ {Γ rs As rs'}
  → Γ ⊢r rs ⦂ As ⟶ rs'
  → Γ S.⊢r S.♭ S.Z # rs' ⦂ As
annotatability-r e-rnil = S.⊢r-nil
annotatability-r (e-one {e = e} ⊢e) = S.⊢r-one (⊢d-sub-∞ (annotatability ⊢e) (req-plusS⇒ e))
annotatability-r (e-cons {e = e} ⊢e ⊢r) = S.⊢r-cons (⊢d-sub-∞ (annotatability ⊢e) (req-plusS⇒ e)) (annotatability-r ⊢r)

annotatability e-con = S.⊢d-c
annotatability (e-var x) = S.⊢d-var x
annotatability (e-lam ⊢e) = S.⊢d-lam₂ (annotatability ⊢e)
annotatability (e-app1 {e₁ = e₁} {e₂ = e₂} (inj₁ x) ⊢e₁ ⊢e₂) with need e₁ |  annotatability ⊢e₁
... | S.♭ S.Z | ⊢e₁' = S.⊢d-app⇐ (S.⊢d-sub ⊢e₁' (S.≤d-arr-S⇐ S.≤d-refl∞ S.≤d-Z) (λ ())) (⊢d-sub-∞ (annotatability ⊢e₂) (req-plusS⇒ e₂))
annotatability (e-app1 {e₁ = e₁} {e₂ = e₂} (inj₂ y) ⊢e₁ ⊢e₂) with need e₁
                                                                | req-plusS⇒ e₁
                                                                | need e₂
                                                                | req-plusS⇒ e₂
                                                                | annotatability ⊢e₁
                                                                | annotatability ⊢e₂
... | S.♭ S.Z | r1S | S.♭ S.Z | plusS⇒-base | ⊢e₁' | ⊢e₂' =
  S.⊢d-app⇐ (S.⊢d-sub ⊢e₁' (S.≤d-arr-S⇐ S.≤d-refl∞ S.≤d-Z) (λ ())) (S.⊢d-sub ⊢e₂' S.≤d-refl∞ (λ ()))
... | S.S⇒ r1 | r1S | S.♭ S.Z | plusS⇒-base | ⊢e₁' | ⊢e₂' = S.⊢d-app⇒ ⊢e₁' ⊢e₂'
annotatability (e-app2 {e₁ = e₁} {e₂ = e₂} eq1 eq2 ⊢e₁ ⊢e₂) with need e₁
                                                               | req-plusS⇒ e₁
                                                               | need e₂
                                                               | req-plusS⇒ e₂
                                                               | annotatability ⊢e₁
                                                               | annotatability ⊢e₂
... | S.S⇒ r1 | plusS-S⇒ r1S | S.S⇒ r2 | plusS-S⇒ r2S | ⊢e₁' | ⊢e₂' = S.⊢d-app⇒ ⊢e₁' (S.⊢d-ann (⊢d-sub-∞ ⊢e₂' (plusS-S⇒ r2S)))
annotatability (e-rcd x) = S.⊢d-rcd (annotatability-r x)
annotatability (e-prj {e = e} ⊢e) with need e | req-plusS⇒ e | annotatability ⊢e
annotatability (e-prj {e = e} ⊢e) | r | r⇒ | ⊢e' with inv-label ⊢e' r⇒
... | refl = S.⊢d-prj (S.⊢d-sub ⊢e' (S.≤d-rcd-Sl S.≤d-Z) (λ ()))



