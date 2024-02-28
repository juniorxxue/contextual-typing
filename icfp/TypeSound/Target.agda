module TypeSound.Target where

open import TypeSound.Common

infixr 5  ƛ_⇒_
infixl 7  _·_
infix  9  `_

data Record : Set
data Term : Set

data Term where
  lit      : ℕ → Term
  flt      : 𝔽 → Term
  `_       : Id → Term
  ƛ_⇒_     : Id → Term → Term
  _·_      : Term → Term → Term
  +        : Term
  +i       : ℕ → Term
  +f       : 𝔽 → Term
  𝕣_       : Record → Term
  _𝕡_      : Term → Label → Term

data Record where
  rnil : Record
  r⟦_↦_⟧_ : Label → Term → Record → Record

infix 4 _≤_

data _≤_ : Type → Type → Set where

  s-int :
      Int ≤ Int
  s-flt :
      Float ≤ Float
  s-arr : ∀ {A B C D}
    → C ≤ A
    → B ≤ D
    → A ⇒ B ≤ C ⇒ D
  s-top : ∀ {A}
    → A ≤ Top
  s-and-l : ∀ {A B C}
    → A ≤ C
    → A & B ≤ C
  s-and-r : ∀ {A B C}
    → B ≤ C
    → A & B ≤ C
  s-and : ∀ {A B C}
    → A ≤ B
    → A ≤ C
    → A ≤ B & C
  s-rcd : ∀ {l A B}
    → A ≤ B
    → τ⟦ l ↦ A ⟧ ≤ τ⟦ l ↦ B ⟧

s-refl : ∀ {A}
  → A ≤ A
s-refl {Top} = s-top
s-refl {Int} = s-int
s-refl {Float} = s-flt
s-refl {A ⇒ A₁} = s-arr s-refl s-refl
s-refl {A & A₁} = s-and (s-and-l s-refl) (s-and-r s-refl)
s-refl {τ⟦ x ↦ A ⟧} = s-rcd s-refl

inv-&-l : ∀ {A B C}
  → A ≤ B & C
  → A ≤ B
inv-&-r : ∀ {A B C}
  → A ≤ B & C
  → A ≤ C

inv-&-l (s-and-l A≤BC) = s-and-l (inv-&-l A≤BC)
inv-&-l (s-and-r A≤BC) = s-and-r (inv-&-l A≤BC)
inv-&-l (s-and A≤BC A≤BC₁) = A≤BC
inv-&-r (s-and-l A≤BC) = s-and-l (inv-&-r A≤BC)
inv-&-r (s-and-r A≤BC) = s-and-r (inv-&-r A≤BC)
inv-&-r (s-and A≤BC A≤BC₁) = A≤BC₁

≤-trans : ∀ {A B C}
  → A ≤ B
  → B ≤ C
  → A ≤ C
≤-trans {B = Top} A≤B s-top = A≤B
≤-trans {B = Top} A≤B (s-and B≤C B≤C₁) = s-and (≤-trans A≤B B≤C) (≤-trans A≤B B≤C₁)
≤-trans {Int} {Int} x x₁ = x₁
≤-trans {B = Int} (s-and-l A≤B) B≤C = s-and-l (≤-trans A≤B B≤C)
≤-trans {B = Int} (s-and-r A≤B) B≤C = s-and-r (≤-trans A≤B B≤C)
≤-trans {Float} {Float} x x₁ = x₁
≤-trans {B = Float} (s-and-l A≤B) B≤C = s-and-l (≤-trans A≤B B≤C)
≤-trans {B = Float} (s-and-r A≤B) B≤C = s-and-r (≤-trans A≤B B≤C)
≤-trans {B = B ⇒ B₁} (s-arr A≤B A≤B₁) (s-arr B≤C B≤C₁) = s-arr (≤-trans B≤C A≤B) (≤-trans A≤B₁ B≤C₁)
≤-trans {B = B ⇒ B₁} (s-arr A≤B A≤B₁) s-top = s-top
≤-trans {B = B ⇒ B₁} (s-arr A≤B A≤B₁) (s-and B≤C B≤C₁) = s-and (≤-trans (s-arr A≤B A≤B₁) B≤C)
                                                               (≤-trans (s-arr A≤B A≤B₁) B≤C₁)
≤-trans {B = B ⇒ B₁} (s-and-l A≤B) B≤C = s-and-l (≤-trans A≤B B≤C)
≤-trans {B = B ⇒ B₁} (s-and-r A≤B) B≤C = s-and-r (≤-trans A≤B B≤C)
≤-trans {B = B & B₁} A≤B s-top = s-top
≤-trans {B = B & B₁} A≤B (s-and-l B≤C) = ≤-trans (inv-&-l A≤B) B≤C
≤-trans {B = B & B₁} A≤B (s-and-r B≤C) = ≤-trans (inv-&-r A≤B) B≤C
≤-trans {B = B & B₁} A≤B (s-and B≤C B≤C₁) = s-and (≤-trans A≤B B≤C) (≤-trans A≤B B≤C₁)

≤-trans {B = τ⟦ x₁ ↦ B ⟧} x s-top = s-top
≤-trans {B = τ⟦ x₁ ↦ B ⟧} x (s-and x₂ x₃) = s-and (≤-trans x x₂) (≤-trans x x₃)
≤-trans {B = τ⟦ x₁ ↦ B ⟧} (s-and-l x) (s-rcd s) = s-and-l (≤-trans x (s-rcd s))
≤-trans {B = τ⟦ x₁ ↦ B ⟧} (s-and-r x) (s-rcd s) = s-and-r (≤-trans x (s-rcd s))
≤-trans {B = τ⟦ x₁ ↦ B ⟧} (s-rcd x) (s-rcd s) = s-rcd (≤-trans x s)

infix  4  _⊢_⦂_
infix  4  _⊢r_⦂_

data _⊢_⦂_ : Context → Term → Type → Set
data _⊢r_⦂_ : Context → Record → Type → Set

data _⊢_⦂_ where

  ⊢n : ∀ {Γ n}
    → Γ ⊢ (lit n) ⦂ Int

  ⊢m : ∀ {Γ m}
    → Γ ⊢ (flt m) ⦂ Float
    
  ⊢` : ∀ {Γ x A}
    → Γ ∋ x ⦂ A
      -----------
    → Γ ⊢ ` x ⦂ A
    
  ⊢ƛ : ∀ {Γ x N A B}
    → Γ , x ⦂ A ⊢ N ⦂ B
      -------------------
    → Γ ⊢ ƛ x ⇒ N ⦂ A ⇒ B
    
  ⊢· : ∀ {Γ L M A B}
    → Γ ⊢ L ⦂ A ⇒ B
    → Γ ⊢ M ⦂ A
      -------------
    → Γ ⊢ L · M ⦂ B

  ⊢& : ∀ {Γ M A B}
    → Γ ⊢ M ⦂ A
    → Γ ⊢ M ⦂ B
    → Γ ⊢ M ⦂ (A & B)

  ⊢+ : ∀ {Γ}
    → Γ ⊢ + ⦂ (Int ⇒ Int ⇒ Int) & (Float ⇒ Float ⇒ Float)

  ⊢+i : ∀ {Γ n}
    → Γ ⊢ (+i n) ⦂ Int ⇒ Int

  ⊢+f : ∀ {Γ m}
    → Γ ⊢ (+f m) ⦂ Float ⇒ Float

  ⊢rcd : ∀ {Γ rs As}
    → Γ ⊢r rs ⦂ As
    → Γ ⊢ (𝕣 rs) ⦂ As

  ⊢prj : ∀ {Γ e l A}
    → Γ ⊢ e ⦂ τ⟦ l ↦ A ⟧
    → Γ ⊢ e 𝕡 l ⦂ A

  ⊢sub : ∀ {Γ M A B}
    → Γ ⊢ M ⦂ A
    → A ≤ B
    → Γ ⊢ M ⦂ B

data _⊢r_⦂_ where

  ⊢r-nil : ∀ {Γ}
    → Γ ⊢r rnil ⦂ Top

  ⊢r-one : ∀ {Γ e A l}
    → Γ ⊢ e ⦂ A
    → Γ ⊢r r⟦ l ↦ e ⟧ rnil ⦂ τ⟦ l ↦ A ⟧

  ⊢r-cons : ∀ {Γ l e rs A As}
    → (⊢e : Γ ⊢ e ⦂ A)
    → Γ ⊢r rs ⦂ As
--    → (rs≢nil : rs ≢ rnil)
    → Γ ⊢r r⟦ l ↦ e ⟧ rs ⦂ (τ⟦ l ↦ A ⟧ & As)

infix 9 _[_:=_]

_[_:=_] : Term → Id → Term → Term
_[_:=_]r : Record → Id → Term → Record

(` x) [ y := V ] with x ≟ y
... | yes _         = V
... | no  _         = ` x
(ƛ x ⇒ e) [ y := V ] with x ≟ y
... | yes _         = ƛ x ⇒ e
... | no  _         = ƛ x ⇒ e [ y := V ]
(e₁ · e₂) [ y := V ]  = e₁ [ y := V ] · e₂ [ y := V ]
(lit n) [ y := V ]  = lit n
(flt m) [ y := V ]  = flt m
+ [ x := x₁ ] = +
+i n [ x := x₁ ] = +i n
+f m [ x := x₁ ] = +f m
(𝕣 rs) [ y := V ] = 𝕣 (rs [ y := V ]r)
(e 𝕡 l) [ y := V ] = (e [ y := V ]) 𝕡 l

rnil [ y := V ]r = rnil
(r⟦ l ↦ e ⟧ rs) [ y := V ]r = r⟦ l ↦ (e [ y := V ]) ⟧ (rs [ y := V ]r)

select : Record → Label → Maybe Term
select rnil l = nothing
select (r⟦ l₁ ↦ e ⟧ rs) l₂ with l₁ ≟n l₂
... | yes p = just e
... | no ¬p = select rs l₂

data Value : Term → Set
data ValueR : Record → Set

data ValueR where

  VR-0 : ValueR rnil
  VR-S : ∀ {v rs l}
    → Value v
    → ValueR rs
    → ValueR (r⟦ l ↦ v ⟧ rs)

data Value where

  V-n : ∀ {n}
    → Value (lit n)

  V-m : ∀ {m}
    → Value (flt m)

  V-ƛ : ∀ {x e}
    → Value (ƛ x ⇒ e)

  V-+ :
      Value (+)

  V-+i : ∀ {n}
    → Value (+i n)

  V-+f : ∀ {m}
    → Value (+f m)

  V-r : ∀ {rs}
    → ValueR rs
    → Value (𝕣 rs)

infix 4 _—→_

data _—→_ : Term → Term → Set
data _→r_ : Record → Record → Set

data _→r_ where

  rstep-1 : ∀ {e e' l rs}
    → e —→ e'
    → (r⟦ l ↦ e ⟧ rs) →r (r⟦ l ↦ e' ⟧ rs)

  rstep-2 : ∀ {v rs rs' l}
    → Value v
    → rs →r rs'
    → (r⟦ l ↦ v ⟧ rs) →r (r⟦ l ↦ v ⟧ rs')

data _—→_ where

  ξ-·₁ : ∀ {L L′ M}
    → L —→ L′
    → L · M —→ L′ · M

  ξ-·₂ : ∀ {V M M′}
    → Value V
    → M —→ M′
    → V · M —→ V · M′

  ξ-prj : ∀ {M M' l}
    → M —→ M'
    → (M 𝕡 l) —→  (M' 𝕡 l)

  ξ-rcd : ∀ {rs rs'}
    → rs →r rs'
    → (𝕣 rs) —→ (𝕣 rs')

  β-ƛ : ∀ {x N V}
    → Value V
    → (ƛ x ⇒ N) · V —→ N [ x := V ]

  β-+-i : ∀ {n}
    → + · (lit n) —→ +i n

  β-+-f : ∀ {m}
    → + · (flt m) —→ +f m

  β-+i : ∀ {n₁ n₂}
    → (+i n₁) · (lit n₂) —→ (lit (n₁ ++n n₂))

  β-+f : ∀ {m₁ m₂}
    → (+f m₁) · (flt m₂) —→ (flt (m₁ ++f m₂))

  β-prj : ∀ {rs l e}
    → ValueR rs
    → select rs l ≡ just e
    → (𝕣 rs) 𝕡 l —→ e

data Progress (M : Term) : Set where

  step : ∀ {N}
    → M —→ N
      ----------
    → Progress M

  done :
      Value M
      ----------
    → Progress M

elim-int : ∀ {Γ n A B C}
  → Γ ⊢ lit n ⦂ A
  → A ≤ B ⇒ C
  → ⊥
elim-int (⊢& ⊢e ⊢e₁) (s-and-l A≤B) = elim-int ⊢e A≤B
elim-int (⊢& ⊢e ⊢e₁) (s-and-r A≤B) = elim-int ⊢e₁ A≤B
elim-int (⊢sub ⊢e x) A≤B = elim-int ⊢e (≤-trans x A≤B)

elim-int' : ∀ {Γ n A B}
  → Γ ⊢ lit n ⦂ A ⇒ B
  → ⊥
elim-int' (⊢sub ⊢e x) = elim-int ⊢e x

elim-flt : ∀ {Γ n A B C}
  → Γ ⊢ flt n ⦂ A
  → A ≤ B ⇒ C
  → ⊥
elim-flt (⊢& ⊢e ⊢e₁) (s-and-l A≤B) = elim-flt ⊢e A≤B
elim-flt (⊢& ⊢e ⊢e₁) (s-and-r A≤B) = elim-flt ⊢e₁ A≤B
elim-flt (⊢sub ⊢e x) A≤B = elim-flt ⊢e (≤-trans x A≤B)

elim-flt' : ∀ {Γ n A B}
  → Γ ⊢ flt n ⦂ A ⇒ B
  → ⊥
elim-flt' (⊢sub ⊢e x) = elim-flt ⊢e x

elim-int-rcd : ∀ {Γ rs A}
  → Γ ⊢r rs ⦂ A
  → A ≤ Int
  → ⊥
elim-int-rcd (⊢r-cons x ⊢r) (s-and-r A≤Int) = elim-int-rcd ⊢r A≤Int

elim-flt-rcd : ∀ {Γ rs A}
  → Γ ⊢r rs ⦂ A
  → A ≤ Float
  → ⊥
elim-flt-rcd (⊢r-cons x ⊢r) (s-and-r A≤Flo) = elim-flt-rcd ⊢r A≤Flo

canonical-int : ∀ {Γ M A}
  → Γ ⊢ M ⦂ A
  → A ≤ Int
  → Value M
  → ∃[ n ](M ≡ lit n)
canonical-int {A = Int} (⊢n {n = n}) x₁ x₂ = ⟨ n , refl ⟩
canonical-int {A = Int} (⊢sub x x₃) x₁ x₂ = canonical-int x x₃ x₂
canonical-int (⊢& ⊢M ⊢M₁) (s-and-l A≤Int) VM = canonical-int ⊢M A≤Int VM
canonical-int (⊢sub ⊢M x) (s-and-l A≤Int) VM = canonical-int ⊢M (≤-trans (inv-&-l x) A≤Int) VM
canonical-int (⊢& ⊢M ⊢M₁) (s-and-r A≤Int) VM = canonical-int ⊢M₁ A≤Int VM
canonical-int (⊢sub ⊢M x) (s-and-r A≤Int) VM = canonical-int ⊢M (≤-trans (inv-&-r x) A≤Int) VM
canonical-int (⊢rcd ⊢r) (s-and-l A≤Int) VM = ⊥-elim (elim-int-rcd ⊢r (s-and-l A≤Int))
canonical-int (⊢rcd ⊢r) (s-and-r A≤Int) VM = ⊥-elim (elim-int-rcd ⊢r (s-and-r A≤Int))

canonical-flt : ∀ {Γ M A}
  → Γ ⊢ M ⦂ A
  → A ≤ Float
  → Value M
  → ∃[ m ](M ≡ flt m)
canonical-flt (⊢m {m = m}) s-flt VM = ⟨ m , refl ⟩
canonical-flt (⊢sub ⊢M x) s-flt VM = canonical-flt ⊢M x VM
canonical-flt (⊢& ⊢M ⊢M₁) (s-and-l A≤F) VM = canonical-flt ⊢M A≤F VM
canonical-flt (⊢sub ⊢M x) (s-and-l A≤F) VM = canonical-flt ⊢M (≤-trans (inv-&-l x) A≤F) VM
canonical-flt (⊢& ⊢M ⊢M₁) (s-and-r A≤F) VM = canonical-flt ⊢M₁ A≤F VM
canonical-flt (⊢sub ⊢M x) (s-and-r A≤F) VM = canonical-flt ⊢M (≤-trans (inv-&-r x) A≤F) VM
canonical-flt (⊢rcd x₁) (s-and-l x₂) x = ⊥-elim (elim-flt-rcd x₁ (s-and-l x₂))
canonical-flt (⊢rcd x₁) (s-and-r x₂) x = ⊥-elim (elim-flt-rcd x₁ (s-and-r x₂))

inv-arr-l : ∀ {A B C D}
  → A ⇒ B ≤ C ⇒ D
  → C ≤ A
inv-arr-r : ∀ {A B C D}
  → A ⇒ B ≤ C ⇒ D
  → B ≤ D
inv-arr-l (s-arr AB≤CD AB≤CD₁) = AB≤CD
inv-arr-r (s-arr AB≤CD AB≤CD₁) = AB≤CD₁

progress-+' : ∀ {M T A B}
  → ∅ ⊢ + ⦂ T
  → T ≤ A ⇒ B
  → ∅ ⊢ M ⦂ A
  → Value M
  → Progress (+ · M)
progress-+' (⊢& ⊢T ⊢T₁) (s-and-l T≤AB) ⊢M VM = progress-+' ⊢T T≤AB ⊢M VM
progress-+' (⊢& ⊢T ⊢T₁) (s-and-r T≤AB) ⊢M VM = progress-+' ⊢T₁ T≤AB ⊢M VM
progress-+' ⊢+ (s-and-l (s-arr T≤AB T≤AB₁)) ⊢M VM with canonical-int ⊢M T≤AB VM
... | ⟨ n , eq ⟩ rewrite eq = step β-+-i
progress-+' ⊢+ (s-and-r (s-arr T≤AB T≤AB₁)) ⊢M VM with canonical-flt ⊢M T≤AB VM
... | ⟨ m , eq ⟩ rewrite eq = step β-+-f
progress-+' (⊢sub ⊢T x) AB≤T ⊢M VM = progress-+' ⊢T (≤-trans x AB≤T) ⊢M VM

progress-+ : ∀ {M A B}
  → ∅ ⊢ + ⦂ A ⇒ B
  → ∅ ⊢ M ⦂ A
  → Value M
  → Progress (+ · M)
progress-+ (⊢sub ⊢N x) ⊢M VM = progress-+' ⊢N x ⊢M VM

progress-+i' : ∀ {T M A B n}
  → ∅ ⊢ +i n ⦂ T
  → T ≤ A ⇒ B
  → ∅ ⊢ M ⦂ A
  → Value M
  → Progress (+i n · M)
progress-+i' (⊢& ⊢T ⊢T₁) (s-and-l T≤A⇒B) ⊢M VM = progress-+i' ⊢T T≤A⇒B ⊢M VM
progress-+i' (⊢& ⊢T ⊢T₁) (s-and-r T≤A⇒B) ⊢M VM = progress-+i' ⊢T₁ T≤A⇒B ⊢M VM
progress-+i' ⊢+i (s-arr T≤A⇒B T≤A⇒B₁) ⊢M VM with canonical-int ⊢M T≤A⇒B VM
... | ⟨ n , eq ⟩ rewrite eq = step β-+i
progress-+i' (⊢sub ⊢T x) T≤A⇒B ⊢M VM = progress-+i' ⊢T (≤-trans x T≤A⇒B) ⊢M VM

progress-+i : ∀ {M A B n}
  → ∅ ⊢ +i n ⦂ A ⇒ B
  → ∅ ⊢ M ⦂ A
  → Value M
  → Progress (+i n · M)
progress-+i ⊢+i ⊢M VM with canonical-int ⊢M s-int VM
... | ⟨ n , eq ⟩ rewrite eq = step β-+i
progress-+i (⊢sub ⊢N x) ⊢M VM = progress-+i' ⊢N x ⊢M VM

progress-+f' : ∀ {T M A B n}
  → ∅ ⊢ +f n ⦂ T
  → T ≤ A ⇒ B
  → ∅ ⊢ M ⦂ A
  → Value M
  → Progress (+f n · M)
progress-+f' (⊢& ⊢T ⊢T₁) (s-and-l T≤A⇒B) ⊢M VM = progress-+f' ⊢T T≤A⇒B ⊢M VM
progress-+f' (⊢& ⊢T ⊢T₁) (s-and-r T≤A⇒B) ⊢M VM = progress-+f' ⊢T₁ T≤A⇒B ⊢M VM
progress-+f' ⊢+f (s-arr T≤A⇒B T≤A⇒B₁) ⊢M VM with canonical-flt ⊢M T≤A⇒B VM
... | ⟨ n , eq ⟩ rewrite eq = step β-+f
progress-+f' (⊢sub ⊢T x) T≤A⇒B ⊢M VM = progress-+f' ⊢T (≤-trans x T≤A⇒B) ⊢M VM

progress-+f : ∀ {M A B n}
  → ∅ ⊢ +f n ⦂ A ⇒ B
  → ∅ ⊢ M ⦂ A
  → Value M
  → Progress (+f n · M)
progress-+f ⊢+f ⊢M VM with canonical-flt ⊢M s-flt VM
... | ⟨ n , eq ⟩ rewrite eq = step β-+f
progress-+f (⊢sub ⊢N x) ⊢M VM = progress-+f' ⊢N x ⊢M VM

elim-rcd-arr-r : ∀ {Γ rs A B C}
  → Γ ⊢r rs ⦂ C
  → C ≤ A ⇒ B
  → ⊥
elim-rcd-arr-r (⊢r-cons x ⊢r) (s-and-r sub) = elim-rcd-arr-r ⊢r sub

elim-rcd-arr : ∀ {Γ rs A B C}
  → Γ ⊢ 𝕣 rs ⦂ C
  → C ≤ A ⇒ B
  → ⊥
elim-rcd-arr (⊢& ⊢r ⊢r₁) (s-and-l sub) = elim-rcd-arr ⊢r sub
elim-rcd-arr (⊢& ⊢r ⊢r₁) (s-and-r sub) = elim-rcd-arr ⊢r₁ sub
elim-rcd-arr (⊢rcd x) sub = elim-rcd-arr-r x sub
elim-rcd-arr (⊢sub ⊢r x) sub = elim-rcd-arr ⊢r (≤-trans x sub)


infix 3 _∉_

data _∉_ : Label → Record → Set where
  notin-empty : ∀ {l}
    → l ∉ rnil

  notin-cons : ∀ {l₁ l₂ rs e}
    → l₁ ≢ l₂
    → l₁ ∉ rs
    → l₁ ∉ r⟦ l₂ ↦ e ⟧ rs

data WFE : Term → Set 
data WFR : Record → Set

data WFE where
  wfe-n : ∀ {n} → WFE (lit n)
  wfe-m : ∀ {m} → WFE (flt m)
  wfe-+i : ∀ {m} → WFE (+i m)
  wfe-+f : ∀ {n} → WFE (+f n)
  wfe-+ : WFE +
  wfe-var : ∀ {x} → WFE (` x)
  wfe-lam : ∀ {x e} → WFE e → WFE (ƛ x ⇒ e)
  wfe-app : ∀ {e₁ e₂} → WFE e₁ → WFE e₂ → WFE (e₁ · e₂)
  wfe-rcd : ∀ {rs} → WFR rs → WFE (𝕣 rs)
  wfe-prj : ∀ {e l} → WFE e → WFE (e 𝕡 l)

data WFR where
  wfr-nil : WFR rnil
  wfr-cons : ∀ {e l rs}
    → WFE e
    → WFR rs
    → l ∉ rs
    → WFR (r⟦ l ↦ e ⟧ rs)

false-case : ∀ {l rs e}
  → l ∉ rs
  → select rs l ≡ just e
  → ⊥
false-case {l = l} (notin-cons {l₂ = l₂} x notin) eq with l₂ ≟n l
... | yes p = x (sym p)
... | no ¬p = false-case notin eq

select-v-r-wf : ∀ {rs A l A₁}
  → WFR rs
  → ValueR rs
  → ∅ ⊢r rs ⦂ A₁
  → A₁ ≤ τ⟦ l ↦ A ⟧
  → ∃[ e ](select rs l ≡ just e × (∅ ⊢ e ⦂ A))
select-v-r-wf {l = l} wfr vr (⊢r-one {e = e} x) (s-rcd s) with l ≟n l
... | yes p = ⟨ e , ⟨ refl , ⊢sub x s ⟩ ⟩
... | no ¬p = ⊥-elim (¬p refl)
select-v-r-wf {l = l} wfr (VR-S x vr) (⊢r-cons {e = e} ⊢e ⊢r) (s-and-l (s-rcd s)) with l ≟n l
... | yes p = ⟨ e , ⟨ refl , ⊢sub ⊢e s ⟩ ⟩
... | no ¬p = ⊥-elim (¬p refl)
select-v-r-wf {l = l} (wfr-cons x wfr x₁) (VR-S {v = v} x₂ vr) (⊢r-cons {l = l'} ⊢e ⊢r) (s-and-r s) with select-v-r-wf wfr vr ⊢r s
select-v-r-wf {l = l} (wfr-cons x wfr x₁) (VR-S {v = v} x₂ vr) (⊢r-cons {l = l'} ⊢e ⊢r) (s-and-r s) | ⟨ e , ⟨ eq , ⊢e' ⟩ ⟩ with l' ≟n l
... | yes p rewrite p = ⊥-elim (false-case x₁ eq)
... | no ¬p = ⟨ e , ⟨ eq , ⊢e' ⟩ ⟩

select-value' : ∀ {rs l A A₁}
  → WFR rs
  → ValueR rs
  → ∅ ⊢ 𝕣 rs ⦂ A₁
  → A₁ ≤ τ⟦ l ↦ A ⟧
  → ∃[ e ](select rs l ≡ just e × (∅ ⊢ e ⦂ A))
select-value' wfr vr (⊢& ⊢e ⊢e₁) (s-and-l s) = select-value' wfr vr ⊢e s
select-value' wfr vr (⊢& ⊢e ⊢e₁) (s-and-r s) = select-value' wfr vr ⊢e₁ s
select-value' wfr vr (⊢rcd x) s = select-v-r-wf wfr vr x s
select-value' wfr vr (⊢sub ⊢e x) s = select-value' wfr vr ⊢e (≤-trans x s)

select-value : ∀ {rs l A}
  → WFR rs
  → ValueR rs
  → ∅ ⊢ 𝕣 rs ⦂ τ⟦ l ↦ A ⟧
  → ∃[ e ](select rs l ≡ just e × (∅ ⊢ e ⦂ A))
select-value {l = l} wfr vr (⊢rcd (⊢r-one {e = e} {l = l} x)) with l ≟n l
... | yes p = ⟨ e , ⟨ refl , x ⟩ ⟩
... | no ¬p = ⊥-elim (¬p refl)
select-value wfr vr (⊢sub ⊢e x) = select-value' wfr vr ⊢e x


-- inversion cases
inv-n-rcd : ∀ {n l A B}
  → ∅ ⊢ lit n ⦂ A
  → A ≤ τ⟦ l ↦ B ⟧
  → ⊥
inv-n-rcd (⊢& ⊢e ⊢e₁) (s-and-l s) = inv-n-rcd ⊢e s
inv-n-rcd (⊢& ⊢e ⊢e₁) (s-and-r s) = inv-n-rcd ⊢e₁ s
inv-n-rcd (⊢sub ⊢e x) s = inv-n-rcd ⊢e (≤-trans x s)

inv-m-rcd : ∀ {m l A B}
  → ∅ ⊢ flt m ⦂ A
  → A ≤ τ⟦ l ↦ B ⟧
  → ⊥
inv-m-rcd (⊢& ⊢e ⊢e₁) (s-and-l s) = inv-m-rcd ⊢e s
inv-m-rcd (⊢& ⊢e ⊢e₁) (s-and-r s) = inv-m-rcd ⊢e₁ s
inv-m-rcd (⊢sub ⊢e x) s = inv-m-rcd ⊢e (≤-trans x s)

inv-lam-rcd : ∀ {x e l A B}
  → ∅ ⊢ ƛ x ⇒ e ⦂ A
  → A ≤ τ⟦ l ↦ B ⟧
  → ⊥
inv-lam-rcd (⊢& ⊢e ⊢e₁) (s-and-l s) = inv-lam-rcd ⊢e s
inv-lam-rcd (⊢& ⊢e ⊢e₁) (s-and-r s) = inv-lam-rcd ⊢e₁ s
inv-lam-rcd (⊢sub ⊢e x) s = inv-lam-rcd ⊢e (≤-trans x s)

inv-+-rcd : ∀ {l A B}
  → ∅ ⊢ + ⦂ A
  → A ≤ τ⟦ l ↦ B ⟧
  → ⊥
inv-+-rcd (⊢& ⊢e ⊢e₁) (s-and-l s) = inv-+-rcd ⊢e s
inv-+-rcd (⊢& ⊢e ⊢e₁) (s-and-r s) = inv-+-rcd ⊢e₁ s
inv-+-rcd ⊢+ (s-and-l ())
inv-+-rcd ⊢+ (s-and-r ())
inv-+-rcd (⊢sub ⊢e x) s = inv-+-rcd ⊢e (≤-trans x s)

inv-+i-rcd : ∀ {l n A B}
  → ∅ ⊢ +i n ⦂ A
  → A ≤ τ⟦ l ↦ B ⟧
  → ⊥
inv-+i-rcd (⊢& ⊢e ⊢e₁) (s-and-l s) = inv-+i-rcd ⊢e s
inv-+i-rcd (⊢& ⊢e ⊢e₁) (s-and-r s) = inv-+i-rcd ⊢e₁ s
inv-+i-rcd (⊢sub ⊢e x) s = inv-+i-rcd ⊢e (≤-trans x s)

inv-+f-rcd : ∀ {l n A B}
  → ∅ ⊢ +f n ⦂ A
  → A ≤ τ⟦ l ↦ B ⟧
  → ⊥
inv-+f-rcd (⊢& ⊢e ⊢e₁) (s-and-l s) = inv-+f-rcd ⊢e s
inv-+f-rcd (⊢& ⊢e ⊢e₁) (s-and-r s) = inv-+f-rcd ⊢e₁ s
inv-+f-rcd (⊢sub ⊢e x) s = inv-+f-rcd ⊢e (≤-trans x s)

wfr-inv : ∀ {rs}
  → WFE (𝕣 rs)
  → WFR rs
wfr-inv (wfe-rcd x) = x

progress : ∀ {e A}
  → WFE e
  → ∅ ⊢ e ⦂ A
  → Progress e

progress-r : ∀ {rs A}
  → WFR rs
  → ∅ ⊢r rs ⦂ A
  → Progress (𝕣 rs)

progress-r wfe ⊢r-nil = done (V-r VR-0)
progress-r (wfr-cons wfe wfr l∉) (⊢r-one ⊢e) with progress wfe ⊢e
... | step x = step (ξ-rcd (rstep-1 x))
... | done x = done (V-r (VR-S x VR-0))
progress-r (wfr-cons wfe wfr l∉) (⊢r-cons ⊢e ⊢r ) with progress wfe ⊢e | progress-r wfr ⊢r
... | step x | p2 = step (ξ-rcd (rstep-1 x))
... | done x | step (ξ-rcd x₁) = step (ξ-rcd (rstep-2 x x₁))
... | done x | done (V-r x₁) = done (V-r (VR-S x x₁))

progress wfe ⊢n = done V-n
progress wfe ⊢m = done V-m
progress wfe (⊢ƛ ⊢e) = done V-ƛ
progress (wfe-app wfe1 wfe2) (⊢· ⊢e₁ ⊢e₂) with progress wfe1 ⊢e₁ | progress wfe2 ⊢e₂
... | step s₁ | _ = step (ξ-·₁ s₁)
... | done v₁ | step s₂ = step (ξ-·₂ v₁ s₂)
... | done V-n | done v₂ = ⊥-elim (elim-int' ⊢e₁)
... | done V-m | done v₂ = ⊥-elim (elim-flt' ⊢e₁)
... | done V-ƛ | done v₂ = step (β-ƛ v₂)
... | done V-+ | done v₂ = progress-+ ⊢e₁ ⊢e₂ v₂
... | done V-+i | done v₂ = progress-+i ⊢e₁ ⊢e₂ v₂
... | done V-+f | done v₂ = progress-+f ⊢e₁ ⊢e₂ v₂
... | done (V-r vr) | done v₂ = ⊥-elim (elim-rcd-arr ⊢e₁ s-refl)
progress wfe (⊢& ⊢e ⊢e₁) = progress wfe ⊢e
progress wfe ⊢+ = done V-+
progress wfe ⊢+i = done V-+i
progress wfe ⊢+f = done V-+f
progress wfe (⊢sub ⊢e x) = progress wfe ⊢e
progress (wfe-rcd x) (⊢rcd ⊢r) = progress-r x ⊢r
progress (wfe-prj wfe) (⊢prj ⊢e) with progress wfe ⊢e
... | step x = step (ξ-prj x)
... | done V-n = ⊥-elim (inv-n-rcd ⊢e s-refl)
... | done V-m = ⊥-elim (inv-m-rcd ⊢e s-refl)
... | done V-ƛ = ⊥-elim (inv-lam-rcd ⊢e s-refl)
... | done V-+ = ⊥-elim (inv-+-rcd ⊢e s-refl)
... | done V-+i = ⊥-elim (inv-+i-rcd ⊢e s-refl)
... | done V-+f = ⊥-elim (inv-+f-rcd ⊢e s-refl)
... | done (V-r x) = let ⟨ e , ⟨ eq , ⊢e ⟩ ⟩ = select-value (wfr-inv wfe) x ⊢e
                     in step (β-prj x eq)                       



ext : ∀ {Γ Δ}
  → (∀ {x A}     →         Γ ∋ x ⦂ A →         Δ ∋ x ⦂ A)
    -----------------------------------------------------
  → (∀ {x y A B} → Γ , y ⦂ B ∋ x ⦂ A → Δ , y ⦂ B ∋ x ⦂ A)
ext ρ Z           =  Z
ext ρ (S x≢y ∋x)  =  S x≢y (ρ ∋x)

rename : ∀ {Γ Δ}
  → (∀ {x A} → Γ ∋ x ⦂ A → Δ ∋ x ⦂ A)
    ----------------------------------
  → (∀ {M A} → Γ ⊢ M ⦂ A → Δ ⊢ M ⦂ A)

rename-r : ∀ {Γ Δ}
  → (∀ {x A} → Γ ∋ x ⦂ A → Δ ∋ x ⦂ A)
    ----------------------------------
  → (∀ {M A} → Γ ⊢r M ⦂ A → Δ ⊢r M ⦂ A)

rename-r ρ ⊢r-nil = ⊢r-nil
rename-r ρ (⊢r-one x) = ⊢r-one (rename ρ x)
rename-r ρ (⊢r-cons ⊢e ⊢r) = ⊢r-cons (rename ρ ⊢e) (rename-r ρ ⊢r)

rename ρ ⊢n = ⊢n
rename ρ ⊢m = ⊢m
rename ρ (⊢` ∋w)    =  ⊢` (ρ ∋w)
rename ρ (⊢ƛ ⊢N)    =  ⊢ƛ (rename (ext ρ) ⊢N)
rename ρ (⊢· ⊢L ⊢M) =  ⊢· (rename ρ ⊢L) (rename ρ ⊢M)
rename ρ (⊢& ⊢L ⊢M) =  ⊢& (rename ρ ⊢L) (rename ρ ⊢M)
rename ρ (⊢sub ⊢L s) = ⊢sub (rename ρ ⊢L) s
rename ρ ⊢+ = ⊢+
rename ρ ⊢+i = ⊢+i
rename ρ ⊢+f = ⊢+f
rename ρ (⊢rcd ⊢r) = ⊢rcd (rename-r ρ ⊢r)
rename ρ (⊢prj ⊢e) = ⊢prj (rename ρ ⊢e)

weaken : ∀ {Γ M A}
  → ∅ ⊢ M ⦂ A
    ----------
  → Γ ⊢ M ⦂ A
weaken {Γ} ⊢M = rename ρ ⊢M
  where
  ρ : ∀ {z C}
    → ∅ ∋ z ⦂ C
      ---------
    → Γ ∋ z ⦂ C
  ρ ()

drop : ∀ {Γ x M A B C}
  → Γ , x ⦂ A , x ⦂ B ⊢ M ⦂ C
    --------------------------
  → Γ , x ⦂ B ⊢ M ⦂ C
drop {Γ} {x} {M} {A} {B} {C} ⊢M = rename ρ ⊢M
  where
  ρ : ∀ {z C}
    → Γ , x ⦂ A , x ⦂ B ∋ z ⦂ C
      -------------------------
    → Γ , x ⦂ B ∋ z ⦂ C
  ρ Z                 =  Z
  ρ (S x≢x Z)         =  ⊥-elim (x≢x refl)
  ρ (S z≢x (S _ ∋z))  =  S z≢x ∋z

swap : ∀ {Γ x y M A B C}
  → x ≢ y
  → Γ , y ⦂ B , x ⦂ A ⊢ M ⦂ C
    --------------------------
  → Γ , x ⦂ A , y ⦂ B ⊢ M ⦂ C
swap {Γ} {x} {y} {M} {A} {B} {C} x≢y ⊢M = rename ρ ⊢M
  where
  ρ : ∀ {z C}
    → Γ , y ⦂ B , x ⦂ A ∋ z ⦂ C
      --------------------------
    → Γ , x ⦂ A , y ⦂ B ∋ z ⦂ C
  ρ Z                   =  S x≢y Z
  ρ (S z≢x Z)           =  Z
  ρ (S z≢x (S z≢y ∋z))  =  S z≢y (S z≢x ∋z)

subst : ∀ {Γ x N V A B}
  → ∅ ⊢ V ⦂ A
  → Γ , x ⦂ A ⊢ N ⦂ B
    --------------------
  → Γ ⊢ N [ x := V ] ⦂ B

subst-r : ∀ {Γ x N V A B}
  → ∅ ⊢ V ⦂ A
  → Γ , x ⦂ A ⊢r N ⦂ B
  → Γ ⊢r N [ x := V ]r ⦂ B
subst-r {x = y} ⊢V ⊢r-nil = ⊢r-nil
subst-r {x = y} ⊢V (⊢r-one ⊢e) = ⊢r-one (subst ⊢V ⊢e)
subst-r {x = y} ⊢V (⊢r-cons ⊢e ⊢r) = ⊢r-cons (subst ⊢V ⊢e) (subst-r ⊢V ⊢r)

subst {x = y} ⊢V ⊢n = ⊢n
subst {x = y} ⊢V ⊢m = ⊢m
subst {x = y} ⊢V (⊢` {x = x} Z) with x ≟ y
... | yes _         =  weaken ⊢V
... | no  x≢y       =  ⊥-elim (x≢y refl)
subst {x = y} ⊢V (⊢` {x = x} (S x≢y ∋x)) with x ≟ y
... | yes refl      =  ⊥-elim (x≢y refl)
... | no  _         =  ⊢` ∋x
subst {x = y} ⊢V (⊢ƛ {x = x} ⊢N) with x ≟ y
... | yes refl      =  ⊢ƛ (drop ⊢N)
... | no  x≢y       =  ⊢ƛ (subst ⊢V (swap x≢y ⊢N))
subst ⊢V (⊢· ⊢L ⊢M) = ⊢· (subst ⊢V ⊢L) (subst ⊢V ⊢M)
subst ⊢V (⊢& ⊢L ⊢M) = ⊢& (subst ⊢V ⊢L) (subst ⊢V ⊢M)
subst ⊢V (⊢sub ⊢L s) = ⊢sub (subst ⊢V ⊢L) s
subst ⊢V ⊢+ = ⊢+
subst ⊢V ⊢+i = ⊢+i
subst ⊢V ⊢+f = ⊢+f
subst ⊢V (⊢rcd ⊢r) = ⊢rcd (subst-r ⊢V ⊢r)
subst ⊢V (⊢prj ⊢e) = ⊢prj (subst ⊢V ⊢e)



inv-lam' : ∀ {Γ x e A B T}
  → Γ ⊢ ƛ x ⇒ e ⦂ T
  → T ≤ A ⇒ B
  → ∃[ A' ]( ∃[ B' ] ((Γ , x ⦂ A' ⊢ e ⦂ B') × (A ≤ A') × (B' ≤ B)))
inv-lam' (⊢ƛ {A = A} {B} ⊢e) (s-arr T≤AB T≤AB₁) = ⟨ A , ⟨ B , ⟨ ⊢e , ⟨ T≤AB , T≤AB₁ ⟩ ⟩ ⟩ ⟩
inv-lam' (⊢sub ⊢e x) (s-arr T≤AB T≤AB₁) = inv-lam' ⊢e (≤-trans x (s-arr T≤AB T≤AB₁))
inv-lam' (⊢& ⊢e ⊢e₁) (s-and-l T≤AB) = inv-lam' ⊢e T≤AB
inv-lam' (⊢sub ⊢e x) (s-and-l T≤AB) = inv-lam' ⊢e (≤-trans (inv-&-l x) T≤AB)
inv-lam' (⊢& ⊢e ⊢e₁) (s-and-r T≤AB) = inv-lam' ⊢e₁ T≤AB
inv-lam' (⊢sub ⊢e x) (s-and-r T≤AB) = inv-lam' ⊢e (≤-trans (inv-&-r x) T≤AB)

inv-lam : ∀ {Γ x e A B}
  → Γ ⊢ ƛ x ⇒ e ⦂ A ⇒ B
  → ∃[ A' ]( ∃[ B' ] ((Γ , x ⦂ A' ⊢ e ⦂ B') × (A ≤ A') × (B' ≤ B)))
inv-lam {A = A} {B = B} (⊢ƛ ⊢e) = ⟨ A , ⟨ B , ⟨ ⊢e , ⟨ s-refl , s-refl ⟩ ⟩ ⟩ ⟩
inv-lam {A = A} {B = B} (⊢sub ⊢e x) = inv-lam' ⊢e x

inv-int : ∀ {Γ n A}
  → Γ ⊢ lit n ⦂ A
  → Int ≤ A
inv-int ⊢n = s-refl
inv-int (⊢& ⊢e ⊢e₁) = s-and (inv-int ⊢e) (inv-int ⊢e₁)
inv-int (⊢sub ⊢e x) = ≤-trans (inv-int ⊢e) x

inv-flt : ∀ {Γ m A}
  → Γ ⊢ flt m ⦂ A
  → Float ≤ A
inv-flt ⊢m = s-flt
inv-flt (⊢& ⊢M ⊢M₁) = s-and (inv-flt ⊢M) (inv-flt ⊢M₁)
inv-flt (⊢sub ⊢M x) = ≤-trans (inv-flt ⊢M) x

¬Int≤Float : Int ≤ Float → ⊥
¬Int≤Float ()

¬Float≤Int : Float ≤ Int → ⊥
¬Float≤Int ()

inv-+-i+' : ∀ {Γ T A B}
  → Γ ⊢ + ⦂ T
  → T ≤ A ⇒ B
  → Int ≤ A
  → Int ⇒ Int ≤ B
inv-+-i+' (⊢& ⊢T ⊢T₁) (s-and-l T≤AB) Int≤A = inv-+-i+' ⊢T T≤AB Int≤A
inv-+-i+' (⊢& ⊢T ⊢T₁) (s-and-r T≤AB) Int≤A = inv-+-i+' ⊢T₁ T≤AB Int≤A
inv-+-i+' ⊢+ (s-and-l (s-arr T≤AB T≤AB₁)) Int≤A = T≤AB₁
inv-+-i+' ⊢+ (s-and-r (s-arr T≤AB T≤AB₁)) Int≤A = ⊥-elim (¬Int≤Float (≤-trans Int≤A T≤AB))
inv-+-i+' (⊢sub ⊢T x) T≤AB Int≤A = inv-+-i+' ⊢T (≤-trans x T≤AB) Int≤A

inv-+-i+ : ∀ {Γ A B}
  → Γ ⊢ + ⦂ A ⇒ B
  → Int ≤ A
  → Int ⇒ Int ≤ B
inv-+-i+ (⊢sub ⊢M x) Int≤A = inv-+-i+' ⊢M x Int≤A

inv-+-f+' : ∀ {Γ T A B}
  → Γ ⊢ + ⦂ T
  → T ≤ A ⇒ B
  → Float ≤ A
  → Float ⇒ Float ≤ B
inv-+-f+' (⊢& ⊢T ⊢T₁) (s-and-l T≤AB) Int≤A = inv-+-f+' ⊢T T≤AB Int≤A
inv-+-f+' (⊢& ⊢T ⊢T₁) (s-and-r T≤AB) Int≤A = inv-+-f+' ⊢T₁ T≤AB Int≤A
inv-+-f+' ⊢+ (s-and-l (s-arr T≤AB T≤AB₁)) Int≤A = ⊥-elim (¬Float≤Int (≤-trans Int≤A T≤AB))
inv-+-f+' ⊢+ (s-and-r (s-arr T≤AB T≤AB₁)) Int≤A = T≤AB₁
inv-+-f+' (⊢sub ⊢T x) T≤AB Int≤A = inv-+-f+' ⊢T (≤-trans x T≤AB) Int≤A

inv-+-f+ : ∀ {Γ A B}
  → Γ ⊢ + ⦂ A ⇒ B
  → Float ≤ A
  → Float ⇒ Float ≤ B
inv-+-f+ (⊢sub ⊢M x) Int≤A = inv-+-f+' ⊢M x Int≤A

inv-+i' : ∀ {n A B T}
  → ∅ ⊢ +i n ⦂ T
  → T ≤ A ⇒ B
  → Int ≤ B
inv-+i' (⊢& ⊢M ⊢M₁) (s-and-l T≤AB) = inv-+i' ⊢M T≤AB
inv-+i' (⊢& ⊢M ⊢M₁) (s-and-r T≤AB) = inv-+i' ⊢M₁ T≤AB
inv-+i' ⊢+i (s-arr T≤AB T≤AB₁) = T≤AB₁
inv-+i' (⊢sub ⊢M x) T≤AB = inv-+i' ⊢M (≤-trans x T≤AB)

inv-+i : ∀ {n A B}
  → ∅ ⊢ +i n ⦂ A ⇒ B
  → Int ≤ B
inv-+i ⊢+i = s-int
inv-+i (⊢sub ⊢e x) = inv-+i' ⊢e x

inv-+f' : ∀ {m A B T}
  → ∅ ⊢ +f m ⦂ T
  → T ≤ A ⇒ B
  → Float ≤ B
inv-+f' (⊢& ⊢M ⊢M₁) (s-and-l T≤AB) = inv-+f' ⊢M T≤AB
inv-+f' (⊢& ⊢M ⊢M₁) (s-and-r T≤AB) = inv-+f' ⊢M₁ T≤AB
inv-+f' ⊢+f (s-arr T≤AB T≤AB₁) = T≤AB₁
inv-+f' (⊢sub ⊢M x) T≤AB = inv-+f' ⊢M (≤-trans x T≤AB)

inv-+f : ∀ {m A B}
  → ∅ ⊢ +f m ⦂ A ⇒ B
  → Float ≤ B
inv-+f ⊢+f = s-flt
inv-+f (⊢sub ⊢M x) = inv-+f' ⊢M x

rw-case : ∀ {e N A}
  → just e ≡ just N
  → ∅ ⊢ e ⦂ A
  → ∅ ⊢ N ⦂ A
rw-case refl ⊢e = ⊢e
  

preserve : ∀ {M N A}
  → WFE M
  → ∅ ⊢ M ⦂ A
  → M —→ N
    ----------
  → ∅ ⊢ N ⦂ A

preserve-r : ∀ {rs rs' A}
  → WFR rs
  → ∅ ⊢r rs ⦂ A
  → rs →r rs'
    ----------
  → ∅ ⊢r rs' ⦂ A
preserve-r (wfr-cons x₂ wfr x₃) (⊢r-one x) (rstep-1 x₁) = ⊢r-one (preserve x₂ x x₁)
preserve-r (wfr-cons x₁ wfr x₂) (⊢r-cons ⊢e ⊢r) (rstep-1 x) = ⊢r-cons (preserve x₁ ⊢e x) ⊢r
preserve-r (wfr-cons x₁ wfr x₂) (⊢r-cons ⊢e ⊢r) (rstep-2 x st) = ⊢r-cons ⊢e (preserve-r wfr ⊢r st)
  
preserve (wfe-app wfe wfe₁) (⊢· ⊢e ⊢e₁) (ξ-·₁ M→N) = ⊢· (preserve wfe ⊢e M→N) ⊢e₁
preserve (wfe-app wfe wfe₁) (⊢· ⊢e ⊢e₁) (ξ-·₂ x M→N) = ⊢· ⊢e (preserve wfe₁ ⊢e₁ M→N)
preserve wfe (⊢· ⊢e ⊢e₁) (β-ƛ x) with inv-lam ⊢e
... | ⟨ A' , ⟨ B' , ⟨ ⊢e' , ⟨ A≤A' , B'≤B ⟩ ⟩ ⟩ ⟩ = subst (⊢sub ⊢e₁ A≤A') (⊢sub ⊢e' B'≤B)
preserve wfe (⊢· ⊢e ⊢e₁) β-+-i = ⊢sub ⊢+i (inv-+-i+ ⊢e (inv-int ⊢e₁))
preserve wfe (⊢· ⊢e ⊢e₁) β-+-f = ⊢sub ⊢+f (inv-+-f+ ⊢e (inv-flt ⊢e₁))
preserve wfe (⊢· ⊢e ⊢e₁) β-+i = ⊢sub ⊢n (inv-+i ⊢e)
preserve wfe (⊢· ⊢e ⊢e₁) β-+f = ⊢sub ⊢m (inv-+f ⊢e)
preserve wfe (⊢& ⊢e ⊢e₁) M→N = ⊢& (preserve wfe ⊢e M→N) (preserve wfe ⊢e₁ M→N)
preserve wfe (⊢sub ⊢e x) M→N = ⊢sub (preserve wfe ⊢e M→N) x
preserve (wfe-prj wfe) (⊢prj ⊢e) (ξ-prj M→N) = ⊢prj (preserve wfe ⊢e M→N)
preserve (wfe-prj (wfe-rcd wfr)) (⊢prj ⊢e) (β-prj vr eq) with select-value wfr vr ⊢e
preserve (wfe-prj (wfe-rcd wfr)) (⊢prj ⊢e) (β-prj vr eq) | ⟨ e , ⟨ eq' , ⊢e' ⟩ ⟩ rewrite eq' = rw-case eq ⊢e'
preserve (wfe-rcd x) (⊢rcd ⊢r) (ξ-rcd x₁) = ⊢rcd (preserve-r x ⊢r x₁)
