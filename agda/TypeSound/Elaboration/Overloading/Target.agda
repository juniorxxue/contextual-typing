
module TypeSound.Elaboration.Overloading.Target where

open import TypeSound.Elaboration.Overloading.Common

infixr 5  ƛ_⇒_
infixl 7  _·_
infix  9  `_

data Term : Set where
  lit      : ℕ → Term
  flt      : 𝔽 → Term
  `_       : Id → Term
  ƛ_⇒_     : Id → Term → Term
  _·_      : Term → Term → Term
  +        : Term
  +i       : ℕ → Term
  +f       : 𝔽 → Term


infix 4 _≤_

data _≤_ : Type → Type → Set where

  s-refl : ∀ {A}
    → A ≤ A
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

inv-&-l : ∀ {A B C}
  → A ≤ B & C
  → A ≤ B
inv-&-r : ∀ {A B C}
  → A ≤ B & C
  → A ≤ C

inv-&-l s-refl = s-and-l s-refl
inv-&-l (s-and-l A≤BC) = s-and-l (inv-&-l A≤BC)
inv-&-l (s-and-r A≤BC) = s-and-r (inv-&-l A≤BC)
inv-&-l (s-and A≤BC A≤BC₁) = A≤BC
inv-&-r s-refl = s-and-r s-refl
inv-&-r (s-and-l A≤BC) = s-and-l (inv-&-r A≤BC)
inv-&-r (s-and-r A≤BC) = s-and-r (inv-&-r A≤BC)
inv-&-r (s-and A≤BC A≤BC₁) = A≤BC₁

≤-trans : ∀ {A B C}
  → A ≤ B
  → B ≤ C
  → A ≤ C
≤-trans {B = Top} A≤B s-refl = A≤B
≤-trans {B = Top} A≤B s-top = A≤B
≤-trans {B = Top} A≤B (s-and B≤C B≤C₁) = s-and (≤-trans A≤B B≤C) (≤-trans A≤B B≤C₁)
≤-trans {B = Int} s-refl B≤C = B≤C
≤-trans {B = Int} (s-and-l A≤B) B≤C = s-and-l (≤-trans A≤B B≤C)
≤-trans {B = Int} (s-and-r A≤B) B≤C = s-and-r (≤-trans A≤B B≤C)
≤-trans {B = Float} s-refl B≤C = B≤C
≤-trans {B = Float} (s-and-l A≤B) B≤C = s-and-l (≤-trans A≤B B≤C)
≤-trans {B = Float} (s-and-r A≤B) B≤C = s-and-r (≤-trans A≤B B≤C)
≤-trans {B = B ⇒ B₁} s-refl B≤C = B≤C
≤-trans {B = B ⇒ B₁} (s-arr A≤B A≤B₁) s-refl = s-arr A≤B A≤B₁
≤-trans {B = B ⇒ B₁} (s-arr A≤B A≤B₁) (s-arr B≤C B≤C₁) = s-arr (≤-trans B≤C A≤B) (≤-trans A≤B₁ B≤C₁)
≤-trans {B = B ⇒ B₁} (s-arr A≤B A≤B₁) s-top = s-top
≤-trans {B = B ⇒ B₁} (s-arr A≤B A≤B₁) (s-and B≤C B≤C₁) = s-and (≤-trans (s-arr A≤B A≤B₁) B≤C)
                                                               (≤-trans (s-arr A≤B A≤B₁) B≤C₁)
≤-trans {B = B ⇒ B₁} (s-and-l A≤B) B≤C = s-and-l (≤-trans A≤B B≤C)
≤-trans {B = B ⇒ B₁} (s-and-r A≤B) B≤C = s-and-r (≤-trans A≤B B≤C)
≤-trans {B = B & B₁} A≤B s-refl = A≤B
≤-trans {B = B & B₁} A≤B s-top = s-top
≤-trans {B = B & B₁} A≤B (s-and-l B≤C) = ≤-trans (inv-&-l A≤B) B≤C
≤-trans {B = B & B₁} A≤B (s-and-r B≤C) = ≤-trans (inv-&-r A≤B) B≤C
≤-trans {B = B & B₁} A≤B (s-and B≤C B≤C₁) = s-and (≤-trans A≤B B≤C) (≤-trans A≤B B≤C₁)

infix  4  _⊢_⦂_

data _⊢_⦂_ : Context → Term → Type → Set where

  ⊢n : ∀ {Γ n}
    → Γ ⊢ (lit n) ⦂ Int

  ⊢m : ∀ {Γ m}
    → Γ ⊢ (flt m) ⦂ Int
    
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

  ⊢sub : ∀ {Γ M A B}
    → Γ ⊢ M ⦂ A
    → A ≤ B
    → Γ ⊢ M ⦂ B

infix 9 _[_:=_]

_[_:=_] : Term → Id → Term → Term
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

data Value : Term → Set where

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

infix 4 _—→_

data _—→_ : Term → Term → Set where

  ξ-·₁ : ∀ {L L′ M}
    → L —→ L′
    → L · M —→ L′ · M

  ξ-·₂ : ∀ {V M M′}
    → Value V
    → M —→ M′
    → V · M —→ V · M′

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

progress-+ : ∀ {M A B}
  → ∅ ⊢ + ⦂ A ⇒ B
  → ∅ ⊢ M ⦂ A
  → Value M
  → Progress (+ · M)
progress-+ ⊢N ⊢M V-n = step β-+-i
progress-+ ⊢N ⊢M V-m = step β-+-f
progress-+ ⊢N ⊢M V-ƛ = {!!}
progress-+ ⊢N ⊢M V-+ = {!!}
progress-+ ⊢N ⊢M V-+i = {!!}
progress-+ ⊢N ⊢M V-+f = {!!}

progress : ∀ {e A}
  → ∅ ⊢ e ⦂ A
  → Progress e
progress ⊢n = done V-n
progress ⊢m = done V-m
progress (⊢ƛ ⊢e) = done V-ƛ
progress (⊢· ⊢e₁ ⊢e₂) with progress ⊢e₁ | progress ⊢e₂
... | step s₁ | _ = step (ξ-·₁ s₁)
... | done v₁ | step s₂ = step (ξ-·₂ v₁ s₂)
... | done V-n | done v₂ = ⊥-elim (elim-int' ⊢e₁)
... | done V-m | done v₂ = ⊥-elim (elim-flt' ⊢e₁)
... | done V-ƛ | done v₂ = step (β-ƛ v₂)
... | done V-+ | done v₂ = {!!}
... | done V-+i | done v₂ = {!!}
... | done V-+f | done v₂ = {!!}
progress (⊢& ⊢e ⊢e₁) = progress ⊢e
progress ⊢+ = done V-+
progress ⊢+i = done V-+i
progress ⊢+f = done V-+f
progress (⊢sub ⊢e x) = progress ⊢e

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

inv-lam' : ∀ {Γ x e A B T}
  → Γ ⊢ ƛ x ⇒ e ⦂ T
  → T ≤ A ⇒ B
  → ∃[ A' ]( ∃[ B' ] ((Γ , x ⦂ A' ⊢ e ⦂ B') × (A ≤ A') × (B' ≤ B)))
inv-lam' {A = A} {B} (⊢ƛ ⊢e) s-refl = ⟨ A , ⟨ B , ⟨ ⊢e , ⟨ s-refl , s-refl ⟩ ⟩ ⟩ ⟩
inv-lam' {A = A} {B} (⊢sub ⊢e x) s-refl = inv-lam' ⊢e x
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

inv-+ : ∀ {Γ A B}
  → Γ ⊢ + ⦂ A ⇒ B
  → Int ≤ A
  → Int ⇒ Int ≤ B
inv-+ = {!!}  

preserve : ∀ {M N A}
  → ∅ ⊢ M ⦂ A
  → M —→ N
    ----------
  → ∅ ⊢ N ⦂ A
preserve (⊢· ⊢e ⊢e₁) (ξ-·₁ M→N) = ⊢· (preserve ⊢e M→N) ⊢e₁
preserve (⊢· ⊢e ⊢e₁) (ξ-·₂ x M→N) = ⊢· ⊢e (preserve ⊢e₁ M→N)
preserve (⊢· ⊢e ⊢e₁) (β-ƛ x) with inv-lam ⊢e
... | ⟨ A' , ⟨ B' , ⟨ ⊢e' , ⟨ A≤A' , B'≤B ⟩ ⟩ ⟩ ⟩ = subst (⊢sub ⊢e₁ A≤A') (⊢sub ⊢e' B'≤B)
preserve (⊢· ⊢e ⊢e₁) β-+-i = ⊢sub ⊢+i {!!}
preserve (⊢· ⊢e ⊢e₁) β-+-f = ⊢sub ⊢+f {!!}
preserve (⊢· ⊢e ⊢e₁) β-+i = ⊢sub ⊢n {!!}
preserve (⊢· ⊢e ⊢e₁) β-+f = ⊢sub ⊢m {!!}
preserve (⊢& ⊢e ⊢e₁) M→N = ⊢& (preserve ⊢e M→N) (preserve ⊢e₁ M→N)
preserve (⊢sub ⊢e x) M→N = ⊢sub (preserve ⊢e M→N) x
