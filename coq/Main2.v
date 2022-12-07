Require Import Autosubst.Autosubst.
Require Import Coq.Program.Equality.

(* ------- Syntax --------------- *)

Inductive type :=
| Int
| Top
| Arr (A B : type).

Inductive term :=
| Lit (n : nat)
| Var (x : var)
| Lam (e : {bind term})
| App (e1 e2 : term)
| Ann (e : term) (A : type).

Instance Ids_term : Ids term. derive. Defined.
Instance Rename_term : Rename term. derive. Defined.
Instance Subst_term : Subst term. derive. Defined.
Instance SubstLemmas_term : SubstLemmas term. derive. Qed.

(* ------- Typing --------------- *)

Inductive htype :=
| HInt
| HTop
| HArr (A B : type)
| Hole (e : term) (B : htype).

Fixpoint type_is_htype (A : type) : htype :=
  match A with
  | Int => HInt
  | Top => HTop
  | Arr A B => HArr A B
  end.

Coercion type_is_htype : type >-> htype.

Inductive ty (Γ : var -> type) : htype -> term -> type -> Prop :=
| Ty_Lit  A n :
  sub Γ Int A ->
  ty Γ A (Lit n) Int
| Ty_Var A B x :
  Γ x = B -> sub Γ B A ->
  ty Γ A (Var x) B     
| Ty_App e1 e2 A C D :
  ty Γ (Hole e2 A) e1 (Arr C D) ->
  ty Γ A (App e1 e2) D     
| Ty_Ann A (B : type) C e :
  ty Γ B e C -> sub Γ B A ->
  ty Γ A (Ann e B) B     
| Ty_Lam1 e1 e A B B':
  ty Γ Top e1 A ->
  ty (A .: Γ) B' e B ->
  ty Γ (Hole e1 B') (Lam e) (Arr A B)     
| Ty_Lam2 e A (B : type) C :
  ty (A .: Γ) B e C ->
  ty Γ (Arr A B) (Lam e) (Arr A C)
with sub (Γ : var -> type) : htype -> htype -> Prop :=
| S_Int         : sub Γ Int Int
| S_Top A       : sub Γ A Top
| S_Arr (A B C D :type) : sub Γ C A -> sub Γ B D -> sub Γ (HArr A B) (HArr C D)
| S_Hole (A B : type) A' B' e : ty Γ A e A' -> sub Γ B B' -> sub Γ (HArr A B) (Hole e B').


