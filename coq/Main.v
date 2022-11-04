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

(* ------- Typing --------------- *)

Inductive htype :=
| HInt
| HTop
| HArr (A B : htype)
| Hole (e : term).

Fixpoint type_is_htype (A : type) :=
  match A with
  | Int => HInt
  | Top => HTop
  | Arr A B => HArr (type_is_htype A) (type_is_htype B)
  end.

Coercion type_is_htype : type >-> htype.

Inductive ty (G : var -> type) : htype -> term -> type -> Prop :=
| Ty_Lit  A n :
  sub G Int A ->
  ty G A (Lit n) Int
| Ty_Var A B x :
  G x = B -> sub G B A ->
  ty G A (Var x) B
| Ty_App e1 e2 A C D :
  ty G (HArr (Hole e2) A) e1 (Arr C D) ->
  ty G A (App e1 e2) D
| Ty_Ann A (B : type) e :
  ty G B e B -> sub G B A ->
  ty G A (Ann e B) B
| Ty_Lam1 e1 e A B B':
  ty G Top e1 A ->
  ty (A .: G) B' e B ->
  ty G (HArr (Hole e1) B') (Lam e) (Arr A B)
| Ty_Lam2 e A B' C :
  ty (A .: G) B' e C ->
  ty G (HArr A B') (Lam e) (Arr A C)
with sub (G : var -> type) : htype -> htype -> Prop :=
| S_Refl        : sub G HInt HInt
| S_Top A       : sub G A HTop
| S_Arr A B C D : sub G C A -> sub G B D -> sub G (HArr A B) (HArr C D)
| S_Hole A A' e : ty G A e A' -> sub G (Hole e) A.

Lemma ty_sub : forall A B e G,
    ty G A e B ->
    sub G B A.
Proof.
  intros. dependent induction H.
Admitted.
  
