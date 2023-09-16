Require Import List.
Import ListNotations.

Inductive type : Set :=
| Int : type
| Arr : type -> type -> type.

Inductive term : Set :=
| Lit : nat -> term
| Var : nat -> term
| Lam : term -> term
| App : term -> term -> term
| Ann : term -> type -> term.

Inductive context : Set :=
| Empty : context
| Cons  : context -> type -> context.

Inductive inCon : context -> nat -> type -> Set :=
| Zin : forall {Gamma A},
      inCon (Cons Gamma A) 0 A
| Sin : forall {Gamma A B n},
      inCon Gamma n A ->
      inCon (Cons Gamma B) (S n) A.

(* Decl. *)

Inductive counter : Set :=
| Inf : counter
| ZCo : counter
| SCo : counter -> counter.

Inductive dwf : type -> counter -> Set :=
| dwf_Z : forall A,
    dwf A ZCo
| dwf_Inf : forall A,
    dwf A Inf
| dwf_S : forall A B j,
    dwf B j ->
    dwf (Arr A B) (SCo j)
.

Inductive dty : context -> counter -> term -> type -> Set :=
| D_Int : forall Gamma i,
    dty Gamma ZCo (Lit i) Int
| D_Var : forall Gamma x A,
    inCon Gamma x A ->
    dty Gamma ZCo (Var x) A
| D_Ann : forall Gamma e A,
    dty Gamma Inf e A ->
    dty Gamma ZCo (Ann e A) A
| D_Lam_Inf : forall Gamma e A B,
    dty (Cons Gamma A) Inf e B ->
    dty Gamma Inf (Lam e) (Arr A B)
| D_Lam_N : forall Gamma e A B j,
    dty (Cons Gamma A) j e B ->
    dty Gamma (SCo j) (Lam e) (Arr A B)
| D_App1 : forall Gamma e1 e2 A B,
    dty Gamma ZCo e1 (Arr A B) ->
    dty Gamma Inf e2 A ->
    dty Gamma ZCo (App e1 e2) B
| D_App2 : forall Gamma e1 e2 A B j,
    dty Gamma (SCo j) e1 (Arr A B) ->
    dty Gamma ZCo e2 A ->
    dty Gamma j (App e1 e2) B
| D_Sub: forall Gamma e A j,
    dty Gamma ZCo e A ->
    dwf A j ->
    dty Gamma j e A
.      

(* Algo. *)

Inductive hint : Set :=
| Noth : hint
| Tau : type -> hint
| Ho : term -> hint -> hint.


Inductive awf : context -> type -> hint -> Set :=
| awf_Noth : forall Gamma A,
    awf Gamma A Noth
| awf_Tau : forall Gamma A,
    awf Gamma A (Tau A)
| awf_Hole : forall Gamma H e A B C,
    aty Gamma (Tau A) e C ->
    awf Gamma B H ->
    awf Gamma (Arr A B) (Ho e H)
with aty : context -> hint -> term -> type -> Set :=
| A_Int : forall Gamma n,
    aty Gamma Noth (Lit n) Int
| A_Var : forall Gamma x A,
    aty Gamma Noth (Var x) A
| A_Ann : forall Gamma e A B,
    aty Gamma (Tau A) e B ->
    aty Gamma Noth (Ann e A) A
| A_App : forall Gamma e1 e2 H A B,
    aty Gamma (Ho e2 H) e1 (Arr A B) ->
    aty Gamma H (App e1 e2) B
(* I omit the shift here to simplify *)
| A_Lam1 : forall Gamma e A B C,
    aty (Cons Gamma A) (Tau B) e C ->
    aty Gamma (Tau (Arr A B)) (Lam e) (Arr A C)
| A_Lam2 : forall Gamma e1 e A B H,
    aty Gamma Noth e1 A ->
    aty (Cons Gamma A) H e B ->
    aty Gamma (Ho e1 H) (Lam e) (Arr A B)
| A_Sub : forall Gamma e A H,
    aty Gamma Noth e A ->
    awf Gamma A H ->
    aty Gamma H e A
.


Fixpoint apps (e : term) (es : list term) : term :=
  match es with
  | [] => e
  | e' :: es' => apps (App e e') es'
  end.

Inductive spl : hint -> type -> list term -> hint -> list type -> type -> Set :=
| No_Noth : forall A,
    spl Noth A [] Noth [] A
| No_Tau : forall A B,
    spl (Tau A) B [] (Tau A) [] B
| Have : forall e H A B es A' B' Bs,
    spl H B es A' Bs B' ->
    spl (Ho e H) (Arr A B) (e :: es) A' (A :: Bs) B'        
.

Theorem rev_app_dist: forall {X} (l1 l2:list X), rev (l1 ++ l2) = rev l2 ++ rev l1.
Proof.
  intros X l1 l2.
  induction l2 using rev_ind.
Admitted.       

Lemma subst_app : forall es Gamma A B e e1 j,
    dty (Cons Gamma A) j (apps e es) B ->
    dty Gamma ZCo e1 A ->
    dty Gamma j (apps (App (Lam e) e1) es) B.
Proof.
  intros es Gamma A B e e1 j.
  induction es using rev_ind.
