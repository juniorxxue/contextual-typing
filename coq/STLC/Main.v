
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
