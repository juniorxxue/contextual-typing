Require Import Autosubst.Autosubst.

Inductive term :=
| Var (x : var)
| App (e1 e2 : term)
| Lam (e : {bind term}).

Inductive type :=
| Int
| Top
| Arr (A B : type).
