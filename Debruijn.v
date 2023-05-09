Require Import Arith.
Require Import Lia.

Inductive Ty : Set := Int | Arr : Ty -> Ty -> Ty.

Inductive Term : Set :=
  Lit : nat -> Term
| Var (x : nat)
| Lam (e : Term)
| App (e1 e2 : Term)
.

Definition shift_var k :=
  fun x => if le_gt_dec k x then (x + 1) else x.

Fixpoint shift k tm {struct tm} :=
  match tm with
  | Lit n => Lit n
  | Var x => Var (shift_var k x)
  | Lam e => Lam (shift (k + 1) e)
  | App e1 e2 => App (shift k e1) (shift k e2)
  end.

Definition unshift_var k :=
  fun x => if le_gt_dec (k+1) x then (x - 1) else x.

Fixpoint unshift k tm {struct tm} :=
  match tm with
  | Lit n => Lit n
  | Var x => Var (unshift_var k x)
  | Lam e => Lam (unshift (k + 1) e)
  | App e1 e2 => App (unshift k e1) (unshift k e2)
  end.

Lemma unshift_shift_var :
  forall x k,
    unshift_var k (shift_var k x) = x.
Proof.
  intros x k.
  unfold unshift_var, shift_var.
  destruct (le_gt_dec k x).
  - destruct (le_gt_dec (k + 1) (x + 1)).
    + lia.
    + lia.
  - destruct (le_gt_dec (k + 1) x).
    + lia.
    + reflexivity.
Qed.
    
                 


                    
              


