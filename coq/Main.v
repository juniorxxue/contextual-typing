Require Import Metalib.Metatheory.
Require Import Coq.Program.Equality.
Require Import Coq.Strings.String.

Import ListNotations.

Set Printing Parentheses.

Inductive type : Set :=
| Int
| Top
| Arr (A B : type).

Inductive term : Set :=
| Lit : nat -> term
| Bvar : nat -> term
| Fvar : var -> term
| Lam : term -> term
| App : term -> term -> term
| Ann : term -> type -> term.

Inductive hype : Set :=
| Hnt
| Hop
| Hrr (A B : hype)
| Hole (e : term).

Hint Constructors type : core.
Hint Constructors term : core.
Hint Constructors hype : core.

Coercion Fvar : atom >-> term.

Definition ctx : Set := list (var * type).

(** * Substituion *)

Fixpoint substitution (z : atom) (u : term) (e : term) {struct e} : term :=
  match e with
  | Lit n => Lit n
  | Bvar i => Bvar i
  | Fvar x => if x == z then u else (Fvar x)
  | Lam e => Lam (substitution z u e)
  | App e1 e2 => App (substitution z u e1) (substitution z u e2)
  | Ann e A => Ann (substitution z u e) A
  end.

Notation "{ z ↦ u } e" := (substitution z u e) (at level 69).

(** * Free variables *)

Fixpoint fv (e : term) {struct e} : atoms :=
  match e with
  | Lit n => empty
  | Bvar i => empty
  | Fvar x => singleton x
  | Lam e => fv e
  | App e1 e2 => (fv e1) `union` (fv e2)
  | Ann e A => fv e
  end.

(** * Opening *)

Fixpoint open_rec (k : nat) (u : term) (e : term) {struct e} : term :=
  match e with
  | Lit n => Lit n
  | Bvar i => if k == i then u else (Bvar i)
  | Fvar x => Fvar x
  | Lam e => Lam (open_rec (S k) u e)
  | App e1 e2 => App (open_rec k u e1) (open_rec k u e2)
  | Ann e A => Ann (open_rec k u e) A
  end.

Definition open e u := open_rec 0 u e.

(** Auxiliary functions for building contexts automatically *)

Ltac gather_atoms ::=
  let A := gather_atoms_with (fun x : atoms => x) in
  let B := gather_atoms_with (fun x : atom => singleton x) in
  let C := gather_atoms_with (fun x : list (atom * type) => dom x) in
  let D := gather_atoms_with (fun x : term => fv x) in
  constr:(A `union` B `union` C `union` D).

Notation "A → B" := (Arr A B) (at level 20).
Notation "A *→ B" := (Hrr A B) (at level 20).
Notation "e ∷ A" := (Ann e A) (at level 20).
Notation "ƛ . e" := (Lam e) (at level 20).
Notation "⟦ e ⟧" := (Hole e) (at level 19).

