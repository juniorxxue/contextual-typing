Require Import Coq.Arith.Wf_nat.
Require Import Coq.Logic.FunctionalExtensionality.
Require Import Coq.Program.Equality.

Require Export Metalib.Metatheory.
Require Export Metalib.LibLNgen.

Require Export subtyping.decl.

Local Set Warnings "-non-recursive". 

(** NOTE: Auxiliary theorems are hidden in generated documentation.
    In general, there is a [_rec] version of every lemma involving
    [open] and [close]. *)


(* *********************************************************************** *)
(** * Induction principles for nonterminals *)

Scheme typ_ind' := Induction for typ Sort Prop.

Combined Scheme typ_mutind from typ_ind'.

Scheme typ_rec' := Induction for typ Sort Set.

Combined Scheme typ_mutrec from typ_rec'.

Scheme bind_ind' := Induction for bind Sort Prop.

Combined Scheme bind_mutind from bind_ind'.

Scheme bind_rec' := Induction for bind Sort Set.

Combined Scheme bind_mutrec from bind_rec'.

Scheme counter_ind' := Induction for counter Sort Prop.

Combined Scheme counter_mutind from counter_ind'.

Scheme counter_rec' := Induction for counter Sort Set.

Combined Scheme counter_mutrec from counter_rec'.


(* *********************************************************************** *)
(** * Size *)

Fixpoint size_typ (A1 : typ) {struct A1} : nat :=
  match A1 with
    | typ_unit => 1
    | typ_var_f X1 => 1
    | typ_var_b n1 => 1
    | typ_arrow A2 A3 => 1 + (size_typ A2) + (size_typ A3)
    | typ_all A2 => 1 + (size_typ A2)
  end.

Fixpoint size_bind (b1 : bind) {struct b1} : nat :=
  match b1 with
    | bind_empty => 1
    | bind_typ A1 => 1 + (size_typ A1)
  end.

Fixpoint size_counter (c1 : counter) {struct c1} : nat :=
  match c1 with
    | counter_z => 1
    | counter_inf => 1
    | counter_suc c2 => 1 + (size_counter c2)
    | counter_tsuc c2 => 1 + (size_counter c2)
  end.


(* *********************************************************************** *)
(** * Degree *)

(** These define only an upper bound, not a strict upper bound. *)

Inductive degree_typ_wrt_typ : nat -> typ -> Prop :=
  | degree_wrt_typ_typ_unit : forall n1,
    degree_typ_wrt_typ n1 (typ_unit)
  | degree_wrt_typ_typ_var_f : forall n1 X1,
    degree_typ_wrt_typ n1 (typ_var_f X1)
  | degree_wrt_typ_typ_var_b : forall n1 n2,
    lt n2 n1 ->
    degree_typ_wrt_typ n1 (typ_var_b n2)
  | degree_wrt_typ_typ_arrow : forall n1 A1 A2,
    degree_typ_wrt_typ n1 A1 ->
    degree_typ_wrt_typ n1 A2 ->
    degree_typ_wrt_typ n1 (typ_arrow A1 A2)
  | degree_wrt_typ_typ_all : forall n1 A1,
    degree_typ_wrt_typ (S n1) A1 ->
    degree_typ_wrt_typ n1 (typ_all A1).

Scheme degree_typ_wrt_typ_ind' := Induction for degree_typ_wrt_typ Sort Prop.

Combined Scheme degree_typ_wrt_typ_mutind from degree_typ_wrt_typ_ind'.

#[export] Hint Constructors degree_typ_wrt_typ : core lngen.

Inductive degree_bind_wrt_typ : nat -> bind -> Prop :=
  | degree_wrt_typ_bind_empty : forall n1,
    degree_bind_wrt_typ n1 (bind_empty)
  | degree_wrt_typ_bind_typ : forall n1 A1,
    degree_typ_wrt_typ n1 A1 ->
    degree_bind_wrt_typ n1 (bind_typ A1).

Scheme degree_bind_wrt_typ_ind' := Induction for degree_bind_wrt_typ Sort Prop.

Combined Scheme degree_bind_wrt_typ_mutind from degree_bind_wrt_typ_ind'.

#[export] Hint Constructors degree_bind_wrt_typ : core lngen.


(* *********************************************************************** *)
(** * Local closure (version in [Set], induction principles) *)

Inductive lc_set_typ : typ -> Set :=
  | lc_set_typ_unit :
    lc_set_typ (typ_unit)
  | lc_set_typ_var_f : forall X1,
    lc_set_typ (typ_var_f X1)
  | lc_set_typ_arrow : forall A1 A2,
    lc_set_typ A1 ->
    lc_set_typ A2 ->
    lc_set_typ (typ_arrow A1 A2)
  | lc_set_typ_all : forall A1,
    (forall X1 : typvar, lc_set_typ (open_typ_wrt_typ A1 (typ_var_f X1))) ->
    lc_set_typ (typ_all A1).

Scheme lc_typ_ind' := Induction for lc_typ Sort Prop.

Combined Scheme lc_typ_mutind from lc_typ_ind'.

Scheme lc_set_typ_ind' := Induction for lc_set_typ Sort Prop.

Combined Scheme lc_set_typ_mutind from lc_set_typ_ind'.

Scheme lc_set_typ_rec' := Induction for lc_set_typ Sort Set.

Combined Scheme lc_set_typ_mutrec from lc_set_typ_rec'.

#[export] Hint Constructors lc_typ : core lngen.

#[export] Hint Constructors lc_set_typ : core lngen.

Inductive lc_set_bind : bind -> Set :=
  | lc_set_bind_empty :
    lc_set_bind (bind_empty)
  | lc_set_bind_typ : forall A1,
    lc_set_typ A1 ->
    lc_set_bind (bind_typ A1).

Scheme lc_bind_ind' := Induction for lc_bind Sort Prop.

Combined Scheme lc_bind_mutind from lc_bind_ind'.

Scheme lc_set_bind_ind' := Induction for lc_set_bind Sort Prop.

Combined Scheme lc_set_bind_mutind from lc_set_bind_ind'.

Scheme lc_set_bind_rec' := Induction for lc_set_bind Sort Set.

Combined Scheme lc_set_bind_mutrec from lc_set_bind_rec'.

#[export] Hint Constructors lc_bind : core lngen.

#[export] Hint Constructors lc_set_bind : core lngen.


(* *********************************************************************** *)
(** * Body *)

Definition body_typ_wrt_typ A1 := forall X1, lc_typ (open_typ_wrt_typ A1 (typ_var_f X1)).

#[export] Hint Unfold body_typ_wrt_typ : core.

Definition body_bind_wrt_typ b1 := forall X1, lc_bind (open_bind_wrt_typ b1 (typ_var_f X1)).

#[export] Hint Unfold body_bind_wrt_typ : core.


(* *********************************************************************** *)
(** * Tactic support *)

(** Additional hint declarations. *)

#[export] Hint Resolve plus_le_compat : lngen.

(** Redefine some tactics. *)

Ltac default_case_split ::=
  first
    [ progress destruct_notin
    | progress destruct_sum
    | progress safe_f_equal
    ].


(* *********************************************************************** *)
(** * Theorems about [size] *)

Ltac default_auto ::= auto with arith lngen; tauto.
Ltac default_autorewrite ::= fail.

(* begin hide *)

Lemma size_typ_min_mutual :
(forall A1, 1 <= size_typ A1).
Proof.
apply_mutual_ind typ_mutind;
default_simp.
Qed.

(* end hide *)

Lemma size_typ_min :
forall A1, 1 <= size_typ A1.
Proof.
pose proof size_typ_min_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve size_typ_min : lngen.

(* begin hide *)

Lemma size_bind_min_mutual :
(forall b1, 1 <= size_bind b1).
Proof.
apply_mutual_ind bind_mutind;
default_simp.
Qed.

(* end hide *)

Lemma size_bind_min :
forall b1, 1 <= size_bind b1.
Proof.
pose proof size_bind_min_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve size_bind_min : lngen.

(* begin hide *)

Lemma size_counter_min_mutual :
(forall c1, 1 <= size_counter c1).
Proof.
apply_mutual_ind counter_mutind;
default_simp.
Qed.

(* end hide *)

Lemma size_counter_min :
forall c1, 1 <= size_counter c1.
Proof.
pose proof size_counter_min_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve size_counter_min : lngen.

(* begin hide *)

Lemma size_typ_close_typ_wrt_typ_rec_mutual :
(forall A1 X1 n1,
  size_typ (close_typ_wrt_typ_rec n1 X1 A1) = size_typ A1).
Proof.
apply_mutual_ind typ_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma size_typ_close_typ_wrt_typ_rec :
forall A1 X1 n1,
  size_typ (close_typ_wrt_typ_rec n1 X1 A1) = size_typ A1.
Proof.
pose proof size_typ_close_typ_wrt_typ_rec_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve size_typ_close_typ_wrt_typ_rec : lngen.
#[export] Hint Rewrite size_typ_close_typ_wrt_typ_rec using solve [auto] : lngen.

(* end hide *)

(* begin hide *)

Lemma size_bind_close_bind_wrt_typ_rec_mutual :
(forall b1 X1 n1,
  size_bind (close_bind_wrt_typ_rec n1 X1 b1) = size_bind b1).
Proof.
apply_mutual_ind bind_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma size_bind_close_bind_wrt_typ_rec :
forall b1 X1 n1,
  size_bind (close_bind_wrt_typ_rec n1 X1 b1) = size_bind b1.
Proof.
pose proof size_bind_close_bind_wrt_typ_rec_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve size_bind_close_bind_wrt_typ_rec : lngen.
#[export] Hint Rewrite size_bind_close_bind_wrt_typ_rec using solve [auto] : lngen.

(* end hide *)

Lemma size_typ_close_typ_wrt_typ :
forall A1 X1,
  size_typ (close_typ_wrt_typ X1 A1) = size_typ A1.
Proof.
unfold close_typ_wrt_typ; default_simp.
Qed.

#[export] Hint Resolve size_typ_close_typ_wrt_typ : lngen.
#[export] Hint Rewrite size_typ_close_typ_wrt_typ using solve [auto] : lngen.

Lemma size_bind_close_bind_wrt_typ :
forall b1 X1,
  size_bind (close_bind_wrt_typ X1 b1) = size_bind b1.
Proof.
unfold close_bind_wrt_typ; default_simp.
Qed.

#[export] Hint Resolve size_bind_close_bind_wrt_typ : lngen.
#[export] Hint Rewrite size_bind_close_bind_wrt_typ using solve [auto] : lngen.

(* begin hide *)

Lemma size_typ_open_typ_wrt_typ_rec_mutual :
(forall A1 A2 n1,
  size_typ A1 <= size_typ (open_typ_wrt_typ_rec n1 A2 A1)).
Proof.
apply_mutual_ind typ_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma size_typ_open_typ_wrt_typ_rec :
forall A1 A2 n1,
  size_typ A1 <= size_typ (open_typ_wrt_typ_rec n1 A2 A1).
Proof.
pose proof size_typ_open_typ_wrt_typ_rec_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve size_typ_open_typ_wrt_typ_rec : lngen.

(* end hide *)

(* begin hide *)

Lemma size_bind_open_bind_wrt_typ_rec_mutual :
(forall b1 A1 n1,
  size_bind b1 <= size_bind (open_bind_wrt_typ_rec n1 A1 b1)).
Proof.
apply_mutual_ind bind_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma size_bind_open_bind_wrt_typ_rec :
forall b1 A1 n1,
  size_bind b1 <= size_bind (open_bind_wrt_typ_rec n1 A1 b1).
Proof.
pose proof size_bind_open_bind_wrt_typ_rec_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve size_bind_open_bind_wrt_typ_rec : lngen.

(* end hide *)

Lemma size_typ_open_typ_wrt_typ :
forall A1 A2,
  size_typ A1 <= size_typ (open_typ_wrt_typ A1 A2).
Proof.
unfold open_typ_wrt_typ; default_simp.
Qed.

#[export] Hint Resolve size_typ_open_typ_wrt_typ : lngen.

Lemma size_bind_open_bind_wrt_typ :
forall b1 A1,
  size_bind b1 <= size_bind (open_bind_wrt_typ b1 A1).
Proof.
unfold open_bind_wrt_typ; default_simp.
Qed.

#[export] Hint Resolve size_bind_open_bind_wrt_typ : lngen.

(* begin hide *)

Lemma size_typ_open_typ_wrt_typ_rec_var_mutual :
(forall A1 X1 n1,
  size_typ (open_typ_wrt_typ_rec n1 (typ_var_f X1) A1) = size_typ A1).
Proof.
apply_mutual_ind typ_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma size_typ_open_typ_wrt_typ_rec_var :
forall A1 X1 n1,
  size_typ (open_typ_wrt_typ_rec n1 (typ_var_f X1) A1) = size_typ A1.
Proof.
pose proof size_typ_open_typ_wrt_typ_rec_var_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve size_typ_open_typ_wrt_typ_rec_var : lngen.
#[export] Hint Rewrite size_typ_open_typ_wrt_typ_rec_var using solve [auto] : lngen.

(* end hide *)

(* begin hide *)

Lemma size_bind_open_bind_wrt_typ_rec_var_mutual :
(forall b1 X1 n1,
  size_bind (open_bind_wrt_typ_rec n1 (typ_var_f X1) b1) = size_bind b1).
Proof.
apply_mutual_ind bind_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma size_bind_open_bind_wrt_typ_rec_var :
forall b1 X1 n1,
  size_bind (open_bind_wrt_typ_rec n1 (typ_var_f X1) b1) = size_bind b1.
Proof.
pose proof size_bind_open_bind_wrt_typ_rec_var_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve size_bind_open_bind_wrt_typ_rec_var : lngen.
#[export] Hint Rewrite size_bind_open_bind_wrt_typ_rec_var using solve [auto] : lngen.

(* end hide *)

Lemma size_typ_open_typ_wrt_typ_var :
forall A1 X1,
  size_typ (open_typ_wrt_typ A1 (typ_var_f X1)) = size_typ A1.
Proof.
unfold open_typ_wrt_typ; default_simp.
Qed.

#[export] Hint Resolve size_typ_open_typ_wrt_typ_var : lngen.
#[export] Hint Rewrite size_typ_open_typ_wrt_typ_var using solve [auto] : lngen.

Lemma size_bind_open_bind_wrt_typ_var :
forall b1 X1,
  size_bind (open_bind_wrt_typ b1 (typ_var_f X1)) = size_bind b1.
Proof.
unfold open_bind_wrt_typ; default_simp.
Qed.

#[export] Hint Resolve size_bind_open_bind_wrt_typ_var : lngen.
#[export] Hint Rewrite size_bind_open_bind_wrt_typ_var using solve [auto] : lngen.


(* *********************************************************************** *)
(** * Theorems about [degree] *)

Ltac default_auto ::= auto with lngen; tauto.
Ltac default_autorewrite ::= fail.

(* begin hide *)

Lemma degree_typ_wrt_typ_S_mutual :
(forall n1 A1,
  degree_typ_wrt_typ n1 A1 ->
  degree_typ_wrt_typ (S n1) A1).
Proof.
apply_mutual_ind degree_typ_wrt_typ_mutind;
default_simp.
Qed.

(* end hide *)

Lemma degree_typ_wrt_typ_S :
forall n1 A1,
  degree_typ_wrt_typ n1 A1 ->
  degree_typ_wrt_typ (S n1) A1.
Proof.
pose proof degree_typ_wrt_typ_S_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve degree_typ_wrt_typ_S : lngen.

(* begin hide *)

Lemma degree_bind_wrt_typ_S_mutual :
(forall n1 b1,
  degree_bind_wrt_typ n1 b1 ->
  degree_bind_wrt_typ (S n1) b1).
Proof.
apply_mutual_ind degree_bind_wrt_typ_mutind;
default_simp.
Qed.

(* end hide *)

Lemma degree_bind_wrt_typ_S :
forall n1 b1,
  degree_bind_wrt_typ n1 b1 ->
  degree_bind_wrt_typ (S n1) b1.
Proof.
pose proof degree_bind_wrt_typ_S_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve degree_bind_wrt_typ_S : lngen.

Lemma degree_typ_wrt_typ_O :
forall n1 A1,
  degree_typ_wrt_typ O A1 ->
  degree_typ_wrt_typ n1 A1.
Proof.
induction n1; default_simp.
Qed.

#[export] Hint Resolve degree_typ_wrt_typ_O : lngen.

Lemma degree_bind_wrt_typ_O :
forall n1 b1,
  degree_bind_wrt_typ O b1 ->
  degree_bind_wrt_typ n1 b1.
Proof.
induction n1; default_simp.
Qed.

#[export] Hint Resolve degree_bind_wrt_typ_O : lngen.

(* begin hide *)

Lemma degree_typ_wrt_typ_close_typ_wrt_typ_rec_mutual :
(forall A1 X1 n1,
  degree_typ_wrt_typ n1 A1 ->
  degree_typ_wrt_typ (S n1) (close_typ_wrt_typ_rec n1 X1 A1)).
Proof.
apply_mutual_ind typ_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma degree_typ_wrt_typ_close_typ_wrt_typ_rec :
forall A1 X1 n1,
  degree_typ_wrt_typ n1 A1 ->
  degree_typ_wrt_typ (S n1) (close_typ_wrt_typ_rec n1 X1 A1).
Proof.
pose proof degree_typ_wrt_typ_close_typ_wrt_typ_rec_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve degree_typ_wrt_typ_close_typ_wrt_typ_rec : lngen.

(* end hide *)

(* begin hide *)

Lemma degree_bind_wrt_typ_close_bind_wrt_typ_rec_mutual :
(forall b1 X1 n1,
  degree_bind_wrt_typ n1 b1 ->
  degree_bind_wrt_typ (S n1) (close_bind_wrt_typ_rec n1 X1 b1)).
Proof.
apply_mutual_ind bind_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma degree_bind_wrt_typ_close_bind_wrt_typ_rec :
forall b1 X1 n1,
  degree_bind_wrt_typ n1 b1 ->
  degree_bind_wrt_typ (S n1) (close_bind_wrt_typ_rec n1 X1 b1).
Proof.
pose proof degree_bind_wrt_typ_close_bind_wrt_typ_rec_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve degree_bind_wrt_typ_close_bind_wrt_typ_rec : lngen.

(* end hide *)

Lemma degree_typ_wrt_typ_close_typ_wrt_typ :
forall A1 X1,
  degree_typ_wrt_typ 0 A1 ->
  degree_typ_wrt_typ 1 (close_typ_wrt_typ X1 A1).
Proof.
unfold close_typ_wrt_typ; default_simp.
Qed.

#[export] Hint Resolve degree_typ_wrt_typ_close_typ_wrt_typ : lngen.

Lemma degree_bind_wrt_typ_close_bind_wrt_typ :
forall b1 X1,
  degree_bind_wrt_typ 0 b1 ->
  degree_bind_wrt_typ 1 (close_bind_wrt_typ X1 b1).
Proof.
unfold close_bind_wrt_typ; default_simp.
Qed.

#[export] Hint Resolve degree_bind_wrt_typ_close_bind_wrt_typ : lngen.

(* begin hide *)

Lemma degree_typ_wrt_typ_close_typ_wrt_typ_rec_inv_mutual :
(forall A1 X1 n1,
  degree_typ_wrt_typ (S n1) (close_typ_wrt_typ_rec n1 X1 A1) ->
  degree_typ_wrt_typ n1 A1).
Proof.
apply_mutual_ind typ_mutind;
default_simp; eauto with lngen.
Qed.

(* end hide *)

(* begin hide *)

Lemma degree_typ_wrt_typ_close_typ_wrt_typ_rec_inv :
forall A1 X1 n1,
  degree_typ_wrt_typ (S n1) (close_typ_wrt_typ_rec n1 X1 A1) ->
  degree_typ_wrt_typ n1 A1.
Proof.
pose proof degree_typ_wrt_typ_close_typ_wrt_typ_rec_inv_mutual as H; intuition eauto.
Qed.

#[export] Hint Immediate degree_typ_wrt_typ_close_typ_wrt_typ_rec_inv : lngen.

(* end hide *)

(* begin hide *)

Lemma degree_bind_wrt_typ_close_bind_wrt_typ_rec_inv_mutual :
(forall b1 X1 n1,
  degree_bind_wrt_typ (S n1) (close_bind_wrt_typ_rec n1 X1 b1) ->
  degree_bind_wrt_typ n1 b1).
Proof.
apply_mutual_ind bind_mutind;
default_simp; eauto with lngen.
Qed.

(* end hide *)

(* begin hide *)

Lemma degree_bind_wrt_typ_close_bind_wrt_typ_rec_inv :
forall b1 X1 n1,
  degree_bind_wrt_typ (S n1) (close_bind_wrt_typ_rec n1 X1 b1) ->
  degree_bind_wrt_typ n1 b1.
Proof.
pose proof degree_bind_wrt_typ_close_bind_wrt_typ_rec_inv_mutual as H; intuition eauto.
Qed.

#[export] Hint Immediate degree_bind_wrt_typ_close_bind_wrt_typ_rec_inv : lngen.

(* end hide *)

Lemma degree_typ_wrt_typ_close_typ_wrt_typ_inv :
forall A1 X1,
  degree_typ_wrt_typ 1 (close_typ_wrt_typ X1 A1) ->
  degree_typ_wrt_typ 0 A1.
Proof.
unfold close_typ_wrt_typ; eauto with lngen.
Qed.

#[export] Hint Immediate degree_typ_wrt_typ_close_typ_wrt_typ_inv : lngen.

Lemma degree_bind_wrt_typ_close_bind_wrt_typ_inv :
forall b1 X1,
  degree_bind_wrt_typ 1 (close_bind_wrt_typ X1 b1) ->
  degree_bind_wrt_typ 0 b1.
Proof.
unfold close_bind_wrt_typ; eauto with lngen.
Qed.

#[export] Hint Immediate degree_bind_wrt_typ_close_bind_wrt_typ_inv : lngen.

(* begin hide *)

Lemma degree_typ_wrt_typ_open_typ_wrt_typ_rec_mutual :
(forall A1 A2 n1,
  degree_typ_wrt_typ (S n1) A1 ->
  degree_typ_wrt_typ n1 A2 ->
  degree_typ_wrt_typ n1 (open_typ_wrt_typ_rec n1 A2 A1)).
Proof.
apply_mutual_ind typ_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma degree_typ_wrt_typ_open_typ_wrt_typ_rec :
forall A1 A2 n1,
  degree_typ_wrt_typ (S n1) A1 ->
  degree_typ_wrt_typ n1 A2 ->
  degree_typ_wrt_typ n1 (open_typ_wrt_typ_rec n1 A2 A1).
Proof.
pose proof degree_typ_wrt_typ_open_typ_wrt_typ_rec_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve degree_typ_wrt_typ_open_typ_wrt_typ_rec : lngen.

(* end hide *)

(* begin hide *)

Lemma degree_bind_wrt_typ_open_bind_wrt_typ_rec_mutual :
(forall b1 A1 n1,
  degree_bind_wrt_typ (S n1) b1 ->
  degree_typ_wrt_typ n1 A1 ->
  degree_bind_wrt_typ n1 (open_bind_wrt_typ_rec n1 A1 b1)).
Proof.
apply_mutual_ind bind_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma degree_bind_wrt_typ_open_bind_wrt_typ_rec :
forall b1 A1 n1,
  degree_bind_wrt_typ (S n1) b1 ->
  degree_typ_wrt_typ n1 A1 ->
  degree_bind_wrt_typ n1 (open_bind_wrt_typ_rec n1 A1 b1).
Proof.
pose proof degree_bind_wrt_typ_open_bind_wrt_typ_rec_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve degree_bind_wrt_typ_open_bind_wrt_typ_rec : lngen.

(* end hide *)

Lemma degree_typ_wrt_typ_open_typ_wrt_typ :
forall A1 A2,
  degree_typ_wrt_typ 1 A1 ->
  degree_typ_wrt_typ 0 A2 ->
  degree_typ_wrt_typ 0 (open_typ_wrt_typ A1 A2).
Proof.
unfold open_typ_wrt_typ; default_simp.
Qed.

#[export] Hint Resolve degree_typ_wrt_typ_open_typ_wrt_typ : lngen.

Lemma degree_bind_wrt_typ_open_bind_wrt_typ :
forall b1 A1,
  degree_bind_wrt_typ 1 b1 ->
  degree_typ_wrt_typ 0 A1 ->
  degree_bind_wrt_typ 0 (open_bind_wrt_typ b1 A1).
Proof.
unfold open_bind_wrt_typ; default_simp.
Qed.

#[export] Hint Resolve degree_bind_wrt_typ_open_bind_wrt_typ : lngen.

(* begin hide *)

Lemma degree_typ_wrt_typ_open_typ_wrt_typ_rec_inv_mutual :
(forall A1 A2 n1,
  degree_typ_wrt_typ n1 (open_typ_wrt_typ_rec n1 A2 A1) ->
  degree_typ_wrt_typ (S n1) A1).
Proof.
apply_mutual_ind typ_mutind;
default_simp; eauto with lngen.
Qed.

(* end hide *)

(* begin hide *)

Lemma degree_typ_wrt_typ_open_typ_wrt_typ_rec_inv :
forall A1 A2 n1,
  degree_typ_wrt_typ n1 (open_typ_wrt_typ_rec n1 A2 A1) ->
  degree_typ_wrt_typ (S n1) A1.
Proof.
pose proof degree_typ_wrt_typ_open_typ_wrt_typ_rec_inv_mutual as H; intuition eauto.
Qed.

#[export] Hint Immediate degree_typ_wrt_typ_open_typ_wrt_typ_rec_inv : lngen.

(* end hide *)

(* begin hide *)

Lemma degree_bind_wrt_typ_open_bind_wrt_typ_rec_inv_mutual :
(forall b1 A1 n1,
  degree_bind_wrt_typ n1 (open_bind_wrt_typ_rec n1 A1 b1) ->
  degree_bind_wrt_typ (S n1) b1).
Proof.
apply_mutual_ind bind_mutind;
default_simp; eauto with lngen.
Qed.

(* end hide *)

(* begin hide *)

Lemma degree_bind_wrt_typ_open_bind_wrt_typ_rec_inv :
forall b1 A1 n1,
  degree_bind_wrt_typ n1 (open_bind_wrt_typ_rec n1 A1 b1) ->
  degree_bind_wrt_typ (S n1) b1.
Proof.
pose proof degree_bind_wrt_typ_open_bind_wrt_typ_rec_inv_mutual as H; intuition eauto.
Qed.

#[export] Hint Immediate degree_bind_wrt_typ_open_bind_wrt_typ_rec_inv : lngen.

(* end hide *)

Lemma degree_typ_wrt_typ_open_typ_wrt_typ_inv :
forall A1 A2,
  degree_typ_wrt_typ 0 (open_typ_wrt_typ A1 A2) ->
  degree_typ_wrt_typ 1 A1.
Proof.
unfold open_typ_wrt_typ; eauto with lngen.
Qed.

#[export] Hint Immediate degree_typ_wrt_typ_open_typ_wrt_typ_inv : lngen.

Lemma degree_bind_wrt_typ_open_bind_wrt_typ_inv :
forall b1 A1,
  degree_bind_wrt_typ 0 (open_bind_wrt_typ b1 A1) ->
  degree_bind_wrt_typ 1 b1.
Proof.
unfold open_bind_wrt_typ; eauto with lngen.
Qed.

#[export] Hint Immediate degree_bind_wrt_typ_open_bind_wrt_typ_inv : lngen.


(* *********************************************************************** *)
(** * Theorems about [open] and [close] *)

Ltac default_auto ::= auto with lngen brute_force; tauto.
Ltac default_autorewrite ::= fail.

(* begin hide *)

Lemma close_typ_wrt_typ_rec_inj_mutual :
(forall A1 A2 X1 n1,
  close_typ_wrt_typ_rec n1 X1 A1 = close_typ_wrt_typ_rec n1 X1 A2 ->
  A1 = A2).
Proof.
apply_mutual_ind typ_mutind;
intros; match goal with
          | |- _ = ?term => destruct term
        end;
default_simp; eauto with lngen.
Qed.

(* end hide *)

(* begin hide *)

Lemma close_typ_wrt_typ_rec_inj :
forall A1 A2 X1 n1,
  close_typ_wrt_typ_rec n1 X1 A1 = close_typ_wrt_typ_rec n1 X1 A2 ->
  A1 = A2.
Proof.
pose proof close_typ_wrt_typ_rec_inj_mutual as H; intuition eauto.
Qed.

#[export] Hint Immediate close_typ_wrt_typ_rec_inj : lngen.

(* end hide *)

(* begin hide *)

Lemma close_bind_wrt_typ_rec_inj_mutual :
(forall b1 b2 X1 n1,
  close_bind_wrt_typ_rec n1 X1 b1 = close_bind_wrt_typ_rec n1 X1 b2 ->
  b1 = b2).
Proof.
apply_mutual_ind bind_mutind;
intros; match goal with
          | |- _ = ?term => destruct term
        end;
default_simp; eauto with lngen.
Qed.

(* end hide *)

(* begin hide *)

Lemma close_bind_wrt_typ_rec_inj :
forall b1 b2 X1 n1,
  close_bind_wrt_typ_rec n1 X1 b1 = close_bind_wrt_typ_rec n1 X1 b2 ->
  b1 = b2.
Proof.
pose proof close_bind_wrt_typ_rec_inj_mutual as H; intuition eauto.
Qed.

#[export] Hint Immediate close_bind_wrt_typ_rec_inj : lngen.

(* end hide *)

Lemma close_typ_wrt_typ_inj :
forall A1 A2 X1,
  close_typ_wrt_typ X1 A1 = close_typ_wrt_typ X1 A2 ->
  A1 = A2.
Proof.
unfold close_typ_wrt_typ; eauto with lngen.
Qed.

#[export] Hint Immediate close_typ_wrt_typ_inj : lngen.

Lemma close_bind_wrt_typ_inj :
forall b1 b2 X1,
  close_bind_wrt_typ X1 b1 = close_bind_wrt_typ X1 b2 ->
  b1 = b2.
Proof.
unfold close_bind_wrt_typ; eauto with lngen.
Qed.

#[export] Hint Immediate close_bind_wrt_typ_inj : lngen.

(* begin hide *)

Lemma close_typ_wrt_typ_rec_open_typ_wrt_typ_rec_mutual :
(forall A1 X1 n1,
  X1 `notin` ftvar_in_typ A1 ->
  close_typ_wrt_typ_rec n1 X1 (open_typ_wrt_typ_rec n1 (typ_var_f X1) A1) = A1).
Proof.
apply_mutual_ind typ_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma close_typ_wrt_typ_rec_open_typ_wrt_typ_rec :
forall A1 X1 n1,
  X1 `notin` ftvar_in_typ A1 ->
  close_typ_wrt_typ_rec n1 X1 (open_typ_wrt_typ_rec n1 (typ_var_f X1) A1) = A1.
Proof.
pose proof close_typ_wrt_typ_rec_open_typ_wrt_typ_rec_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve close_typ_wrt_typ_rec_open_typ_wrt_typ_rec : lngen.
#[export] Hint Rewrite close_typ_wrt_typ_rec_open_typ_wrt_typ_rec using solve [auto] : lngen.

(* end hide *)

(* begin hide *)

Lemma close_bind_wrt_typ_rec_open_bind_wrt_typ_rec_mutual :
(forall b1 X1 n1,
  X1 `notin` ftvar_in_bind b1 ->
  close_bind_wrt_typ_rec n1 X1 (open_bind_wrt_typ_rec n1 (typ_var_f X1) b1) = b1).
Proof.
apply_mutual_ind bind_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma close_bind_wrt_typ_rec_open_bind_wrt_typ_rec :
forall b1 X1 n1,
  X1 `notin` ftvar_in_bind b1 ->
  close_bind_wrt_typ_rec n1 X1 (open_bind_wrt_typ_rec n1 (typ_var_f X1) b1) = b1.
Proof.
pose proof close_bind_wrt_typ_rec_open_bind_wrt_typ_rec_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve close_bind_wrt_typ_rec_open_bind_wrt_typ_rec : lngen.
#[export] Hint Rewrite close_bind_wrt_typ_rec_open_bind_wrt_typ_rec using solve [auto] : lngen.

(* end hide *)

Lemma close_typ_wrt_typ_open_typ_wrt_typ :
forall A1 X1,
  X1 `notin` ftvar_in_typ A1 ->
  close_typ_wrt_typ X1 (open_typ_wrt_typ A1 (typ_var_f X1)) = A1.
Proof.
unfold close_typ_wrt_typ; unfold open_typ_wrt_typ; default_simp.
Qed.

#[export] Hint Resolve close_typ_wrt_typ_open_typ_wrt_typ : lngen.
#[export] Hint Rewrite close_typ_wrt_typ_open_typ_wrt_typ using solve [auto] : lngen.

Lemma close_bind_wrt_typ_open_bind_wrt_typ :
forall b1 X1,
  X1 `notin` ftvar_in_bind b1 ->
  close_bind_wrt_typ X1 (open_bind_wrt_typ b1 (typ_var_f X1)) = b1.
Proof.
unfold close_bind_wrt_typ; unfold open_bind_wrt_typ; default_simp.
Qed.

#[export] Hint Resolve close_bind_wrt_typ_open_bind_wrt_typ : lngen.
#[export] Hint Rewrite close_bind_wrt_typ_open_bind_wrt_typ using solve [auto] : lngen.

(* begin hide *)

Lemma open_typ_wrt_typ_rec_close_typ_wrt_typ_rec_mutual :
(forall A1 X1 n1,
  open_typ_wrt_typ_rec n1 (typ_var_f X1) (close_typ_wrt_typ_rec n1 X1 A1) = A1).
Proof.
apply_mutual_ind typ_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma open_typ_wrt_typ_rec_close_typ_wrt_typ_rec :
forall A1 X1 n1,
  open_typ_wrt_typ_rec n1 (typ_var_f X1) (close_typ_wrt_typ_rec n1 X1 A1) = A1.
Proof.
pose proof open_typ_wrt_typ_rec_close_typ_wrt_typ_rec_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve open_typ_wrt_typ_rec_close_typ_wrt_typ_rec : lngen.
#[export] Hint Rewrite open_typ_wrt_typ_rec_close_typ_wrt_typ_rec using solve [auto] : lngen.

(* end hide *)

(* begin hide *)

Lemma open_bind_wrt_typ_rec_close_bind_wrt_typ_rec_mutual :
(forall b1 X1 n1,
  open_bind_wrt_typ_rec n1 (typ_var_f X1) (close_bind_wrt_typ_rec n1 X1 b1) = b1).
Proof.
apply_mutual_ind bind_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma open_bind_wrt_typ_rec_close_bind_wrt_typ_rec :
forall b1 X1 n1,
  open_bind_wrt_typ_rec n1 (typ_var_f X1) (close_bind_wrt_typ_rec n1 X1 b1) = b1.
Proof.
pose proof open_bind_wrt_typ_rec_close_bind_wrt_typ_rec_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve open_bind_wrt_typ_rec_close_bind_wrt_typ_rec : lngen.
#[export] Hint Rewrite open_bind_wrt_typ_rec_close_bind_wrt_typ_rec using solve [auto] : lngen.

(* end hide *)

Lemma open_typ_wrt_typ_close_typ_wrt_typ :
forall A1 X1,
  open_typ_wrt_typ (close_typ_wrt_typ X1 A1) (typ_var_f X1) = A1.
Proof.
unfold close_typ_wrt_typ; unfold open_typ_wrt_typ; default_simp.
Qed.

#[export] Hint Resolve open_typ_wrt_typ_close_typ_wrt_typ : lngen.
#[export] Hint Rewrite open_typ_wrt_typ_close_typ_wrt_typ using solve [auto] : lngen.

Lemma open_bind_wrt_typ_close_bind_wrt_typ :
forall b1 X1,
  open_bind_wrt_typ (close_bind_wrt_typ X1 b1) (typ_var_f X1) = b1.
Proof.
unfold close_bind_wrt_typ; unfold open_bind_wrt_typ; default_simp.
Qed.

#[export] Hint Resolve open_bind_wrt_typ_close_bind_wrt_typ : lngen.
#[export] Hint Rewrite open_bind_wrt_typ_close_bind_wrt_typ using solve [auto] : lngen.

(* begin hide *)

Lemma open_typ_wrt_typ_rec_inj_mutual :
(forall A2 A1 X1 n1,
  X1 `notin` ftvar_in_typ A2 ->
  X1 `notin` ftvar_in_typ A1 ->
  open_typ_wrt_typ_rec n1 (typ_var_f X1) A2 = open_typ_wrt_typ_rec n1 (typ_var_f X1) A1 ->
  A2 = A1).
Proof.
apply_mutual_ind typ_mutind;
intros; match goal with
          | |- _ = ?term => destruct term
        end;
default_simp; eauto with lngen.
Qed.

(* end hide *)

(* begin hide *)

Lemma open_typ_wrt_typ_rec_inj :
forall A2 A1 X1 n1,
  X1 `notin` ftvar_in_typ A2 ->
  X1 `notin` ftvar_in_typ A1 ->
  open_typ_wrt_typ_rec n1 (typ_var_f X1) A2 = open_typ_wrt_typ_rec n1 (typ_var_f X1) A1 ->
  A2 = A1.
Proof.
pose proof open_typ_wrt_typ_rec_inj_mutual as H; intuition eauto.
Qed.

#[export] Hint Immediate open_typ_wrt_typ_rec_inj : lngen.

(* end hide *)

(* begin hide *)

Lemma open_bind_wrt_typ_rec_inj_mutual :
(forall b2 b1 X1 n1,
  X1 `notin` ftvar_in_bind b2 ->
  X1 `notin` ftvar_in_bind b1 ->
  open_bind_wrt_typ_rec n1 (typ_var_f X1) b2 = open_bind_wrt_typ_rec n1 (typ_var_f X1) b1 ->
  b2 = b1).
Proof.
apply_mutual_ind bind_mutind;
intros; match goal with
          | |- _ = ?term => destruct term
        end;
default_simp; eauto with lngen.
Qed.

(* end hide *)

(* begin hide *)

Lemma open_bind_wrt_typ_rec_inj :
forall b2 b1 X1 n1,
  X1 `notin` ftvar_in_bind b2 ->
  X1 `notin` ftvar_in_bind b1 ->
  open_bind_wrt_typ_rec n1 (typ_var_f X1) b2 = open_bind_wrt_typ_rec n1 (typ_var_f X1) b1 ->
  b2 = b1.
Proof.
pose proof open_bind_wrt_typ_rec_inj_mutual as H; intuition eauto.
Qed.

#[export] Hint Immediate open_bind_wrt_typ_rec_inj : lngen.

(* end hide *)

Lemma open_typ_wrt_typ_inj :
forall A2 A1 X1,
  X1 `notin` ftvar_in_typ A2 ->
  X1 `notin` ftvar_in_typ A1 ->
  open_typ_wrt_typ A2 (typ_var_f X1) = open_typ_wrt_typ A1 (typ_var_f X1) ->
  A2 = A1.
Proof.
unfold open_typ_wrt_typ; eauto with lngen.
Qed.

#[export] Hint Immediate open_typ_wrt_typ_inj : lngen.

Lemma open_bind_wrt_typ_inj :
forall b2 b1 X1,
  X1 `notin` ftvar_in_bind b2 ->
  X1 `notin` ftvar_in_bind b1 ->
  open_bind_wrt_typ b2 (typ_var_f X1) = open_bind_wrt_typ b1 (typ_var_f X1) ->
  b2 = b1.
Proof.
unfold open_bind_wrt_typ; eauto with lngen.
Qed.

#[export] Hint Immediate open_bind_wrt_typ_inj : lngen.


(* *********************************************************************** *)
(** * Theorems about [lc] *)

Ltac default_auto ::= auto with lngen brute_force; tauto.
Ltac default_autorewrite ::= autorewrite with lngen.

(* begin hide *)

Lemma degree_typ_wrt_typ_of_lc_typ_mutual :
(forall A1,
  lc_typ A1 ->
  degree_typ_wrt_typ 0 A1).
Proof.
apply_mutual_ind lc_typ_mutind;
intros;
let X1 := fresh "X1" in pick_fresh X1;
repeat (match goal with
          | H1 : _, H2 : _ |- _ => specialize H1 with H2
        end);
default_simp; eauto with lngen.
Qed.

(* end hide *)

Lemma degree_typ_wrt_typ_of_lc_typ :
forall A1,
  lc_typ A1 ->
  degree_typ_wrt_typ 0 A1.
Proof.
pose proof degree_typ_wrt_typ_of_lc_typ_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve degree_typ_wrt_typ_of_lc_typ : lngen.

(* begin hide *)

Lemma degree_bind_wrt_typ_of_lc_bind_mutual :
(forall b1,
  lc_bind b1 ->
  degree_bind_wrt_typ 0 b1).
Proof.
apply_mutual_ind lc_bind_mutind;
intros;
let X1 := fresh "X1" in pick_fresh X1;
repeat (match goal with
          | H1 : _, H2 : _ |- _ => specialize H1 with H2
        end);
default_simp; eauto with lngen.
Qed.

(* end hide *)

Lemma degree_bind_wrt_typ_of_lc_bind :
forall b1,
  lc_bind b1 ->
  degree_bind_wrt_typ 0 b1.
Proof.
pose proof degree_bind_wrt_typ_of_lc_bind_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve degree_bind_wrt_typ_of_lc_bind : lngen.

(* begin hide *)

Lemma lc_typ_of_degree_size_mutual :
forall i1,
(forall A1,
  size_typ A1 = i1 ->
  degree_typ_wrt_typ 0 A1 ->
  lc_typ A1).
Proof.
intros i1; pattern i1; apply lt_wf_rec;
clear i1; intros i1 H1;
apply_mutual_ind typ_mutind;
default_simp;
(* non-trivial cases *)
constructor; default_simp; eapply_first_lt_hyp;
(* instantiate the size *)
match goal with
  | |- _ = _ => reflexivity
  | _ => idtac
end;
instantiate;
(* everything should be easy now *)
default_simp.
Qed.

(* end hide *)

Lemma lc_typ_of_degree :
forall A1,
  degree_typ_wrt_typ 0 A1 ->
  lc_typ A1.
Proof.
intros A1; intros;
pose proof (lc_typ_of_degree_size_mutual (size_typ A1));
intuition eauto.
Qed.

#[export] Hint Resolve lc_typ_of_degree : lngen.

(* begin hide *)

Lemma lc_bind_of_degree_size_mutual :
forall i1,
(forall b1,
  size_bind b1 = i1 ->
  degree_bind_wrt_typ 0 b1 ->
  lc_bind b1).
Proof.
intros i1; pattern i1; apply lt_wf_rec;
clear i1; intros i1 H1;
apply_mutual_ind bind_mutind;
default_simp;
(* non-trivial cases *)
constructor; default_simp; eapply_first_lt_hyp;
(* instantiate the size *)
match goal with
  | |- _ = _ => reflexivity
  | _ => idtac
end;
instantiate;
(* everything should be easy now *)
default_simp.
Qed.

(* end hide *)

Lemma lc_bind_of_degree :
forall b1,
  degree_bind_wrt_typ 0 b1 ->
  lc_bind b1.
Proof.
intros b1; intros;
pose proof (lc_bind_of_degree_size_mutual (size_bind b1));
intuition eauto.
Qed.

#[export] Hint Resolve lc_bind_of_degree : lngen.

Ltac typ_lc_exists_tac :=
  repeat (match goal with
            | H : _ |- _ =>
              let J1 := fresh in pose proof H as J1; apply degree_typ_wrt_typ_of_lc_typ in J1; clear H
          end).

Ltac bind_lc_exists_tac :=
  repeat (match goal with
            | H : _ |- _ =>
              let J1 := fresh in pose proof H as J1; apply degree_bind_wrt_typ_of_lc_bind in J1; clear H
          end).

Ltac counter_lc_exists_tac :=
  repeat (match goal with
            | H : _ |- _ =>
              fail 1
          end).

Lemma lc_typ_all_exists :
forall X1 A1,
  lc_typ (open_typ_wrt_typ A1 (typ_var_f X1)) ->
  lc_typ (typ_all A1).
Proof.
intros; typ_lc_exists_tac; eauto 6 with lngen.
Qed.

#[export] Hint Extern 1 (lc_typ (typ_all _)) =>
  let X1 := fresh in
  pick_fresh X1;
  apply (lc_typ_all_exists X1) : core.

Lemma lc_body_typ_wrt_typ :
forall A1 A2,
  body_typ_wrt_typ A1 ->
  lc_typ A2 ->
  lc_typ (open_typ_wrt_typ A1 A2).
Proof.
unfold body_typ_wrt_typ;
default_simp;
let X1 := fresh "x" in
pick_fresh X1;
specialize_all X1;
typ_lc_exists_tac;
eauto 7 with lngen.
Qed.

#[export] Hint Resolve lc_body_typ_wrt_typ : lngen.

Lemma lc_body_bind_wrt_typ :
forall b1 A1,
  body_bind_wrt_typ b1 ->
  lc_typ A1 ->
  lc_bind (open_bind_wrt_typ b1 A1).
Proof.
unfold body_bind_wrt_typ;
default_simp;
let X1 := fresh "x" in
pick_fresh X1;
specialize_all X1;
bind_lc_exists_tac;
eauto 7 with lngen.
Qed.

#[export] Hint Resolve lc_body_bind_wrt_typ : lngen.

Lemma lc_body_typ_all_1 :
forall A1,
  lc_typ (typ_all A1) ->
  body_typ_wrt_typ A1.
Proof.
default_simp.
Qed.

#[export] Hint Resolve lc_body_typ_all_1 : lngen.

(* begin hide *)

Lemma lc_typ_unique_mutual :
(forall A1 (proof2 proof3 : lc_typ A1), proof2 = proof3).
Proof.
apply_mutual_ind lc_typ_mutind;
intros;
let proof1 := fresh "proof1" in
rename_last_into proof1; dependent destruction proof1;
f_equal; default_simp; auto using @functional_extensionality_dep with lngen.
Qed.

(* end hide *)

Lemma lc_typ_unique :
forall A1 (proof2 proof3 : lc_typ A1), proof2 = proof3.
Proof.
pose proof lc_typ_unique_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve lc_typ_unique : lngen.

(* begin hide *)

Lemma lc_bind_unique_mutual :
(forall b1 (proof2 proof3 : lc_bind b1), proof2 = proof3).
Proof.
apply_mutual_ind lc_bind_mutind;
intros;
let proof1 := fresh "proof1" in
rename_last_into proof1; dependent destruction proof1;
f_equal; default_simp; auto using @functional_extensionality_dep with lngen.
Qed.

(* end hide *)

Lemma lc_bind_unique :
forall b1 (proof2 proof3 : lc_bind b1), proof2 = proof3.
Proof.
pose proof lc_bind_unique_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve lc_bind_unique : lngen.

(* begin hide *)

Lemma lc_typ_of_lc_set_typ_mutual :
(forall A1, lc_set_typ A1 -> lc_typ A1).
Proof.
apply_mutual_ind lc_set_typ_mutind;
default_simp.
Qed.

(* end hide *)

Lemma lc_typ_of_lc_set_typ :
forall A1, lc_set_typ A1 -> lc_typ A1.
Proof.
pose proof lc_typ_of_lc_set_typ_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve lc_typ_of_lc_set_typ : lngen.

(* begin hide *)

Lemma lc_bind_of_lc_set_bind_mutual :
(forall b1, lc_set_bind b1 -> lc_bind b1).
Proof.
apply_mutual_ind lc_set_bind_mutind;
default_simp.
Qed.

(* end hide *)

Lemma lc_bind_of_lc_set_bind :
forall b1, lc_set_bind b1 -> lc_bind b1.
Proof.
pose proof lc_bind_of_lc_set_bind_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve lc_bind_of_lc_set_bind : lngen.

(* begin hide *)

Lemma lc_set_typ_of_lc_typ_size_mutual :
forall i1,
(forall A1,
  size_typ A1 = i1 ->
  lc_typ A1 ->
  lc_set_typ A1).
Proof.
intros i1; pattern i1; apply lt_wf_rec;
clear i1; intros i1 H1;
apply_mutual_ind typ_mutrec;
default_simp;
try solve [assert False by default_simp; tauto];
(* non-trivial cases *)
constructor; default_simp;
try first [apply lc_set_typ_of_lc_typ];
default_simp; eapply_first_lt_hyp;
(* instantiate the size *)
match goal with
  | |- _ = _ => reflexivity
  | _ => idtac
end;
instantiate;
(* everything should be easy now *)
default_simp.
Qed.

(* end hide *)

Lemma lc_set_typ_of_lc_typ :
forall A1,
  lc_typ A1 ->
  lc_set_typ A1.
Proof.
intros A1; intros;
pose proof (lc_set_typ_of_lc_typ_size_mutual (size_typ A1));
intuition eauto.
Qed.

#[export] Hint Resolve lc_set_typ_of_lc_typ : lngen.

(* begin hide *)

Lemma lc_set_bind_of_lc_bind_size_mutual :
forall i1,
(forall b1,
  size_bind b1 = i1 ->
  lc_bind b1 ->
  lc_set_bind b1).
Proof.
intros i1; pattern i1; apply lt_wf_rec;
clear i1; intros i1 H1;
apply_mutual_ind bind_mutrec;
default_simp;
try solve [assert False by default_simp; tauto];
(* non-trivial cases *)
constructor; default_simp;
try first [apply lc_set_typ_of_lc_typ
 | apply lc_set_bind_of_lc_bind];
default_simp; eapply_first_lt_hyp;
(* instantiate the size *)
match goal with
  | |- _ = _ => reflexivity
  | _ => idtac
end;
instantiate;
(* everything should be easy now *)
default_simp.
Qed.

(* end hide *)

Lemma lc_set_bind_of_lc_bind :
forall b1,
  lc_bind b1 ->
  lc_set_bind b1.
Proof.
intros b1; intros;
pose proof (lc_set_bind_of_lc_bind_size_mutual (size_bind b1));
intuition eauto.
Qed.

#[export] Hint Resolve lc_set_bind_of_lc_bind : lngen.


(* *********************************************************************** *)
(** * More theorems about [open] and [close] *)

Ltac default_auto ::= auto with lngen; tauto.
Ltac default_autorewrite ::= fail.

(* begin hide *)

Lemma close_typ_wrt_typ_rec_degree_typ_wrt_typ_mutual :
(forall A1 X1 n1,
  degree_typ_wrt_typ n1 A1 ->
  X1 `notin` ftvar_in_typ A1 ->
  close_typ_wrt_typ_rec n1 X1 A1 = A1).
Proof.
apply_mutual_ind typ_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma close_typ_wrt_typ_rec_degree_typ_wrt_typ :
forall A1 X1 n1,
  degree_typ_wrt_typ n1 A1 ->
  X1 `notin` ftvar_in_typ A1 ->
  close_typ_wrt_typ_rec n1 X1 A1 = A1.
Proof.
pose proof close_typ_wrt_typ_rec_degree_typ_wrt_typ_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve close_typ_wrt_typ_rec_degree_typ_wrt_typ : lngen.
#[export] Hint Rewrite close_typ_wrt_typ_rec_degree_typ_wrt_typ using solve [auto] : lngen.

(* end hide *)

(* begin hide *)

Lemma close_bind_wrt_typ_rec_degree_bind_wrt_typ_mutual :
(forall b1 X1 n1,
  degree_bind_wrt_typ n1 b1 ->
  X1 `notin` ftvar_in_bind b1 ->
  close_bind_wrt_typ_rec n1 X1 b1 = b1).
Proof.
apply_mutual_ind bind_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma close_bind_wrt_typ_rec_degree_bind_wrt_typ :
forall b1 X1 n1,
  degree_bind_wrt_typ n1 b1 ->
  X1 `notin` ftvar_in_bind b1 ->
  close_bind_wrt_typ_rec n1 X1 b1 = b1.
Proof.
pose proof close_bind_wrt_typ_rec_degree_bind_wrt_typ_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve close_bind_wrt_typ_rec_degree_bind_wrt_typ : lngen.
#[export] Hint Rewrite close_bind_wrt_typ_rec_degree_bind_wrt_typ using solve [auto] : lngen.

(* end hide *)

Lemma close_typ_wrt_typ_lc_typ :
forall A1 X1,
  lc_typ A1 ->
  X1 `notin` ftvar_in_typ A1 ->
  close_typ_wrt_typ X1 A1 = A1.
Proof.
unfold close_typ_wrt_typ; default_simp.
Qed.

#[export] Hint Resolve close_typ_wrt_typ_lc_typ : lngen.
#[export] Hint Rewrite close_typ_wrt_typ_lc_typ using solve [auto] : lngen.

Lemma close_bind_wrt_typ_lc_bind :
forall b1 X1,
  lc_bind b1 ->
  X1 `notin` ftvar_in_bind b1 ->
  close_bind_wrt_typ X1 b1 = b1.
Proof.
unfold close_bind_wrt_typ; default_simp.
Qed.

#[export] Hint Resolve close_bind_wrt_typ_lc_bind : lngen.
#[export] Hint Rewrite close_bind_wrt_typ_lc_bind using solve [auto] : lngen.

(* begin hide *)

Lemma open_typ_wrt_typ_rec_degree_typ_wrt_typ_mutual :
(forall A2 A1 n1,
  degree_typ_wrt_typ n1 A2 ->
  open_typ_wrt_typ_rec n1 A1 A2 = A2).
Proof.
apply_mutual_ind typ_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma open_typ_wrt_typ_rec_degree_typ_wrt_typ :
forall A2 A1 n1,
  degree_typ_wrt_typ n1 A2 ->
  open_typ_wrt_typ_rec n1 A1 A2 = A2.
Proof.
pose proof open_typ_wrt_typ_rec_degree_typ_wrt_typ_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve open_typ_wrt_typ_rec_degree_typ_wrt_typ : lngen.
#[export] Hint Rewrite open_typ_wrt_typ_rec_degree_typ_wrt_typ using solve [auto] : lngen.

(* end hide *)

(* begin hide *)

Lemma open_bind_wrt_typ_rec_degree_bind_wrt_typ_mutual :
(forall b1 A1 n1,
  degree_bind_wrt_typ n1 b1 ->
  open_bind_wrt_typ_rec n1 A1 b1 = b1).
Proof.
apply_mutual_ind bind_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma open_bind_wrt_typ_rec_degree_bind_wrt_typ :
forall b1 A1 n1,
  degree_bind_wrt_typ n1 b1 ->
  open_bind_wrt_typ_rec n1 A1 b1 = b1.
Proof.
pose proof open_bind_wrt_typ_rec_degree_bind_wrt_typ_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve open_bind_wrt_typ_rec_degree_bind_wrt_typ : lngen.
#[export] Hint Rewrite open_bind_wrt_typ_rec_degree_bind_wrt_typ using solve [auto] : lngen.

(* end hide *)

Lemma open_typ_wrt_typ_lc_typ :
forall A2 A1,
  lc_typ A2 ->
  open_typ_wrt_typ A2 A1 = A2.
Proof.
unfold open_typ_wrt_typ; default_simp.
Qed.

#[export] Hint Resolve open_typ_wrt_typ_lc_typ : lngen.
#[export] Hint Rewrite open_typ_wrt_typ_lc_typ using solve [auto] : lngen.

Lemma open_bind_wrt_typ_lc_bind :
forall b1 A1,
  lc_bind b1 ->
  open_bind_wrt_typ b1 A1 = b1.
Proof.
unfold open_bind_wrt_typ; default_simp.
Qed.

#[export] Hint Resolve open_bind_wrt_typ_lc_bind : lngen.
#[export] Hint Rewrite open_bind_wrt_typ_lc_bind using solve [auto] : lngen.


(* *********************************************************************** *)
(** * Theorems about [fv] *)

Ltac default_auto ::= auto with set lngen; tauto.
Ltac default_autorewrite ::= autorewrite with lngen.

(* begin hide *)

Lemma ftvar_in_typ_close_typ_wrt_typ_rec_mutual :
(forall A1 X1 n1,
  ftvar_in_typ (close_typ_wrt_typ_rec n1 X1 A1) [=] remove X1 (ftvar_in_typ A1)).
Proof.
apply_mutual_ind typ_mutind;
default_simp; fsetdec.
Qed.

(* end hide *)

(* begin hide *)

Lemma ftvar_in_typ_close_typ_wrt_typ_rec :
forall A1 X1 n1,
  ftvar_in_typ (close_typ_wrt_typ_rec n1 X1 A1) [=] remove X1 (ftvar_in_typ A1).
Proof.
pose proof ftvar_in_typ_close_typ_wrt_typ_rec_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve ftvar_in_typ_close_typ_wrt_typ_rec : lngen.
#[export] Hint Rewrite ftvar_in_typ_close_typ_wrt_typ_rec using solve [auto] : lngen.

(* end hide *)

(* begin hide *)

Lemma ftvar_in_bind_close_bind_wrt_typ_rec_mutual :
(forall b1 X1 n1,
  ftvar_in_bind (close_bind_wrt_typ_rec n1 X1 b1) [=] remove X1 (ftvar_in_bind b1)).
Proof.
apply_mutual_ind bind_mutind;
default_simp; fsetdec.
Qed.

(* end hide *)

(* begin hide *)

Lemma ftvar_in_bind_close_bind_wrt_typ_rec :
forall b1 X1 n1,
  ftvar_in_bind (close_bind_wrt_typ_rec n1 X1 b1) [=] remove X1 (ftvar_in_bind b1).
Proof.
pose proof ftvar_in_bind_close_bind_wrt_typ_rec_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve ftvar_in_bind_close_bind_wrt_typ_rec : lngen.
#[export] Hint Rewrite ftvar_in_bind_close_bind_wrt_typ_rec using solve [auto] : lngen.

(* end hide *)

Lemma ftvar_in_typ_close_typ_wrt_typ :
forall A1 X1,
  ftvar_in_typ (close_typ_wrt_typ X1 A1) [=] remove X1 (ftvar_in_typ A1).
Proof.
unfold close_typ_wrt_typ; default_simp.
Qed.

#[export] Hint Resolve ftvar_in_typ_close_typ_wrt_typ : lngen.
#[export] Hint Rewrite ftvar_in_typ_close_typ_wrt_typ using solve [auto] : lngen.

Lemma ftvar_in_bind_close_bind_wrt_typ :
forall b1 X1,
  ftvar_in_bind (close_bind_wrt_typ X1 b1) [=] remove X1 (ftvar_in_bind b1).
Proof.
unfold close_bind_wrt_typ; default_simp.
Qed.

#[export] Hint Resolve ftvar_in_bind_close_bind_wrt_typ : lngen.
#[export] Hint Rewrite ftvar_in_bind_close_bind_wrt_typ using solve [auto] : lngen.

(* begin hide *)

Lemma ftvar_in_typ_open_typ_wrt_typ_rec_lower_mutual :
(forall A1 A2 n1,
  ftvar_in_typ A1 [<=] ftvar_in_typ (open_typ_wrt_typ_rec n1 A2 A1)).
Proof.
apply_mutual_ind typ_mutind;
default_simp; fsetdec.
Qed.

(* end hide *)

(* begin hide *)

Lemma ftvar_in_typ_open_typ_wrt_typ_rec_lower :
forall A1 A2 n1,
  ftvar_in_typ A1 [<=] ftvar_in_typ (open_typ_wrt_typ_rec n1 A2 A1).
Proof.
pose proof ftvar_in_typ_open_typ_wrt_typ_rec_lower_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve ftvar_in_typ_open_typ_wrt_typ_rec_lower : lngen.

(* end hide *)

(* begin hide *)

Lemma ftvar_in_bind_open_bind_wrt_typ_rec_lower_mutual :
(forall b1 A1 n1,
  ftvar_in_bind b1 [<=] ftvar_in_bind (open_bind_wrt_typ_rec n1 A1 b1)).
Proof.
apply_mutual_ind bind_mutind;
default_simp; fsetdec.
Qed.

(* end hide *)

(* begin hide *)

Lemma ftvar_in_bind_open_bind_wrt_typ_rec_lower :
forall b1 A1 n1,
  ftvar_in_bind b1 [<=] ftvar_in_bind (open_bind_wrt_typ_rec n1 A1 b1).
Proof.
pose proof ftvar_in_bind_open_bind_wrt_typ_rec_lower_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve ftvar_in_bind_open_bind_wrt_typ_rec_lower : lngen.

(* end hide *)

Lemma ftvar_in_typ_open_typ_wrt_typ_lower :
forall A1 A2,
  ftvar_in_typ A1 [<=] ftvar_in_typ (open_typ_wrt_typ A1 A2).
Proof.
unfold open_typ_wrt_typ; default_simp.
Qed.

#[export] Hint Resolve ftvar_in_typ_open_typ_wrt_typ_lower : lngen.

Lemma ftvar_in_bind_open_bind_wrt_typ_lower :
forall b1 A1,
  ftvar_in_bind b1 [<=] ftvar_in_bind (open_bind_wrt_typ b1 A1).
Proof.
unfold open_bind_wrt_typ; default_simp.
Qed.

#[export] Hint Resolve ftvar_in_bind_open_bind_wrt_typ_lower : lngen.

(* begin hide *)

Lemma ftvar_in_typ_open_typ_wrt_typ_rec_upper_mutual :
(forall A1 A2 n1,
  ftvar_in_typ (open_typ_wrt_typ_rec n1 A2 A1) [<=] ftvar_in_typ A2 `union` ftvar_in_typ A1).
Proof.
apply_mutual_ind typ_mutind;
default_simp; fsetdec.
Qed.

(* end hide *)

(* begin hide *)

Lemma ftvar_in_typ_open_typ_wrt_typ_rec_upper :
forall A1 A2 n1,
  ftvar_in_typ (open_typ_wrt_typ_rec n1 A2 A1) [<=] ftvar_in_typ A2 `union` ftvar_in_typ A1.
Proof.
pose proof ftvar_in_typ_open_typ_wrt_typ_rec_upper_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve ftvar_in_typ_open_typ_wrt_typ_rec_upper : lngen.

(* end hide *)

(* begin hide *)

Lemma ftvar_in_bind_open_bind_wrt_typ_rec_upper_mutual :
(forall b1 A1 n1,
  ftvar_in_bind (open_bind_wrt_typ_rec n1 A1 b1) [<=] ftvar_in_typ A1 `union` ftvar_in_bind b1).
Proof.
apply_mutual_ind bind_mutind;
default_simp; fsetdec.
Qed.

(* end hide *)

(* begin hide *)

Lemma ftvar_in_bind_open_bind_wrt_typ_rec_upper :
forall b1 A1 n1,
  ftvar_in_bind (open_bind_wrt_typ_rec n1 A1 b1) [<=] ftvar_in_typ A1 `union` ftvar_in_bind b1.
Proof.
pose proof ftvar_in_bind_open_bind_wrt_typ_rec_upper_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve ftvar_in_bind_open_bind_wrt_typ_rec_upper : lngen.

(* end hide *)

Lemma ftvar_in_typ_open_typ_wrt_typ_upper :
forall A1 A2,
  ftvar_in_typ (open_typ_wrt_typ A1 A2) [<=] ftvar_in_typ A2 `union` ftvar_in_typ A1.
Proof.
unfold open_typ_wrt_typ; default_simp.
Qed.

#[export] Hint Resolve ftvar_in_typ_open_typ_wrt_typ_upper : lngen.

Lemma ftvar_in_bind_open_bind_wrt_typ_upper :
forall b1 A1,
  ftvar_in_bind (open_bind_wrt_typ b1 A1) [<=] ftvar_in_typ A1 `union` ftvar_in_bind b1.
Proof.
unfold open_bind_wrt_typ; default_simp.
Qed.

#[export] Hint Resolve ftvar_in_bind_open_bind_wrt_typ_upper : lngen.

(* begin hide *)

Lemma ftvar_in_typ_subst_tvar_in_typ_fresh_mutual :
(forall A1 A2 X1,
  X1 `notin` ftvar_in_typ A1 ->
  ftvar_in_typ (subst_tvar_in_typ A2 X1 A1) [=] ftvar_in_typ A1).
Proof.
apply_mutual_ind typ_mutind;
default_simp; fsetdec.
Qed.

(* end hide *)

Lemma ftvar_in_typ_subst_tvar_in_typ_fresh :
forall A1 A2 X1,
  X1 `notin` ftvar_in_typ A1 ->
  ftvar_in_typ (subst_tvar_in_typ A2 X1 A1) [=] ftvar_in_typ A1.
Proof.
pose proof ftvar_in_typ_subst_tvar_in_typ_fresh_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve ftvar_in_typ_subst_tvar_in_typ_fresh : lngen.
#[export] Hint Rewrite ftvar_in_typ_subst_tvar_in_typ_fresh using solve [auto] : lngen.

(* begin hide *)

Lemma ftvar_in_bind_subst_tvar_in_bind_fresh_mutual :
(forall b1 A1 X1,
  X1 `notin` ftvar_in_bind b1 ->
  ftvar_in_bind (subst_tvar_in_bind A1 X1 b1) [=] ftvar_in_bind b1).
Proof.
apply_mutual_ind bind_mutind;
default_simp; fsetdec.
Qed.

(* end hide *)

Lemma ftvar_in_bind_subst_tvar_in_bind_fresh :
forall b1 A1 X1,
  X1 `notin` ftvar_in_bind b1 ->
  ftvar_in_bind (subst_tvar_in_bind A1 X1 b1) [=] ftvar_in_bind b1.
Proof.
pose proof ftvar_in_bind_subst_tvar_in_bind_fresh_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve ftvar_in_bind_subst_tvar_in_bind_fresh : lngen.
#[export] Hint Rewrite ftvar_in_bind_subst_tvar_in_bind_fresh using solve [auto] : lngen.

(* begin hide *)

Lemma ftvar_in_typ_subst_tvar_in_typ_lower_mutual :
(forall A1 A2 X1,
  remove X1 (ftvar_in_typ A1) [<=] ftvar_in_typ (subst_tvar_in_typ A2 X1 A1)).
Proof.
apply_mutual_ind typ_mutind;
default_simp; fsetdec.
Qed.

(* end hide *)

Lemma ftvar_in_typ_subst_tvar_in_typ_lower :
forall A1 A2 X1,
  remove X1 (ftvar_in_typ A1) [<=] ftvar_in_typ (subst_tvar_in_typ A2 X1 A1).
Proof.
pose proof ftvar_in_typ_subst_tvar_in_typ_lower_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve ftvar_in_typ_subst_tvar_in_typ_lower : lngen.

(* begin hide *)

Lemma ftvar_in_bind_subst_tvar_in_bind_lower_mutual :
(forall b1 A1 X1,
  remove X1 (ftvar_in_bind b1) [<=] ftvar_in_bind (subst_tvar_in_bind A1 X1 b1)).
Proof.
apply_mutual_ind bind_mutind;
default_simp; fsetdec.
Qed.

(* end hide *)

Lemma ftvar_in_bind_subst_tvar_in_bind_lower :
forall b1 A1 X1,
  remove X1 (ftvar_in_bind b1) [<=] ftvar_in_bind (subst_tvar_in_bind A1 X1 b1).
Proof.
pose proof ftvar_in_bind_subst_tvar_in_bind_lower_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve ftvar_in_bind_subst_tvar_in_bind_lower : lngen.

(* begin hide *)

Lemma ftvar_in_typ_subst_tvar_in_typ_notin_mutual :
(forall A1 A2 X1 X2,
  X2 `notin` ftvar_in_typ A1 ->
  X2 `notin` ftvar_in_typ A2 ->
  X2 `notin` ftvar_in_typ (subst_tvar_in_typ A2 X1 A1)).
Proof.
apply_mutual_ind typ_mutind;
default_simp; fsetdec.
Qed.

(* end hide *)

Lemma ftvar_in_typ_subst_tvar_in_typ_notin :
forall A1 A2 X1 X2,
  X2 `notin` ftvar_in_typ A1 ->
  X2 `notin` ftvar_in_typ A2 ->
  X2 `notin` ftvar_in_typ (subst_tvar_in_typ A2 X1 A1).
Proof.
pose proof ftvar_in_typ_subst_tvar_in_typ_notin_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve ftvar_in_typ_subst_tvar_in_typ_notin : lngen.

(* begin hide *)

Lemma ftvar_in_bind_subst_tvar_in_bind_notin_mutual :
(forall b1 A1 X1 X2,
  X2 `notin` ftvar_in_bind b1 ->
  X2 `notin` ftvar_in_typ A1 ->
  X2 `notin` ftvar_in_bind (subst_tvar_in_bind A1 X1 b1)).
Proof.
apply_mutual_ind bind_mutind;
default_simp; fsetdec.
Qed.

(* end hide *)

Lemma ftvar_in_bind_subst_tvar_in_bind_notin :
forall b1 A1 X1 X2,
  X2 `notin` ftvar_in_bind b1 ->
  X2 `notin` ftvar_in_typ A1 ->
  X2 `notin` ftvar_in_bind (subst_tvar_in_bind A1 X1 b1).
Proof.
pose proof ftvar_in_bind_subst_tvar_in_bind_notin_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve ftvar_in_bind_subst_tvar_in_bind_notin : lngen.

(* begin hide *)

Lemma ftvar_in_typ_subst_tvar_in_typ_upper_mutual :
(forall A1 A2 X1,
  ftvar_in_typ (subst_tvar_in_typ A2 X1 A1) [<=] ftvar_in_typ A2 `union` remove X1 (ftvar_in_typ A1)).
Proof.
apply_mutual_ind typ_mutind;
default_simp; fsetdec.
Qed.

(* end hide *)

Lemma ftvar_in_typ_subst_tvar_in_typ_upper :
forall A1 A2 X1,
  ftvar_in_typ (subst_tvar_in_typ A2 X1 A1) [<=] ftvar_in_typ A2 `union` remove X1 (ftvar_in_typ A1).
Proof.
pose proof ftvar_in_typ_subst_tvar_in_typ_upper_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve ftvar_in_typ_subst_tvar_in_typ_upper : lngen.

(* begin hide *)

Lemma ftvar_in_bind_subst_tvar_in_bind_upper_mutual :
(forall b1 A1 X1,
  ftvar_in_bind (subst_tvar_in_bind A1 X1 b1) [<=] ftvar_in_typ A1 `union` remove X1 (ftvar_in_bind b1)).
Proof.
apply_mutual_ind bind_mutind;
default_simp; fsetdec.
Qed.

(* end hide *)

Lemma ftvar_in_bind_subst_tvar_in_bind_upper :
forall b1 A1 X1,
  ftvar_in_bind (subst_tvar_in_bind A1 X1 b1) [<=] ftvar_in_typ A1 `union` remove X1 (ftvar_in_bind b1).
Proof.
pose proof ftvar_in_bind_subst_tvar_in_bind_upper_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve ftvar_in_bind_subst_tvar_in_bind_upper : lngen.


(* *********************************************************************** *)
(** * Theorems about [subst] *)

Ltac default_auto ::= auto with lngen brute_force; tauto.
Ltac default_autorewrite ::= autorewrite with lngen.

(* begin hide *)

Lemma subst_tvar_in_typ_close_typ_wrt_typ_rec_mutual :
(forall A2 A1 X1 X2 n1,
  degree_typ_wrt_typ n1 A1 ->
  X1 <> X2 ->
  X2 `notin` ftvar_in_typ A1 ->
  subst_tvar_in_typ A1 X1 (close_typ_wrt_typ_rec n1 X2 A2) = close_typ_wrt_typ_rec n1 X2 (subst_tvar_in_typ A1 X1 A2)).
Proof.
apply_mutual_ind typ_mutind;
default_simp.
Qed.

(* end hide *)

Lemma subst_tvar_in_typ_close_typ_wrt_typ_rec :
forall A2 A1 X1 X2 n1,
  degree_typ_wrt_typ n1 A1 ->
  X1 <> X2 ->
  X2 `notin` ftvar_in_typ A1 ->
  subst_tvar_in_typ A1 X1 (close_typ_wrt_typ_rec n1 X2 A2) = close_typ_wrt_typ_rec n1 X2 (subst_tvar_in_typ A1 X1 A2).
Proof.
pose proof subst_tvar_in_typ_close_typ_wrt_typ_rec_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve subst_tvar_in_typ_close_typ_wrt_typ_rec : lngen.

(* begin hide *)

Lemma subst_tvar_in_bind_close_bind_wrt_typ_rec_mutual :
(forall b1 A1 X1 X2 n1,
  degree_typ_wrt_typ n1 A1 ->
  X1 <> X2 ->
  X2 `notin` ftvar_in_typ A1 ->
  subst_tvar_in_bind A1 X1 (close_bind_wrt_typ_rec n1 X2 b1) = close_bind_wrt_typ_rec n1 X2 (subst_tvar_in_bind A1 X1 b1)).
Proof.
apply_mutual_ind bind_mutind;
default_simp.
Qed.

(* end hide *)

Lemma subst_tvar_in_bind_close_bind_wrt_typ_rec :
forall b1 A1 X1 X2 n1,
  degree_typ_wrt_typ n1 A1 ->
  X1 <> X2 ->
  X2 `notin` ftvar_in_typ A1 ->
  subst_tvar_in_bind A1 X1 (close_bind_wrt_typ_rec n1 X2 b1) = close_bind_wrt_typ_rec n1 X2 (subst_tvar_in_bind A1 X1 b1).
Proof.
pose proof subst_tvar_in_bind_close_bind_wrt_typ_rec_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve subst_tvar_in_bind_close_bind_wrt_typ_rec : lngen.

Lemma subst_tvar_in_typ_close_typ_wrt_typ :
forall A2 A1 X1 X2,
  lc_typ A1 ->  X1 <> X2 ->
  X2 `notin` ftvar_in_typ A1 ->
  subst_tvar_in_typ A1 X1 (close_typ_wrt_typ X2 A2) = close_typ_wrt_typ X2 (subst_tvar_in_typ A1 X1 A2).
Proof.
unfold close_typ_wrt_typ; default_simp.
Qed.

#[export] Hint Resolve subst_tvar_in_typ_close_typ_wrt_typ : lngen.

Lemma subst_tvar_in_bind_close_bind_wrt_typ :
forall b1 A1 X1 X2,
  lc_typ A1 ->  X1 <> X2 ->
  X2 `notin` ftvar_in_typ A1 ->
  subst_tvar_in_bind A1 X1 (close_bind_wrt_typ X2 b1) = close_bind_wrt_typ X2 (subst_tvar_in_bind A1 X1 b1).
Proof.
unfold close_bind_wrt_typ; default_simp.
Qed.

#[export] Hint Resolve subst_tvar_in_bind_close_bind_wrt_typ : lngen.

(* begin hide *)

Lemma subst_tvar_in_typ_degree_typ_wrt_typ_mutual :
(forall A1 A2 X1 n1,
  degree_typ_wrt_typ n1 A1 ->
  degree_typ_wrt_typ n1 A2 ->
  degree_typ_wrt_typ n1 (subst_tvar_in_typ A2 X1 A1)).
Proof.
apply_mutual_ind typ_mutind;
default_simp.
Qed.

(* end hide *)

Lemma subst_tvar_in_typ_degree_typ_wrt_typ :
forall A1 A2 X1 n1,
  degree_typ_wrt_typ n1 A1 ->
  degree_typ_wrt_typ n1 A2 ->
  degree_typ_wrt_typ n1 (subst_tvar_in_typ A2 X1 A1).
Proof.
pose proof subst_tvar_in_typ_degree_typ_wrt_typ_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve subst_tvar_in_typ_degree_typ_wrt_typ : lngen.

(* begin hide *)

Lemma subst_tvar_in_bind_degree_bind_wrt_typ_mutual :
(forall b1 A1 X1 n1,
  degree_bind_wrt_typ n1 b1 ->
  degree_typ_wrt_typ n1 A1 ->
  degree_bind_wrt_typ n1 (subst_tvar_in_bind A1 X1 b1)).
Proof.
apply_mutual_ind bind_mutind;
default_simp.
Qed.

(* end hide *)

Lemma subst_tvar_in_bind_degree_bind_wrt_typ :
forall b1 A1 X1 n1,
  degree_bind_wrt_typ n1 b1 ->
  degree_typ_wrt_typ n1 A1 ->
  degree_bind_wrt_typ n1 (subst_tvar_in_bind A1 X1 b1).
Proof.
pose proof subst_tvar_in_bind_degree_bind_wrt_typ_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve subst_tvar_in_bind_degree_bind_wrt_typ : lngen.

(* begin hide *)

Lemma subst_tvar_in_typ_fresh_eq_mutual :
(forall A2 A1 X1,
  X1 `notin` ftvar_in_typ A2 ->
  subst_tvar_in_typ A1 X1 A2 = A2).
Proof.
apply_mutual_ind typ_mutind;
default_simp.
Qed.

(* end hide *)

Lemma subst_tvar_in_typ_fresh_eq :
forall A2 A1 X1,
  X1 `notin` ftvar_in_typ A2 ->
  subst_tvar_in_typ A1 X1 A2 = A2.
Proof.
pose proof subst_tvar_in_typ_fresh_eq_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve subst_tvar_in_typ_fresh_eq : lngen.
#[export] Hint Rewrite subst_tvar_in_typ_fresh_eq using solve [auto] : lngen.

(* begin hide *)

Lemma subst_tvar_in_bind_fresh_eq_mutual :
(forall b1 A1 X1,
  X1 `notin` ftvar_in_bind b1 ->
  subst_tvar_in_bind A1 X1 b1 = b1).
Proof.
apply_mutual_ind bind_mutind;
default_simp.
Qed.

(* end hide *)

Lemma subst_tvar_in_bind_fresh_eq :
forall b1 A1 X1,
  X1 `notin` ftvar_in_bind b1 ->
  subst_tvar_in_bind A1 X1 b1 = b1.
Proof.
pose proof subst_tvar_in_bind_fresh_eq_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve subst_tvar_in_bind_fresh_eq : lngen.
#[export] Hint Rewrite subst_tvar_in_bind_fresh_eq using solve [auto] : lngen.

(* begin hide *)

Lemma subst_tvar_in_typ_fresh_same_mutual :
(forall A2 A1 X1,
  X1 `notin` ftvar_in_typ A1 ->
  X1 `notin` ftvar_in_typ (subst_tvar_in_typ A1 X1 A2)).
Proof.
apply_mutual_ind typ_mutind;
default_simp.
Qed.

(* end hide *)

Lemma subst_tvar_in_typ_fresh_same :
forall A2 A1 X1,
  X1 `notin` ftvar_in_typ A1 ->
  X1 `notin` ftvar_in_typ (subst_tvar_in_typ A1 X1 A2).
Proof.
pose proof subst_tvar_in_typ_fresh_same_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve subst_tvar_in_typ_fresh_same : lngen.

(* begin hide *)

Lemma subst_tvar_in_bind_fresh_same_mutual :
(forall b1 A1 X1,
  X1 `notin` ftvar_in_typ A1 ->
  X1 `notin` ftvar_in_bind (subst_tvar_in_bind A1 X1 b1)).
Proof.
apply_mutual_ind bind_mutind;
default_simp.
Qed.

(* end hide *)

Lemma subst_tvar_in_bind_fresh_same :
forall b1 A1 X1,
  X1 `notin` ftvar_in_typ A1 ->
  X1 `notin` ftvar_in_bind (subst_tvar_in_bind A1 X1 b1).
Proof.
pose proof subst_tvar_in_bind_fresh_same_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve subst_tvar_in_bind_fresh_same : lngen.

(* begin hide *)

Lemma subst_tvar_in_typ_fresh_mutual :
(forall A2 A1 X1 X2,
  X1 `notin` ftvar_in_typ A2 ->
  X1 `notin` ftvar_in_typ A1 ->
  X1 `notin` ftvar_in_typ (subst_tvar_in_typ A1 X2 A2)).
Proof.
apply_mutual_ind typ_mutind;
default_simp.
Qed.

(* end hide *)

Lemma subst_tvar_in_typ_fresh :
forall A2 A1 X1 X2,
  X1 `notin` ftvar_in_typ A2 ->
  X1 `notin` ftvar_in_typ A1 ->
  X1 `notin` ftvar_in_typ (subst_tvar_in_typ A1 X2 A2).
Proof.
pose proof subst_tvar_in_typ_fresh_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve subst_tvar_in_typ_fresh : lngen.

(* begin hide *)

Lemma subst_tvar_in_bind_fresh_mutual :
(forall b1 A1 X1 X2,
  X1 `notin` ftvar_in_bind b1 ->
  X1 `notin` ftvar_in_typ A1 ->
  X1 `notin` ftvar_in_bind (subst_tvar_in_bind A1 X2 b1)).
Proof.
apply_mutual_ind bind_mutind;
default_simp.
Qed.

(* end hide *)

Lemma subst_tvar_in_bind_fresh :
forall b1 A1 X1 X2,
  X1 `notin` ftvar_in_bind b1 ->
  X1 `notin` ftvar_in_typ A1 ->
  X1 `notin` ftvar_in_bind (subst_tvar_in_bind A1 X2 b1).
Proof.
pose proof subst_tvar_in_bind_fresh_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve subst_tvar_in_bind_fresh : lngen.

Lemma subst_tvar_in_typ_lc_typ :
forall A1 A2 X1,
  lc_typ A1 ->
  lc_typ A2 ->
  lc_typ (subst_tvar_in_typ A2 X1 A1).
Proof.
default_simp.
Qed.

#[export] Hint Resolve subst_tvar_in_typ_lc_typ : lngen.

Lemma subst_tvar_in_bind_lc_bind :
forall b1 A1 X1,
  lc_bind b1 ->
  lc_typ A1 ->
  lc_bind (subst_tvar_in_bind A1 X1 b1).
Proof.
default_simp.
Qed.

#[export] Hint Resolve subst_tvar_in_bind_lc_bind : lngen.

(* begin hide *)

Lemma subst_tvar_in_typ_open_typ_wrt_typ_rec_mutual :
(forall A3 A1 A2 X1 n1,
  lc_typ A1 ->
  subst_tvar_in_typ A1 X1 (open_typ_wrt_typ_rec n1 A2 A3) = open_typ_wrt_typ_rec n1 (subst_tvar_in_typ A1 X1 A2) (subst_tvar_in_typ A1 X1 A3)).
Proof.
apply_mutual_ind typ_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma subst_tvar_in_typ_open_typ_wrt_typ_rec :
forall A3 A1 A2 X1 n1,
  lc_typ A1 ->
  subst_tvar_in_typ A1 X1 (open_typ_wrt_typ_rec n1 A2 A3) = open_typ_wrt_typ_rec n1 (subst_tvar_in_typ A1 X1 A2) (subst_tvar_in_typ A1 X1 A3).
Proof.
pose proof subst_tvar_in_typ_open_typ_wrt_typ_rec_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve subst_tvar_in_typ_open_typ_wrt_typ_rec : lngen.

(* end hide *)

(* begin hide *)

Lemma subst_tvar_in_bind_open_bind_wrt_typ_rec_mutual :
(forall b1 A1 A2 X1 n1,
  lc_typ A1 ->
  subst_tvar_in_bind A1 X1 (open_bind_wrt_typ_rec n1 A2 b1) = open_bind_wrt_typ_rec n1 (subst_tvar_in_typ A1 X1 A2) (subst_tvar_in_bind A1 X1 b1)).
Proof.
apply_mutual_ind bind_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma subst_tvar_in_bind_open_bind_wrt_typ_rec :
forall b1 A1 A2 X1 n1,
  lc_typ A1 ->
  subst_tvar_in_bind A1 X1 (open_bind_wrt_typ_rec n1 A2 b1) = open_bind_wrt_typ_rec n1 (subst_tvar_in_typ A1 X1 A2) (subst_tvar_in_bind A1 X1 b1).
Proof.
pose proof subst_tvar_in_bind_open_bind_wrt_typ_rec_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve subst_tvar_in_bind_open_bind_wrt_typ_rec : lngen.

(* end hide *)

Lemma subst_tvar_in_typ_open_typ_wrt_typ :
forall A3 A1 A2 X1,
  lc_typ A1 ->
  subst_tvar_in_typ A1 X1 (open_typ_wrt_typ A3 A2) = open_typ_wrt_typ (subst_tvar_in_typ A1 X1 A3) (subst_tvar_in_typ A1 X1 A2).
Proof.
unfold open_typ_wrt_typ; default_simp.
Qed.

#[export] Hint Resolve subst_tvar_in_typ_open_typ_wrt_typ : lngen.

Lemma subst_tvar_in_bind_open_bind_wrt_typ :
forall b1 A1 A2 X1,
  lc_typ A1 ->
  subst_tvar_in_bind A1 X1 (open_bind_wrt_typ b1 A2) = open_bind_wrt_typ (subst_tvar_in_bind A1 X1 b1) (subst_tvar_in_typ A1 X1 A2).
Proof.
unfold open_bind_wrt_typ; default_simp.
Qed.

#[export] Hint Resolve subst_tvar_in_bind_open_bind_wrt_typ : lngen.

Lemma subst_tvar_in_typ_open_typ_wrt_typ_var :
forall A2 A1 X1 X2,
  X1 <> X2 ->
  lc_typ A1 ->
  open_typ_wrt_typ (subst_tvar_in_typ A1 X1 A2) (typ_var_f X2) = subst_tvar_in_typ A1 X1 (open_typ_wrt_typ A2 (typ_var_f X2)).
Proof.
intros; rewrite subst_tvar_in_typ_open_typ_wrt_typ; default_simp.
Qed.

#[export] Hint Resolve subst_tvar_in_typ_open_typ_wrt_typ_var : lngen.

Lemma subst_tvar_in_bind_open_bind_wrt_typ_var :
forall b1 A1 X1 X2,
  X1 <> X2 ->
  lc_typ A1 ->
  open_bind_wrt_typ (subst_tvar_in_bind A1 X1 b1) (typ_var_f X2) = subst_tvar_in_bind A1 X1 (open_bind_wrt_typ b1 (typ_var_f X2)).
Proof.
intros; rewrite subst_tvar_in_bind_open_bind_wrt_typ; default_simp.
Qed.

#[export] Hint Resolve subst_tvar_in_bind_open_bind_wrt_typ_var : lngen.

(* begin hide *)

Lemma subst_tvar_in_typ_spec_rec_mutual :
(forall A1 A2 X1 n1,
  subst_tvar_in_typ A2 X1 A1 = open_typ_wrt_typ_rec n1 A2 (close_typ_wrt_typ_rec n1 X1 A1)).
Proof.
apply_mutual_ind typ_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma subst_tvar_in_typ_spec_rec :
forall A1 A2 X1 n1,
  subst_tvar_in_typ A2 X1 A1 = open_typ_wrt_typ_rec n1 A2 (close_typ_wrt_typ_rec n1 X1 A1).
Proof.
pose proof subst_tvar_in_typ_spec_rec_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve subst_tvar_in_typ_spec_rec : lngen.

(* end hide *)

(* begin hide *)

Lemma subst_tvar_in_bind_spec_rec_mutual :
(forall b1 A1 X1 n1,
  subst_tvar_in_bind A1 X1 b1 = open_bind_wrt_typ_rec n1 A1 (close_bind_wrt_typ_rec n1 X1 b1)).
Proof.
apply_mutual_ind bind_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma subst_tvar_in_bind_spec_rec :
forall b1 A1 X1 n1,
  subst_tvar_in_bind A1 X1 b1 = open_bind_wrt_typ_rec n1 A1 (close_bind_wrt_typ_rec n1 X1 b1).
Proof.
pose proof subst_tvar_in_bind_spec_rec_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve subst_tvar_in_bind_spec_rec : lngen.

(* end hide *)

Lemma subst_tvar_in_typ_spec :
forall A1 A2 X1,
  subst_tvar_in_typ A2 X1 A1 = open_typ_wrt_typ (close_typ_wrt_typ X1 A1) A2.
Proof.
unfold close_typ_wrt_typ; unfold open_typ_wrt_typ; default_simp.
Qed.

#[export] Hint Resolve subst_tvar_in_typ_spec : lngen.

Lemma subst_tvar_in_bind_spec :
forall b1 A1 X1,
  subst_tvar_in_bind A1 X1 b1 = open_bind_wrt_typ (close_bind_wrt_typ X1 b1) A1.
Proof.
unfold close_bind_wrt_typ; unfold open_bind_wrt_typ; default_simp.
Qed.

#[export] Hint Resolve subst_tvar_in_bind_spec : lngen.

(* begin hide *)

Lemma subst_tvar_in_typ_subst_tvar_in_typ_mutual :
(forall A1 A2 A3 X2 X1,
  X2 `notin` ftvar_in_typ A2 ->
  X2 <> X1 ->
  subst_tvar_in_typ A2 X1 (subst_tvar_in_typ A3 X2 A1) = subst_tvar_in_typ (subst_tvar_in_typ A2 X1 A3) X2 (subst_tvar_in_typ A2 X1 A1)).
Proof.
apply_mutual_ind typ_mutind;
default_simp.
Qed.

(* end hide *)

Lemma subst_tvar_in_typ_subst_tvar_in_typ :
forall A1 A2 A3 X2 X1,
  X2 `notin` ftvar_in_typ A2 ->
  X2 <> X1 ->
  subst_tvar_in_typ A2 X1 (subst_tvar_in_typ A3 X2 A1) = subst_tvar_in_typ (subst_tvar_in_typ A2 X1 A3) X2 (subst_tvar_in_typ A2 X1 A1).
Proof.
pose proof subst_tvar_in_typ_subst_tvar_in_typ_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve subst_tvar_in_typ_subst_tvar_in_typ : lngen.

(* begin hide *)

Lemma subst_tvar_in_bind_subst_tvar_in_bind_mutual :
(forall b1 A1 A2 X2 X1,
  X2 `notin` ftvar_in_typ A1 ->
  X2 <> X1 ->
  subst_tvar_in_bind A1 X1 (subst_tvar_in_bind A2 X2 b1) = subst_tvar_in_bind (subst_tvar_in_typ A1 X1 A2) X2 (subst_tvar_in_bind A1 X1 b1)).
Proof.
apply_mutual_ind bind_mutind;
default_simp.
Qed.

(* end hide *)

Lemma subst_tvar_in_bind_subst_tvar_in_bind :
forall b1 A1 A2 X2 X1,
  X2 `notin` ftvar_in_typ A1 ->
  X2 <> X1 ->
  subst_tvar_in_bind A1 X1 (subst_tvar_in_bind A2 X2 b1) = subst_tvar_in_bind (subst_tvar_in_typ A1 X1 A2) X2 (subst_tvar_in_bind A1 X1 b1).
Proof.
pose proof subst_tvar_in_bind_subst_tvar_in_bind_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve subst_tvar_in_bind_subst_tvar_in_bind : lngen.

(* begin hide *)

Lemma subst_tvar_in_typ_close_typ_wrt_typ_rec_open_typ_wrt_typ_rec_mutual :
(forall A2 A1 X1 X2 n1,
  X2 `notin` ftvar_in_typ A2 ->
  X2 `notin` ftvar_in_typ A1 ->
  X2 <> X1 ->
  degree_typ_wrt_typ n1 A1 ->
  subst_tvar_in_typ A1 X1 A2 = close_typ_wrt_typ_rec n1 X2 (subst_tvar_in_typ A1 X1 (open_typ_wrt_typ_rec n1 (typ_var_f X2) A2))).
Proof.
apply_mutual_ind typ_mutrec;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma subst_tvar_in_typ_close_typ_wrt_typ_rec_open_typ_wrt_typ_rec :
forall A2 A1 X1 X2 n1,
  X2 `notin` ftvar_in_typ A2 ->
  X2 `notin` ftvar_in_typ A1 ->
  X2 <> X1 ->
  degree_typ_wrt_typ n1 A1 ->
  subst_tvar_in_typ A1 X1 A2 = close_typ_wrt_typ_rec n1 X2 (subst_tvar_in_typ A1 X1 (open_typ_wrt_typ_rec n1 (typ_var_f X2) A2)).
Proof.
pose proof subst_tvar_in_typ_close_typ_wrt_typ_rec_open_typ_wrt_typ_rec_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve subst_tvar_in_typ_close_typ_wrt_typ_rec_open_typ_wrt_typ_rec : lngen.

(* end hide *)

(* begin hide *)

Lemma subst_tvar_in_bind_close_bind_wrt_typ_rec_open_bind_wrt_typ_rec_mutual :
(forall b1 A1 X1 X2 n1,
  X2 `notin` ftvar_in_bind b1 ->
  X2 `notin` ftvar_in_typ A1 ->
  X2 <> X1 ->
  degree_typ_wrt_typ n1 A1 ->
  subst_tvar_in_bind A1 X1 b1 = close_bind_wrt_typ_rec n1 X2 (subst_tvar_in_bind A1 X1 (open_bind_wrt_typ_rec n1 (typ_var_f X2) b1))).
Proof.
apply_mutual_ind bind_mutrec;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma subst_tvar_in_bind_close_bind_wrt_typ_rec_open_bind_wrt_typ_rec :
forall b1 A1 X1 X2 n1,
  X2 `notin` ftvar_in_bind b1 ->
  X2 `notin` ftvar_in_typ A1 ->
  X2 <> X1 ->
  degree_typ_wrt_typ n1 A1 ->
  subst_tvar_in_bind A1 X1 b1 = close_bind_wrt_typ_rec n1 X2 (subst_tvar_in_bind A1 X1 (open_bind_wrt_typ_rec n1 (typ_var_f X2) b1)).
Proof.
pose proof subst_tvar_in_bind_close_bind_wrt_typ_rec_open_bind_wrt_typ_rec_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve subst_tvar_in_bind_close_bind_wrt_typ_rec_open_bind_wrt_typ_rec : lngen.

(* end hide *)

Lemma subst_tvar_in_typ_close_typ_wrt_typ_open_typ_wrt_typ :
forall A2 A1 X1 X2,
  X2 `notin` ftvar_in_typ A2 ->
  X2 `notin` ftvar_in_typ A1 ->
  X2 <> X1 ->
  lc_typ A1 ->
  subst_tvar_in_typ A1 X1 A2 = close_typ_wrt_typ X2 (subst_tvar_in_typ A1 X1 (open_typ_wrt_typ A2 (typ_var_f X2))).
Proof.
unfold close_typ_wrt_typ; unfold open_typ_wrt_typ; default_simp.
Qed.

#[export] Hint Resolve subst_tvar_in_typ_close_typ_wrt_typ_open_typ_wrt_typ : lngen.

Lemma subst_tvar_in_bind_close_bind_wrt_typ_open_bind_wrt_typ :
forall b1 A1 X1 X2,
  X2 `notin` ftvar_in_bind b1 ->
  X2 `notin` ftvar_in_typ A1 ->
  X2 <> X1 ->
  lc_typ A1 ->
  subst_tvar_in_bind A1 X1 b1 = close_bind_wrt_typ X2 (subst_tvar_in_bind A1 X1 (open_bind_wrt_typ b1 (typ_var_f X2))).
Proof.
unfold close_bind_wrt_typ; unfold open_bind_wrt_typ; default_simp.
Qed.

#[export] Hint Resolve subst_tvar_in_bind_close_bind_wrt_typ_open_bind_wrt_typ : lngen.

Lemma subst_tvar_in_typ_typ_all :
forall X2 A2 A1 X1,
  lc_typ A1 ->
  X2 `notin` ftvar_in_typ A1 `union` ftvar_in_typ A2 `union` singleton X1 ->
  subst_tvar_in_typ A1 X1 (typ_all A2) = typ_all (close_typ_wrt_typ X2 (subst_tvar_in_typ A1 X1 (open_typ_wrt_typ A2 (typ_var_f X2)))).
Proof.
default_simp.
Qed.

#[export] Hint Resolve subst_tvar_in_typ_typ_all : lngen.

(* begin hide *)

Lemma subst_tvar_in_typ_intro_rec_mutual :
(forall A1 X1 A2 n1,
  X1 `notin` ftvar_in_typ A1 ->
  open_typ_wrt_typ_rec n1 A2 A1 = subst_tvar_in_typ A2 X1 (open_typ_wrt_typ_rec n1 (typ_var_f X1) A1)).
Proof.
apply_mutual_ind typ_mutind;
default_simp.
Qed.

(* end hide *)

Lemma subst_tvar_in_typ_intro_rec :
forall A1 X1 A2 n1,
  X1 `notin` ftvar_in_typ A1 ->
  open_typ_wrt_typ_rec n1 A2 A1 = subst_tvar_in_typ A2 X1 (open_typ_wrt_typ_rec n1 (typ_var_f X1) A1).
Proof.
pose proof subst_tvar_in_typ_intro_rec_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve subst_tvar_in_typ_intro_rec : lngen.
#[export] Hint Rewrite subst_tvar_in_typ_intro_rec using solve [auto] : lngen.

(* begin hide *)

Lemma subst_tvar_in_bind_intro_rec_mutual :
(forall b1 X1 A1 n1,
  X1 `notin` ftvar_in_bind b1 ->
  open_bind_wrt_typ_rec n1 A1 b1 = subst_tvar_in_bind A1 X1 (open_bind_wrt_typ_rec n1 (typ_var_f X1) b1)).
Proof.
apply_mutual_ind bind_mutind;
default_simp.
Qed.

(* end hide *)

Lemma subst_tvar_in_bind_intro_rec :
forall b1 X1 A1 n1,
  X1 `notin` ftvar_in_bind b1 ->
  open_bind_wrt_typ_rec n1 A1 b1 = subst_tvar_in_bind A1 X1 (open_bind_wrt_typ_rec n1 (typ_var_f X1) b1).
Proof.
pose proof subst_tvar_in_bind_intro_rec_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve subst_tvar_in_bind_intro_rec : lngen.
#[export] Hint Rewrite subst_tvar_in_bind_intro_rec using solve [auto] : lngen.

Lemma subst_tvar_in_typ_intro :
forall X1 A1 A2,
  X1 `notin` ftvar_in_typ A1 ->
  open_typ_wrt_typ A1 A2 = subst_tvar_in_typ A2 X1 (open_typ_wrt_typ A1 (typ_var_f X1)).
Proof.
unfold open_typ_wrt_typ; default_simp.
Qed.

#[export] Hint Resolve subst_tvar_in_typ_intro : lngen.

Lemma subst_tvar_in_bind_intro :
forall X1 b1 A1,
  X1 `notin` ftvar_in_bind b1 ->
  open_bind_wrt_typ b1 A1 = subst_tvar_in_bind A1 X1 (open_bind_wrt_typ b1 (typ_var_f X1)).
Proof.
unfold open_bind_wrt_typ; default_simp.
Qed.

#[export] Hint Resolve subst_tvar_in_bind_intro : lngen.


(* *********************************************************************** *)
(** * "Restore" tactics *)

Ltac default_auto ::= auto; tauto.
Ltac default_autorewrite ::= fail.
