Require Import List.
Import ListNotations.
Require Import Coq.Program.Equality.
Require Import Lia.
Require Import Nat.
Require Import Coq.Arith.Compare_dec.

Inductive type : Set :=
| Int : type
| Arr : type -> type -> type.

Notation "A → B" := (Arr A B) (at level 20).

Inductive term : Set :=
| Lit : nat -> term
| Var : nat -> term
| Lam : term -> term
| App : term -> term -> term
| Ann : term -> type -> term.

Inductive p : term -> Prop :=
| PLit : forall n, p (Lit n)
| PVar : forall x, p (Var x)
| PAnn : forall e A, p (Ann e A)
.              

Notation "e ∷ A" := (Ann e A) (at level 20).
Notation "ƛ A . e : B" := (Lam A e B) (at level 20).

Inductive context : Set :=
| Empty : context
| Cons  : context -> type -> context.

Inductive inCon : context -> nat -> type -> Prop :=
| Zin : forall {Gamma A},
      inCon (Cons Gamma A) 0 A
| Sin : forall {Gamma A B n},
      inCon Gamma n A ->
      inCon (Cons Gamma B) (S n) A.

Inductive hint : Set :=
| Noth : hint
| TT : type -> hint
| Hole : term -> hint -> hint.

Inductive awf : context -> type -> hint -> Prop :=
| awf_Noth : forall Gamma A,
    awf Gamma A Noth
| awf_Tau : forall Gamma A,
    awf Gamma A (TT A)
| awf_Hole : forall Gamma H e A B C,
    aty Gamma (TT A) e C ->
    awf Gamma B H ->
    awf Gamma (Arr A B) (Hole e H)
with aty : context -> hint -> term -> type -> Prop :=
| A_Int : forall Gamma n,
    aty Gamma Noth (Lit n) Int
| A_Var : forall Gamma x A,
    inCon Gamma x A ->
    aty Gamma Noth (Var x) A
| A_Ann : forall Gamma e A B,
    aty Gamma (TT A) e B ->
    aty Gamma Noth (Ann e A) A
| A_App : forall Gamma e1 e2 H A B,
    aty Gamma (Hole e2 H) e1 (Arr A B) ->
    aty Gamma H (App e1 e2) B
| A_Lam1 : forall Gamma e A B C,
    aty (Cons Gamma A) (TT B) e C ->
    aty Gamma (TT (Arr A B)) (Lam e) (Arr A C)
| A_Lam2 : forall Gamma e1 e A B H,
    aty Gamma Noth e1 A ->
    aty (Cons Gamma A) H e B ->
    aty Gamma (Hole e1 H) (Lam e) (Arr A B)
| A_Sub : forall Gamma e A H,
    aty Gamma Noth e A ->
    H <> Noth ->
    p e ->
    awf Gamma A H ->
    aty Gamma H e A
.

Hint Constructors aty : core.
Hint Constructors awf : core.

Notation "T |- A <: H" := (awf T A H) (at level 40).
Notation "T |- H => e => A" := (aty T H e A) (at level 50).

Fixpoint size_h (h : hint) : nat :=
  match h with
  | Noth => 0
  | TT _ => 0
  | Hole _ h' => 1 + size_h h'
  end.

Fixpoint size_e (e : term) : nat :=
  match e with
  | Lit _ => 0
  | Var _ => 0
  | Lam e' => 1 + size_e e'
  | App e1 e2 => 1 + size_e e1 + size_e e2
  | Ann e' A => 1 + size_e e'
  end.

Fixpoint size_t (t : type) : nat :=
  match t with
  | Int => 0
  | Arr A B => 1 + size_t A + size_t B
  end.

Lemma eqt_dec_k1_k2 : forall k1 k2 (A B : type),
    size_t A < k1 ->
    size_t B < k2 ->               
    A = B \/ A <> B.
Proof.
  intros k1 k2. induction k1; induction k2; intros.
  - lia.
  - lia.
  - lia.
  - destruct A; destruct B.
    + left. reflexivity.
    + right. intros Inv. dependent destruction Inv.
    + right. intros Inv. dependent destruction Inv.
    + simpl in *.
      assert (sz1 : size_t A1 < k1). lia.
      assert (sz2 : size_t B1 < S k2). lia.
      assert (sz3 : size_t A2 < k1). lia.
      assert (sz4 : size_t B2 < S k2). lia.      
      pose proof (IHk1 A1 B1 sz1 sz2) as IHi.     
      pose proof (IHk1 A2 B2 sz3 sz4) as IHii.
      destruct IHi; destruct IHii; subst.
      * left. reflexivity.
      * right. intros Rev. dependent destruction Rev.
        apply H2. reflexivity.
      * right. intros Rev. dependent destruction Rev.
        apply H1. reflexivity.
      * right. intros Rev. dependent destruction Rev.
        apply H1. reflexivity.
Qed.

Lemma eqt_dec : forall (A B : type),
    A = B \/ A <> B.
Proof.
  intros.
  eapply eqt_dec_k1_k2; eauto.
Qed.

Lemma inCon_dec : forall Gamma x,
    (exists A, inCon Gamma x A) \/ ~ (exists A, inCon Gamma x A).
Proof.
Admitted. (* this is proved *)

Inductive allsmaller : hint -> nat -> Prop :=
| as_empty:
  forall k, allsmaller Noth k
| as_type :
  forall A k, allsmaller (TT A) k
| as_term :
  forall H e k,
    size_e e < k ->
    allsmaller H k ->
    allsmaller (Hole e H) k               
.

Notation "H << k" := (allsmaller H k) (at level 40).

(* dec of matching is not a exist form since they're all inputs *)
Lemma awf_decidable : forall H Gamma k A,
    allsmaller H (k + size_h H) ->
    (awf Gamma A H) \/ ~ (awf Gamma A H).
Proof.
  induction H; intros.
  - left. econstructor.
  - destruct (eqt_dec t A).
    + subst. left. econstructor.
    + right. intro Inv. dependent destruction Inv.
      apply H0. reflexivity.
  - dependent destruction A.
    + right. intro Inv. dependent destruction Inv.
    + dependent destruction H0.
      (* here we need the dec of typing, and the measure we can only use is H1 *)
Admitted.
      
Lemma aty_decidable : forall k Gamma e H,
    size_e e < k ->
    (exists A, aty Gamma H e A) \/ ~ (exists A, aty Gamma H e A).
Proof.
  induction k; intros.
  lia. 
  destruct e.
  - admit.
  - admit.
  - admit.
  - (* App Case *) admit.
  - simpl in *.
    pose proof (IHk Gamma e (TT t)) as IH. destruct IH. lia.
    + destruct H1. left.
      pose proof (awf_decidable H Gamma k t).
      (* here we sending the measure to matching, the measure is k *)
Admitted.
