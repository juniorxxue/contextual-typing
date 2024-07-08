Require Import List.
Import ListNotations.
Require Import Coq.Program.Equality.
Require Import Lia.
Require Import Nat.
Require Import Coq.Arith.Compare_dec.

Inductive type : Set :=
| Int : type
| Top : type
| Arr : type -> type -> type
| And : type -> type -> type
| SRcd : nat -> type -> type
.

Notation "A → B" := (Arr A B) (at level 20).
Notation "A & B" := (And A B) (at level 20).

Inductive term : Set :=
| Lit : nat -> term
| Var : nat -> term
| Lam : term -> term
| App : term -> term -> term
| Ann : term -> type -> term
| Rcd : record -> term
| Prj : term -> nat -> term
with record : Set :=
| rnil : record
| rcons : nat -> term -> record -> record
.

Notation "e ∷ A" := (Ann e A) (at level 20).

Inductive context : Set :=
| Empty : context
| Cons  : context -> type -> context.

Inductive inCon : context -> nat -> type -> Prop :=
| Zin : forall {Gamma A},
      inCon (Cons Gamma A) 0 A
| Sin : forall {Gamma A B n},
      inCon Gamma n A ->
      inCon (Cons Gamma B) (S n) A.

(* Decl. *)

Inductive ccounter : Set :=
| Inf : ccounter
| Zc : ccounter
| Sc : ccounter -> ccounter
| Sl : ccounter -> ccounter.

Inductive counter : Set :=
| Ba : ccounter -> counter
| Si : counter -> counter.

Fixpoint size_ccounter (j : ccounter) : nat :=
  match j with
  | Inf => 1
  | Zc => 0
  | Sc j' => 1 + size_ccounter j'
  | Sl j' => 1 + size_ccounter j'
  end.

Fixpoint size_counter (i : counter) : nat :=
  match i with
  | Ba j => size_ccounter j
  | Si i => 1 + size_counter i
  end.

Fixpoint size_type (t : type) : nat :=
  match t with
  | And A B => 1 + size_type A + size_type B
  | Arr A B => 1 + size_type A + size_type B
  | SRcd l A => 1 + size_type A
  | _ => 0
  end.

Inductive dsub : type -> counter -> type -> Prop :=
| DS_Z : forall A,
    dsub A (Ba Zc) A
| DS_Int :
    dsub Int (Ba Inf) Int
| DS_Top : forall A,
    dsub A (Ba Inf) Top
| DS_Arr_Inf : forall A B C D,
    dsub C (Ba Inf) A ->
    dsub B (Ba Inf) D ->
    dsub (Arr A B) (Ba Inf) (Arr C D)
| DS_Arr_Sc : forall A B C D j,
    dsub C (Ba Inf) A ->
    dsub B (Ba j) D ->
    dsub (Arr A B) (Ba (Sc j)) (Arr A D)
| DS_Rcd_Inf : forall A B l,
    dsub A (Ba Inf) B ->
    dsub (SRcd l A) (Ba Inf) (SRcd l B)
| DS_Rcd_Sl : forall A B l j,
    dsub A (Ba j) B ->
    dsub (SRcd l A) (Ba (Sl j)) (SRcd l B)
| DS_And1 : forall A B C j,
    dsub A j C ->
    dsub (And A B) j C
| DS_And2 : forall A B C j,
    dsub B j C ->
    dsub (And A B) j C
| DS_And : forall A B C,
    dsub A (Ba Inf) B ->
    dsub A (Ba Inf) C ->
    dsub A (Ba Inf) (And B C)
.

Inductive dty : context -> counter -> term -> type -> Prop :=
| D_Int : forall Gamma i,
    dty Gamma (Ba Zc) (Lit i) Int
| D_Var : forall Gamma x A,
    inCon Gamma x A ->
    dty Gamma (Ba Zc) (Var x) A
| D_Ann : forall Gamma e A,
    dty Gamma (Ba Inf) e A ->
    dty Gamma (Ba Zc) (Ann e A) A
| D_Lam1 : forall Gamma e A B,
    dty (Cons Gamma A) (Ba Inf) e B ->
    dty Gamma (Ba Inf) (Lam e) (Arr A B)
| D_Lam2 : forall Gamma e A B i,
    dty (Cons Gamma A) i e B ->
    dty Gamma (Si i) (Lam e) (Arr A B)
| D_App1 : forall Gamma e1 e2 A B j,
    dty Gamma (Ba (Sc j)) e1 (Arr A B) ->
    dty Gamma (Ba Inf) e2 A ->
    dty Gamma (Ba j) (App e1 e2) B
| D_App2 : forall Gamma e1 e2 A B i,
    dty Gamma (Si i) e1 (Arr A B) ->
    dty Gamma (Ba Zc) e2 A ->
    dty Gamma i (App e1 e2) B
| D_Sub: forall Gamma e A A' i,
    dty Gamma (Ba Zc) e A ->
    dsub A i A'->
    i <> Ba Zc ->
    dty Gamma i e A'
| D_And : forall Gamma e A B,
    dty Gamma (Ba Inf) e A ->
    dty Gamma (Ba Inf) e B ->
    dty Gamma (Ba Inf) e (And A B)
| D_Rcd : forall Gamma rs AS,
    rty Gamma (Ba Zc) rs AS ->
    dty Gamma (Ba Zc) (Rcd rs) AS
| D_Prj : forall Gamma e l j A,
    dty Gamma (Ba (Sl j)) e (SRcd l A) ->
    dty Gamma (Ba j) (Prj e l) A
with rty : context -> counter -> record -> type -> Prop :=
| R_Nil : forall Gamma,
    rty Gamma (Ba Zc) rnil Top
| R_One : forall Gamma e A l,
    dty Gamma (Ba Zc) e A ->
    rty Gamma (Ba Zc) (rcons l e rnil) (SRcd l A)
| R_Cons : forall Gamma l e rs A AS,
    dty Gamma (Ba Zc) e A ->
    rty Gamma (Ba Zc) rs AS ->
    rty Gamma (Ba Zc) (rcons l e rs) (And (SRcd l A) AS)  
.

Notation "A <: i # B" := (dsub A i B) (at level 50).
Notation "T ⊢ j # e : A" := (dty T j e A) (at level 50).

Inductive apps : Set :=
| nil_a : apps
| cons_a : term -> apps -> apps
| cons_l : nat -> apps -> apps.

Fixpoint f (e : term) (es : apps) : term :=
  match es with
  | nil_a => e
  | cons_a e' es' => f (App e e') es'
  | cons_l l es' => f (Prj e l) es'
  end.

Notation "e ▷ es" := (f e es) (at level 15).


Lemma dty_weaken : forall Gamma A B e j,
    dty (Cons Gamma A) j e B ->
    dty Gamma j e B.
Admitted.

Fixpoint len_apps (es : apps) : nat :=
  match es with
  | nil_a => 0
  | cons_a _ es => 1 + len_apps es
  | cons_l _ es => 1 + len_apps es
  end.

Lemma len_0_imply_empty : forall es,
    len_apps es = 0 ->
    es = nil_a.
Proof.
  induction es; intros; eauto.
  - dependent destruction H.
  - dependent destruction H.
Qed.

Fixpoint cat_a (es1 : apps) (es2 : apps) : apps :=
  match es1 with
  | nil_a => es2
  | (cons_a e es') => (cons_a e (cat_a es' es2))
  | (cons_l l es') => (cons_l l (cat_a es' es2))
  end.

Lemma apps_destruct : forall es,
    len_apps es > 0 ->
    (exists es' e, es = cat_a es' (cons_a e nil_a)) \/
      (exists es' l, es = cat_a es' (cons_l l nil_a)).
Proof.
  intros. induction es.
  - inversion H.
  - dependent destruction H.
    + eapply len_0_imply_empty in x. subst.
      left. exists nil_a. exists t. simpl. reflexivity.
    + pose proof (IHes H). destruct H0.
      * destruct H0. destruct H0.
        left. subst. exists (cons_a t x). exists x0. simpl. reflexivity.
      * destruct H0. destruct H0.
        right. subst. exists (cons_a t x). exists x0. simpl. reflexivity.
  - dependent destruction H.
    + eapply len_0_imply_empty in x. subst.
      right. exists nil_a. exists n. simpl. reflexivity.
    + pose proof (IHes H). destruct H0.
      * destruct H0. destruct H0.
        left. subst. exists (cons_l n x). exists x0. simpl. reflexivity.
      * destruct H0. destruct H0.
        right. subst. exists (cons_l n x). exists x0. simpl. reflexivity.
Qed.

Lemma rw_apps_a : forall es e x,
    f e (cat_a es (cons_a x nil_a)) = App (f e es) x.
Proof.
  intros.
Admitted.

Lemma rw_apps_l : forall es e l,
    f e (cat_a es (cons_l l nil_a)) = Prj (f e es) l.
Proof.
  intros.
Admitted.

Lemma size_cat_a : forall es e,
    len_apps (cat_a es (cons_a e nil_a)) = 1 + len_apps es.
Proof.
  intros. induction es; eauto. simpl in *.
  f_equal. assumption. simpl in *. f_equal. assumption.
Qed.

Lemma size_cat_l : forall es l,
    len_apps (cat_a es (cons_l l nil_a)) = 1 + len_apps es.
Proof.
  intros. induction es; eauto. simpl in *.
  f_equal. assumption. simpl in *. f_equal. assumption.
Qed.

Lemma subst_app' : forall k1 k2 k3 es Gamma A B e e1 j,    
    len_apps es < k1 ->
    size_counter j < k2 ->
    size_type B < k3 ->
    dty (Cons Gamma A) j (f e es) B ->
    dty Gamma (Ba Zc) e1 A ->
    dty Gamma j (f (App (Lam e) e1) es) B.
Proof.
  induction k1; induction k2; induction k3; intros; eauto.
  - inversion H1.
  - inversion H.
  - inversion H.
  - inversion H.
  - inversion H0.
  - inversion H0.
  - inversion H1.
  - destruct (lt_eq_lt_dec (len_apps es) 0).
    + destruct s.
      * inversion l.
      * eapply len_0_imply_empty in e0. subst.
        simpl in *. econstructor. econstructor. eapply H2. eapply H3.
    + pose (apps_destruct es l) as Rev. destruct Rev.
      * (* arguments *)
        destruct H4. destruct H4.
        subst.
        rewrite rw_apps_a in H2. dependent destruction H2.
        ++ rewrite rw_apps_a.
           eapply D_App1.
           ** eapply IHk1; eauto. simpl in *.
              rewrite size_cat_a in *. lia.
           ** eapply dty_weaken; eauto.
        ++ rewrite rw_apps_a.
           eapply D_App2.
           ** eapply IHk1; eauto. simpl in *.
              rewrite size_cat_a in *. lia.
           **  eapply dty_weaken; eauto.
        ++ destruct i.
           ** destruct c. (* instance of counters *)
              *** eapply D_Sub; eauto.
                  eapply IHk2; eauto. simpl in *. lia.
                  rewrite rw_apps_a. assumption.
              *** exfalso. eapply H4; eauto.
              *** eapply D_Sub; eauto.
                  eapply IHk2; eauto. simpl in *. lia.
                  rewrite rw_apps_a. assumption.
              *** eapply D_Sub; eauto.
                  eapply IHk2; eauto. simpl in *. lia.
                  rewrite rw_apps_a. assumption.
           ** eapply D_Sub; eauto.
              eapply IHk2; eauto. simpl in *. lia.
              rewrite rw_apps_a. assumption.
        ++ eapply D_And.
           ** eapply IHk3; eauto. simpl in *. lia.
              rewrite rw_apps_a. assumption.
           ** eapply IHk3; eauto. simpl in *. lia.
              rewrite rw_apps_a. assumption.
      * (* label *)
        destruct H4. destruct H4. subst.
        rewrite rw_apps_l in H2.
        dependent destruction H2.
        ++ eapply D_Sub; eauto.
           eapply IHk2; eauto. simpl in *.
           destruct i.
           ** destruct c.
              *** simpl in *. lia.
              *** exfalso. eapply H4. reflexivity.
              *** simpl in *. lia.
              *** simpl in *. lia.
           ** simpl in *. lia.
           ** rewrite rw_apps_l. assumption.
        ++ eapply D_And.
           ** eapply IHk3; eauto. simpl in *. lia.
              rewrite rw_apps_l. assumption.
           ** eapply IHk3; eauto. simpl in *. lia.
              rewrite rw_apps_l. assumption.
        ++ rewrite rw_apps_l.
           eapply D_Prj; eauto.
           eapply IHk1; eauto.
           simpl in *. rewrite size_cat_l in *. lia.           
Qed.
