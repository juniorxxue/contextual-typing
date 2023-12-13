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
| And : type -> type -> type.

Notation "A → B" := (Arr A B) (at level 20).
Notation "A & B" := (And A B) (at level 20).

Inductive term : Set :=
| Lit : nat -> term
| Var : nat -> term
| Lam : term -> term
| App : term -> term -> term
| Ann : term -> type -> term.

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
| Sc : ccounter -> ccounter.

Inductive counter : Set :=
| Ba : ccounter -> counter
| Si : counter -> counter.

Fixpoint size_ccounter (j : ccounter) : nat :=
  match j with
  | Inf => 1
  | Zc => 0
  | Sc j' => 1 + size_ccounter j'
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
| DS_Arr_Si : forall A B C D i,
    dsub C (Ba Inf) A ->
    dsub B i D ->
    dsub (Arr A B) (Si i) (Arr A D)
| DS_Arr_Sc : forall A B C D j,
    dsub C (Ba Inf) A ->
    dsub B (Ba j) D ->
    dsub (Arr A B) (Ba (Sc j)) (Arr A D)
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
.

Notation "A <: i # B" := (dsub A i B) (at level 50).
Notation "T ⊢ j # e : A" := (dty T j e A) (at level 50).

(* Algo. *)

Inductive hint : Prop :=
| Noth : hint
| Tau : type -> hint
| Ho : term -> hint -> hint.

Inductive asub : context -> type -> hint -> type -> Prop :=
| As_Int : forall Gamma,
    asub Gamma Int (Tau Int) Int
| As_Top : forall Gamma A,
    asub Gamma A (Tau Top) Top
| As_Noth : forall Gamma A,
    asub Gamma A Noth A
| As_Arr : forall Gamma A B C D,
    asub Gamma C (Tau A) A ->
    asub Gamma B (Tau B) D ->
    asub Gamma (Arr A B) (Tau (Arr C D)) (Arr C D)
| As_Hint : forall Gamma A B H e D,
    aty Gamma (Tau A) e A ->
    asub Gamma B H D ->
    asub Gamma (Arr A B) (Ho e H) (Arr A D)
| As_And_L : forall Gamma A B H C,
    asub Gamma A H C ->
    asub Gamma (And A B) H C
| As_And_R : forall Gamma A B H C,
    asub Gamma B H C ->
    asub Gamma (And A B) H C
| As_And : forall Gamma A B C,
    asub Gamma A (Tau B) B ->
    asub Gamma A (Tau C) C ->
    asub Gamma A (Tau (And B C)) (And B C)
with aty : context -> hint -> term -> type -> Prop :=
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
| A_Lam1 : forall Gamma e A B,
    aty (Cons Gamma A) (Tau B) e B ->
    aty Gamma (Tau (Arr A B)) (Lam e) (Arr A B)
| A_Lam2 : forall Gamma e1 e A B H,
    aty Gamma Noth e1 A ->
    aty (Cons Gamma A) H e B ->
    aty Gamma (Ho e1 H) (Lam e) (Arr A B)
| A_Sub : forall Gamma e A B H,
    aty Gamma Noth e A ->
    asub Gamma A H B ->
    H <> Noth ->
    aty Gamma H e B
| A_And : forall Gamma A B e,
    aty Gamma (Tau A) e A ->
    aty Gamma (Tau B) e B ->
    aty Gamma (Tau (And A B)) e (And A B)          
.

Hint Constructors aty : core.

Notation "T |- A <: H ⤳ B" := (asub T A H B) (at level 40).
Notation "T |- H => e => A" := (aty T H e A) (at level 50).

Fixpoint apps (e : term) (es : list term) : term :=
  match es with
  | [] => e
  | e' :: es' => apps (App e e') es'
  end.

Notation "e ▷ es" := (apps e es) (at level 15).

Inductive spl : hint -> type -> list term -> hint -> list type -> type -> Set :=
| No_Noth : forall A,
    spl Noth A [] Noth [] A
| No_Tau : forall A B,
    spl (Tau A) B [] (Tau A) [] B
| Have : forall e H A B es A' B' Bs,
    spl H B es A' Bs B' ->
    spl (Ho e H) (Arr A B) (e :: es) A' (A :: Bs) B'       
.

Lemma len_0_imply_empty : forall (l : list term),
    length l = 0 ->
    l = [].
Proof.
  induction l; intros; eauto.
  dependent destruction H.
Qed.
  

Lemma lst_destruct_rev : forall (l : list term),
    length l > 0 -> 
  exists xs x, l = xs ++ [x].
Proof.
  intros. induction l.
  - inversion H.
  - dependent destruction H.
    + eapply len_0_imply_empty in x. subst. exists []. exists a. auto.
    + pose proof (IHl H). destruct H0. destruct H0.
      exists (a :: x). exists x0. subst. reflexivity.
Qed.

Lemma rw_apps_gen : forall es e es',
    apps e (es ++ es') = (apps (apps e es) es').
Proof.
  induction es; eauto.
  intros.
  simpl. eauto.
Qed.

Lemma rw_apps : forall es e x,
    apps e (es ++ [x]) = App (apps e es) x.
Proof.
  intros.
  eapply rw_apps_gen.
Qed.

Lemma dty_weaken : forall Gamma A B e j,
    dty (Cons Gamma A) j e B ->
    dty Gamma j e B.
Admitted.

Lemma length_append : forall (l : list term) x,
    length (l ++ [x]) = length l + 1.
Proof.
  intros. induction l; eauto. simpl in *. f_equal. assumption.
Qed.

Lemma subst_app : forall k g es Gamma A B e e1 j,    
    2 * (length es) + size_counter j < k ->
    size_type B < g ->
    dty (Cons Gamma A) j (apps e es) B ->
    dty Gamma (Ba Zc) e1 A ->
    dty Gamma j (apps (App (Lam e) e1) es) B.
Proof.
  induction k; induction g; intros.  
  - dependent destruction H.
  - dependent destruction H.
  - dependent destruction H0.
  - destruct (lt_eq_lt_dec (length es) 0).
    + destruct s.
      * inversion l.
      * eapply len_0_imply_empty in e0. subst.
        simpl in *. econstructor. econstructor. eapply H1. eapply H2.
    + pose (lst_destruct_rev es l) as Rev. destruct Rev.
      destruct H3. 
      subst. rewrite rw_apps in H1.
      dependent destruction H1.
      * rewrite rw_apps. eapply D_App1.
        ++ eapply IHk; eauto. simpl in *.
           rewrite length_append in H. lia.
        ++ eapply dty_weaken; eauto.
      * rewrite rw_apps. eapply D_App2.
        ++ eapply IHk; eauto. simpl in *.
           rewrite length_append in H. lia.
        ++ eapply dty_weaken; eauto.
      * destruct i.
        ++ destruct c.
           ** eapply D_Sub; eauto.
              eapply IHk; eauto. simpl in *.
              rewrite length_append in *. lia. 
              rewrite rw_apps. assumption.
           ** exfalso. eapply H3; eauto.
           ** eapply D_Sub; eauto.
              eapply IHk; eauto. simpl in *.
              rewrite length_append in *. lia.
              rewrite rw_apps. assumption.
        ++ eapply D_Sub; eauto.
           eapply IHk; eauto. simpl in *.
           rewrite length_append in *. lia.
           rewrite rw_apps. assumption.
      * eapply D_And.
        ++ eapply IHg; eauto. simpl in *.
           rewrite length_append in *. lia.
           rewrite rw_apps. assumption.
        ++ eapply IHg; eauto. simpl in *.
           rewrite length_append in *. lia.
           rewrite rw_apps. assumption.
Qed.

Variable A : Type.

Lemma app_length_k : forall k (l1 l2 : list nat),
  length l1 < k ->
  length (l1 ++ l2) = (length l1) + (length l2).
Proof.
  induction k; intros.
  - dependent destruction H.
  - destruct l1.
    + simpl. reflexivity.
    + simpl. f_equal. apply IHk. 
      simpl in H. lia.
Qed.

Lemma app_length : forall l1 l2 : list nat,
    length (l1 ++ l2) = (length l1) + (length l2).
Proof.
  intros. eapply app_length_k.
  auto.
Qed.
