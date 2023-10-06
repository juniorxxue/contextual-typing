Require Import List.
Import ListNotations.
Require Import Coq.Program.Equality.
Require Import Lia.

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

(* Decl. *)

Inductive counter : Set :=
| Inf : counter
| ZCo : counter
| SCo : counter -> counter.

Fixpoint size_counter (j : counter) : nat :=
  match j with
  | Inf => 1
  | ZCo => 0
  | SCo j' => 1 + size_counter j'
  end.

Inductive dwf : type -> counter -> Prop :=
| dwf_Z : forall A,
    dwf A ZCo
| dwf_Inf : forall A,
    dwf A Inf
| dwf_S : forall A B j,
    dwf B j ->
    dwf (Arr A B) (SCo j)
.

Notation "A ~ j" := (dwf A j) (at level 40).

Inductive dty : context -> counter -> term -> type -> Prop :=
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
    j <> ZCo ->
    dwf A j ->
    dty Gamma j e A
.

Notation "T ⊢ j e : A" := (dty T j e A) (at level 50).

(* Algo. *)

Inductive hint : Prop :=
| Noth : hint
| Tau : type -> hint
| Ho : term -> hint -> hint.

Inductive awf : context -> type -> hint -> Prop :=
| awf_Noth : forall Gamma A,
    awf Gamma A Noth
| awf_Tau : forall Gamma A,
    awf Gamma A (Tau A)
| awf_Hole : forall Gamma H e A B C,
    aty Gamma (Tau A) e C ->
    awf Gamma B H ->
    awf Gamma (Arr A B) (Ho e H)
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

Hint Constructors aty : core.

Notation "T |- A <: H" := (awf T A H) (at level 40).
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

Lemma lst_destruct_rev : forall (l : list term),
  exists xs x, l = xs ++ [x].
Proof.
Admitted.

Lemma rw_apps : forall e es x,
    apps e (es ++ [x]) = App (apps e es) x.
Proof.
  induction es; eauto.
  intros. simpl.
Admitted.

Lemma dty_weaken : forall Gamma A B e j,
    dty (Cons Gamma A) j e B ->
    dty Gamma j e B.
Admitted.

Lemma length_append : forall (l : list term) x,
    length (l ++ [x]) = length l + 1.
Proof.
  intros. induction l; eauto. simpl in *. f_equal. assumption.
Qed.

Lemma subst_app : forall k es Gamma A B e e1 j,
    2 * (length es) + size_counter j < k ->
    dty (Cons Gamma A) j (apps e es) B ->
    dty Gamma ZCo e1 A ->
    dty Gamma j (apps (App (Lam e) e1) es) B.
Proof.
  induction k; intros.
  - dependent destruction H.
  - pose (lst_destruct_rev es) as Rev. destruct Rev. destruct H2.
    subst. rewrite rw_apps in H0.
    dependent destruction H0.
    + rewrite rw_apps. eapply D_App1.
      * eapply IHk; eauto. simpl in *.
        rewrite length_append in H. lia.
      * eapply dty_weaken; eauto.
    + rewrite rw_apps. eapply D_App2.
      * eapply IHk; eauto. simpl in *.
        rewrite length_append in H. lia.
      * eapply dty_weaken; eauto.
    + destruct j.
      * eapply D_Sub; eauto.
        eapply IHk; eauto. simpl in *. lia.
        rewrite rw_apps. assumption.
      * exfalso. eapply H; eauto.
      * eapply D_Sub; eauto.
        eapply IHk; eauto. simpl in *. lia.
        rewrite rw_apps. assumption.
Qed.
      
(* Experiment with induction on size *)

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


(* Completeness *)


Inductive rty : context -> counter -> term -> type -> Prop :=
| RZ : forall Gamma A e,
    aty Gamma Noth e A ->
    rty Gamma ZCo e A
| RInf : forall Gamma A e,
    aty Gamma (Tau A) e A ->
    rty Gamma Inf e A
| RS : forall Gamma e j A B,
    (forall e', dty Gamma ZCo e' A -> rty Gamma j (App e e') B) ->
    rty Gamma (SCo j) e (Arr A B)
.

Notation "T ⊢r j e : A" := (rty T j e A) (at level 50).

Lemma r_app : forall Gamma e e' A B j,
    rty Gamma (SCo j) e (Arr A B) ->
    dty Gamma ZCo e' A ->
    rty Gamma j (App e e') B.
Proof.
  intros. dependent destruction H. eapply H; eauto.
Qed.

Lemma r_lam : forall Gamma e A B j,
    rty (Cons Gamma A) j e B ->
    rty Gamma (SCo j) (Lam e) (Arr A B).
Proof.
  intros. induction H.
  - econstructor. intros.
Admitted.

Lemma r_sub : forall j Gamma e A,
    rty Gamma ZCo e A ->
    dwf A j ->
    rty Gamma j e A.
Proof.
  induction j; intros.
  - econstructor. dependent destruction H.
    admit.
  - assumption.
  - dependent destruction H0.
    econstructor. intros.
    eapply IHj; eauto.
    * 
Admitted.


Theorem complete : forall Gamma j e A,
    dty Gamma j e A ->
    rty Gamma j e A.
Proof.
  intros.
  induction H.
  - econstructor. eauto.
  - econstructor; eauto.
  - econstructor. econstructor. dependent destruction IHdty. eauto.
  - econstructor. dependent destruction IHdty. eauto.
  - econstructor. intros. eapply r_app; eauto. eapply r_lam; eauto.
  - dependent destruction IHdty1. dependent destruction IHdty2.
    econstructor; eauto. eapply A_App. admit. (* by subsumption lemma (proved) *)
  - dependent destruction IHdty1. dependent destruction IHdty2.
    eapply H1; eauto.
  - eapply r_sub; eauto.
Admitted.


Theorem complete' : forall Gamma j e A,
    dty Gamma j e A ->
    dwf A j ->
    rty Gamma j e A.
Proof.
  induction j; intros.
  - econstructor. dependent destruction H0.
    admit.
  - econstructor. dependent destruction H0.
    
  - dependent destruction H0.
    econstructor. intros.    
    eapply IHj; eauto.
    eapply D_App2; eauto.
