Require Import Coq.Program.Equality.
Require Import Coq.Program.Tactics.
Require Import Coq.Strings.String.
Require Import Bool.
Require Import Metalib.Metatheory.
Require Import List.
Require Import Lia.

Require Import subtyping.decl.
Require Import subtyping.prop_ln.

Ltac dd H := dependent destruction H.

Ltac inst_cofinite_impl H x :=
  match type of H with
  | forall x, x `notin` ?L -> _ =>
      let Fr := fresh "Fr" in
      assert (x `notin` L) as Fr by auto;
      specialize (H x Fr); clear Fr
  end
.

Ltac inst_cofinites_with x :=
  repeat
    match goal with
    | H : forall x0, x0 `notin` ?L -> _ |- _ =>
      inst_cofinite_impl H x
    end
.

Ltac inst_cofinites :=
  match goal with
  | x : atom |- _ => inst_cofinites_with x
  end.

Ltac inst_cofinites_with_new :=
  let x := fresh "x" in
  pick fresh x; inst_cofinites_with x.

Ltac inst_cofinites_by F :=
  let L := F in
  let x := fresh "x" in
  pick fresh x for L; inst_cofinites_with x.


(* The definition of n in each rule is not final!!!!! *)
Inductive d_sub_size : env -> counter -> typ -> typ -> nat -> Prop :=  
 | d_subs__refl : forall (E:env) (A B:typ) (n:nat),
     wf_env E ->
     d_inst E A B ->
     d_sub_size E counter_z A B n 
 | d_subs__int : forall (E:env) (n:nat),
     wf_env E ->
     d_sub_size E counter_inf typ_int typ_int n
 | d_subs__tvar : forall (E:env) (X:typvar) (n:nat),
     wf_env E ->
     d_sub_size E counter_inf (typ_var_f X) (typ_var_f X) n
 | d_subs__arr1 : forall (E:env) (A1 B1 A2 B2:typ) (n1 n2 : nat),
     d_sub_size E counter_inf A2 A1 n1 ->
     d_sub_size E counter_inf B1 B2 n2 ->
     d_sub_size E counter_inf (typ_arrow A1 B1) (typ_arrow A2 B2) (S (n1 + n2))
 | d_subs__arr2 : forall (E:env) (c:counter) (A1 B1 A2 B2:typ) (n1 n2 : nat),
     d_sub_size E counter_inf A2 A1 n1 ->
     d_sub_size E c B1 B2 n2 ->
     d_sub_size E (counter_suc c) (typ_arrow A1 B1) (typ_arrow A2 B2) (S (n1 + n2))
 | d_subs__all : forall (L:vars) (E:env) (A1 A2:typ) (n:nat),
      ( forall X , X \notin  L  -> d_sub_size  ( X ~ bind_empty  ++  E )  counter_inf  ( open_typ_wrt_typ A1 (typ_var_f X) )   ( open_typ_wrt_typ A2 (typ_var_f X) )  n)  ->
     d_sub_size E counter_inf (typ_all A1) (typ_all A2) (S n)
 | d_subs__alll1 : forall (L:vars) (E:env) (c:counter) (A B C:typ) (n: nat),
     d_wf_typ E C ->
     ( forall X , X \notin  L  -> find X (counter_suc c)  ( open_typ_wrt_typ A (typ_var_f X) )  )  ->
      ( forall X , X \notin  L  -> d_sub_size  ( X ~ (bind_typ C)  ++  E )  (counter_suc c) ( open_typ_wrt_typ A (typ_var_f X) )  B n)  ->
     d_sub_size E (counter_suc c) (typ_all A) B (S n)
 | d_subs__alll2 : forall (L:vars) (E:env) (c:counter) (A B C:typ) (n : nat),
     d_wf_typ E C ->
      ( forall X , X \notin  L  -> d_sub_size  ( X ~ (bind_typ C)  ++  E )  c  ( open_typ_wrt_typ A (typ_var_f X) )  B n)  ->
     d_sub_size E (counter_tsuc c) (typ_all A) B (S n)
 | d_subs__varl : forall (E:env) (c:counter) (X:typvar) (A B:typ) (n:nat),
      binds ( X )  ( (bind_typ B) ) ( E )  ->
     d_sub_size E c B A n ->
     d_sub_size E c (typ_var_f X) A (S n)
 | d_subs__varr : forall (E:env) (c:counter) (A:typ) (X:typvar) (B:typ) (n:nat),
      binds ( X )  ( (bind_typ B) ) ( E )  ->
     d_sub_size E c A B n ->
     d_sub_size E c A (typ_var_f X) (S n).

Notation "Γ ⊢ j # A <: B" := (d_sub Γ j A B) (at level 50, j at next level, A at next level).
Notation "Γ ⊢ j # A <: B | n" := (d_sub_size Γ j A B n) (at level 50, j at next level, A at next level, B at next level).
Notation "Gamma [ A ] ~> A'"  := (d_inst Gamma A A') (at level 50).
Notation "∞" := counter_inf (at level 30).
Notation "⦲" := counter_z (at level 30).

#[local] Hint Constructors d_sub d_sub_size : core.


Lemma d_sub_size_sound : forall Γ j A B n,
  Γ ⊢ j # A <: B | n -> Γ ⊢ j # A <: B.
Proof.
  intros. induction H; eauto.
Qed.

Lemma d_sub_size_complete : forall Γ j A B,
    Γ ⊢ j # A <: B -> (exists n, Γ ⊢ j # A <: B | n).
Proof.
  intros.
  induction H; try solve [eauto | destruct_conjs; eexists; eauto].
  - intros.
    inst_cofinites_by L.
    destruct H0. exists (S x0).
    eapply d_subs__all with (L := L). intros.
    admit. (* play with ln *)
  - eexists. eapply d_subs__alll1; eauto.
    admit. (* play with ln *)
  - eexists. eapply d_subs__alll2; eauto.
    admit. (* play with ln *)
Admitted.

Fixpoint counter_plus (j1 j2 : counter) : counter :=
  match j1 with
  | counter_z => j2
  | counter_inf => j2
  | counter_suc j1' => counter_suc (counter_plus j1' j2)
  | counter_tsuc j1' => counter_tsuc (counter_plus j1' j2)
  end.

Notation "j1 +j j2" := (counter_plus j1 j2) (at level 50).

Lemma dsub_reflexivity : forall A Gamma,
    wf_env Gamma ->
    Gamma ⊢ counter_inf # A <: A.
Proof.
  induction A; intros; eauto.
  - admit.
  - admit.
Admitted.

(* general form *)
Lemma inst_inf : forall A B Gamma A' B',
    wf_env Gamma ->
    Gamma ⊢ counter_inf # A <: B ->
    d_inst Gamma A A' ->
    d_inst Gamma B B' ->
    Gamma ⊢ counter_inf # A' <: B'.
Proof with eauto.
  intros * WF Sub. generalize dependent A'. generalize dependent B'.
  dependent induction Sub; intros.
  - dependent destruction H0. dependent destruction H1. econstructor...
  - dd H0. dd H1. admit. (* binds are unique *)
  - dd H. dd H1. eapply d_sub__arr1...
  - dd H1. dd H2.
    eapply d_sub__all with (L := L).
    intros. eapply H0; eauto. admit. admit. admit. (* rename *)
  - dd H0. assert (B = B0) by admit. subst. eapply IHSub... admit.
  - dd H1. assert (B = B0) by admit. subst. eapply IHSub...   (* dual to last *)
 Admitted.


Lemma s_trans' : forall n_sub_size Γ j1 j2 A B C n1 n2,
  n1 + n2 < n_sub_size ->
  Γ ⊢ j1 # A <: B | n1 -> 
  Γ ⊢ j2 # B <: C | n2 ->
  Γ ⊢ (j1 +j j2) # A <: C.
Proof with eauto.
  intro. induction n_sub_size; intros.
  - inversion H.
  - dependent induction H0.
    + Case "refl". simpl.
      dependent destruction H2.
      * admit.
      * 
Admitted.
  

Ltac fold_open_typ_wrc_typ_rec :=
  repeat 
    match goal with 
    | H : context [open_typ_wrt_typ_rec 0 ?A ?B ] |- _ => replace (open_typ_wrt_typ_rec 0 A B) with (open_typ_wrt_typ B A) in H by auto
    | |- context [open_typ_wrt_typ_rec 0 ?A ?B ] => replace (open_typ_wrt_typ_rec 0 A B) with (open_typ_wrt_typ B A) by auto
    end.


(* a wrong statement *)
Lemma s_trans : forall n_sub_size Γ j A B C n1 n2,
  n1 + n2 < n_sub_size ->
  Γ ⊢ j # A <: B | n1 -> 
  Γ ⊢ j # B <: C | n2 -> 
  Γ ⊢ j # A <: C.
Proof with eauto.
  intro. induction n_sub_size; intros.
  - inversion H.
  - dependent destruction H0.
    + Case "refl".
      dependent destruction H2.
      * assert (A0 = B) by admit. subst.
        apply d_sub__refl...
      * dependent destruction H1.
        eapply d_sub__varl...
        eapply IHn_sub_size with (B:=B) (n1:=n)... lia. 
      * eapply d_sub__varr; eauto.
        refine (IHn_sub_size _ _ _ _ _ n _ _ _ H3). lia. 
        apply d_subs__refl...
    + Case "int".
      dependent destruction H1.
      * auto.
      * eapply d_sub__varr; eauto.
        refine (IHn_sub_size _ _ _ _ _ n _ _ _ H2)... lia.
    + eapply d_sub_size_sound...
    + dependent destruction H1.
      * constructor. 
        -- eapply IHn_sub_size with (B:=A2)... lia.
        -- eapply IHn_sub_size with (B:=B2)... lia.
      * eapply d_sub__varr...
        eapply IHn_sub_size with (B:=typ_arrow A2 B2)... lia.
    + dependent destruction H1.
      * constructor.
        refine (IHn_sub_size _ _ _ _ _ _ _ _ H1_ H0_ )... lia.  
        refine (IHn_sub_size _ _ _ _ _ _ _ _ H0_0 H1_0 )... lia.
      * eapply d_sub__varr; eauto.
        refine (IHn_sub_size _ _ _ _ _ (S (n1 + n0)) _ _ _ H1)... lia.
    + dependent destruction H1.
      * eapply d_sub__all with (L:= L `union` L0). intros. inst_cofinites_with X.
        eapply IHn_sub_size with (B:=open_typ_wrt_typ A2 (typ_var_f X))... lia.
      * eapply d_sub__varr; eauto.
        eapply IHn_sub_size with (B:=typ_all A2)... lia.
    + Case "s-forall-l".
      dependent destruction H3. 
      * pick fresh X and apply d_sub__alll1; eauto.
        inst_cofinites_with X.
        dependent destruction H1.
        -- destruct A; simpl in x; try solve [inversion x].
           ++ destruct n0; unfold open_typ_wrt_typ in x. simpl in x. inversion x.
              unfold open_typ_wrt_typ in x. simpl in x. inversion x.
           ++ unfold open_typ_wrt_typ in *. simpl in *. dependent destruction x.
              eapply IHn_sub_size with (B:=typ_arrow A1 B1) (n1:=n) (n2:=S(n1 + n2)); eauto. lia.
              constructor; eauto.
              admit.
              admit.
        -- destruct A; simpl in x; try solve [inversion x].
           ++ destruct n0; unfold open_typ_wrt_typ in x. simpl in x. inversion x.
              unfold open_typ_wrt_typ in x. simpl in x. inversion x.
           ++ unfold open_typ_wrt_typ in *. simpl in *. dependent destruction x.
              eapply IHn_sub_size with (B:=typ_arrow A1 B1) (n1:=n) (n2:=S(n1 + n2)); eauto. lia.
              constructor; eauto.
              admit.
              admit.
        -- destruct A; simpl in x; try solve [inversion x].
           ++ destruct n0; unfold open_typ_wrt_typ in x. simpl in x. inversion x.
             unfold open_typ_wrt_typ in x. simpl in x. inversion x.
           ++ unfold open_typ_wrt_typ in *. simpl in *. dependent destruction x.
              eapply IHn_sub_size with (B:=typ_arrow A1 B1) (n1:=n) (n2:=S(n1 + n2)); eauto. lia.
              constructor; auto.
              admit.
              admit.
      * eapply d_sub__alll1 with (C:=C0) (L:=L)...
        intros. inst_cofinites_with X.
        eapply IHn_sub_size with (B:=typ_all A0) (n2:=S n0)... lia.
        dependent destruction H1.
        admit.
        admit.
        admit. (* ***, counter mismatch *)
      * eapply d_sub__alll1 with (C:=C0) (L:=L)...
        intros. inst_cofinites_with X0.
        dependent destruction H1.
        -- admit.
        -- admit.
        -- admit.
      * eapply d_sub__varr; eauto.
        eapply IHn_sub_size with (B:=A0)... lia. 
    + dependent destruction H2.
      (* ∀ X. A < ∀ X. B < C *)
      * econstructor. admit. admit. (* ****,  ∀ X. A < ∀ X. B can also use forall rule and pick a different C*)
      * eapply d_sub__alll2 with (C:=C0) (L:=L)... 
        intros. inst_cofinites_with X0. 
        assert ((X0 ~ bind_typ C0 ++ E) ⊢ c # typ_var_f X <: A0 | (S n0)) by admit. (* **, d_sub_size weaken, should coutner be changed? *)
        eapply IHn_sub_size with (B:=typ_var_f X)... lia.
      * eapply d_sub__varr...
        eapply IHn_sub_size with (B:= A0)... lia.
    + eapply d_sub__varl...    
      eapply IHn_sub_size with (B:=A)... lia.
    + dependent induction H2.
      * assert (B = B0) by admit. subst. eapply d_sub_size_sound... 
      * econstructor... eapply d_sub_size_sound... 
      * assert (B = B0) by admit. subst.
        eapply IHn_sub_size with (B:=B0)... lia.
      (* A < X := B1 < Y := B2 *)
      * econstructor; eauto.
        eapply IHd_sub_size... lia.
Admitted.
   
Lemma s_trans_real : forall Γ j A B C,
  Γ ⊢ j # A <: B -> 
  Γ ⊢ j # B <: C -> 
  Γ ⊢ j # A <: C.
Proof.
  intros.
  eapply d_sub_size_complete in H.
  eapply d_sub_size_complete in H0.
  destruct_conjs.
  eapply s_trans; eauto.
Qed. 
