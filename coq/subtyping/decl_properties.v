Require Import Coq.Program.Equality.
Require Import Bool.
Require Import Metalib.Metatheory.
Require Import List.
Require Import subtyping.decl.
Require Import subtyping.prop_ln.

Notation "Γ |- j # A <: B" := (d_sub Γ j A B) (at level 50, j at level 0, A at next level).


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
      ( forall X , X \notin  L  -> d_sub_size  ( X ~ (bind_typ C)  ++  E )  c  ( open_typ_wrt_typ A (typ_var_f X) )  B n)  ->
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

Notation "Γ |- j # A <: B | n" := (d_sub_size Γ j A B n) (at level 50, j at level 0, A at next level, B at next level).


Lemma s_trans : forall Γ j A B C n1 n2 n_sub_size,
    n1 + n2 < n_sub_size ->
    Γ |- j # A <: B | n1 -> 
    Γ |- j # B <: C | n2 -> 
    Γ |- j # A <: C.
Proof with eauto.
Admitted.
  
            
    
