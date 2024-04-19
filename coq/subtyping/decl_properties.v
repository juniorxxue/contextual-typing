Require Import Bool.
Require Import Metalib.Metatheory.
Require Import List.
Require Import subtyping.decl.
Require Import subtyping.prop_ln.

Notation "T |- j # A <: B" := (d_sub T j A B) (at level 20).

Lemma s_trans : forall Gamma A B C j,
    d_sub Gamma j A B ->
    d_sub Gamma j B C ->
    d_sub Gamma j A C.
Proof.
  intros.  
Admitted.
  
            
    
