Require Import Autosubst.Autosubst.
Require Import Coq.Program.Equality.

(* ------- Syntax --------------- *)  

Inductive type :=
| Int
| Top
| Arr (A B : type).  

Inductive term :=
| Lit (n : nat)
| Var (x : var)
| Lam (e : {bind term})
| App (e1 e2 : term)
| Ann (e : term) (A : type).

Instance Ids_term : Ids term. derive. Defined.
Instance Rename_term : Rename term. derive. Defined.
Instance Subst_term : Subst term. derive. Defined.
Instance SubstLemmas_term : SubstLemmas term. derive. Qed.

(* ------- Typing --------------- *)

Inductive htype :=
| HInt
| HTop
| HArr (A B : htype)
| Hole (e : term).

Fixpoint rename_htype (A : htype) Γ : htype :=
  match A with
  | HInt => HInt
  | HTop => HTop
  | HArr A B => HArr (rename_htype A Γ) (rename_htype B Γ)
  | Hole e => Hole (e.[ren Γ])
  end.

Fixpoint type_is_htype (A : type) : htype :=
  match A with
  | Int => HInt
  | Top => HTop
  | Arr A B => HArr (type_is_htype A) (type_is_htype B)
  end.

Coercion type_is_htype : type >-> htype.

Inductive ty (Γ : var -> type) : htype -> term -> type -> Prop :=
| Ty_Lit  A n :
  sub Γ Int A ->
  ty Γ A (Lit n) Int     
| Ty_Var A B x :
  Γ x = B -> sub Γ B A ->
  ty Γ A (Var x) B     
| Ty_App e1 e2 A C D :
  ty Γ (HArr (Hole e2) A) e1 (Arr C D) ->
  ty Γ A (App e1 e2) D     
| Ty_Ann A (B : type) C e :
  ty Γ B e C -> sub Γ B A ->
  ty Γ A (Ann e B) B     
| Ty_Lam1 e1 e A B B':
  ty Γ Top e1 A ->
  ty (A .: Γ) B' e B ->
  ty Γ (HArr (Hole e1) B') (Lam e) (Arr A B)     
| Ty_Lam2 e A B' C :
  ty (A .: Γ) B' e C ->
  ty Γ (HArr A B') (Lam e) (Arr A C)
with sub (Γ : var -> type) : htype -> htype -> Prop :=
| S_Refl        : sub Γ HInt HInt
| S_Top A       : sub Γ A HTop
| S_Arr A B C D : sub Γ C A -> sub Γ B D -> sub Γ (HArr A B) (HArr C D)
| S_Hole A A' e : ty Γ A e A' -> sub Γ (Hole e) A.

Scheme ty_mut := Induction for ty Sort Prop with sub_mut := Induction for sub Sort Prop.

Notation "A → B" := (Arr A B) (at level 20).
Notation "A *→ B" := (HArr A B) (at level 20).
Notation "⟦ e ⟧" := (Hole e) (at level 20).

Notation "G ⊢ A ⇒ e ⇒ B" := (ty G A e B) (at level 50).
Notation "G ⊢ A <: B" := (sub G A B) (at level 50).

(** Weakening Lemma *)
Check sub_ind.
Check sub_mut.

Lemma rename_type_eq : forall (t : type) ξ, rename_htype t ξ = t.
Proof.
  intros. induction t; eauto.
  simpl in *. rewrite IHt1. rewrite IHt2.
  auto.
Qed.

Lemma sub_ren :
  forall Γ A B, sub Γ A B -> forall Δ ξ, Γ = ξ >>> Δ -> sub Δ (rename_htype A ξ) (rename_htype B ξ).
Proof.
  
  Check sub_mut.
  intros Γ A B H.
  pattern Γ, A, B, H.
  eapply sub_mut with
    (
      P := fun Γ A e B h => forall Δ ξ, Γ = ξ >>> Δ -> ty Δ (rename_htype A ξ) e.[ren ξ] B
    )
  ; intros; eauto.
  (* Typing *)
  - simpl in *. eapply Ty_Lit; eauto.
  - subst. simpl in *. econstructor; eauto.
    specialize (H0 Δ ξ (eq_refl _)).
    rewrite (rename_type_eq _ _) in H0.
    auto.
  - econstructor. eapply H0; eauto.
  - econstructor.
    + pose proof (rename_type_eq B0 ξ).
      specialize (H0 Δ ξ). rewrite H3 in H0. eapply H0. assumption.
    + pose proof (rename_type_eq B0 ξ).
      specialize (H1 Δ ξ). rewrite H3 in H1. eapply H1. assumption.
  - simpl in *. econstructor; eauto.
    admit.
  - admit.
    (* Subtyping *)
  - simpl. econstructor.
  - simpl. econstructor.
  - simpl. econstructor; eauto.
  - simpl. econstructor. eapply H0; eauto.
Admitted.


Lemma ty_ren Γ e A B:
  ty Γ B e A -> forall Δ ξ, Γ = ξ >>> Δ -> ty Δ B e.[ren ξ] A.
Proof.
Admitted.
  
Lemma ty_sub : forall A B e G,
    ty G A e B ->
    sub G B A.
Proof.
  intros. dependent induction H.
  - assumption.
  - assumption.
  - dependent destruction IHty. assumption.
  - assumption.
  - eapply S_Arr.
    + admit.
    + eapply ty_ren in H0; eauto. admit.
Admitted.
