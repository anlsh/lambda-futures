(* Imports *)
From Coq Require Import Arith.EqNat.
From Coq Require Import MSets.
Import ListNotations.
Require Import List.
Require Import lang_spec.

Module VarSet := Make(Nat_as_OT).

Inductive Judgement : Type :=
| judge (v : var) (t : type)
.

Definition ty_ctx := (list Judgement).

Definition disj_vars (s1 s2 : VarSet.t) := VarSet.Empty (VarSet.inter s1 s2).

(* Functions to convert between the different types listed above *)

Fixpoint var_to_varset (v : var) : VarSet.t :=
  VarSet.singleton v.
Coercion var_to_varset : var >-> VarSet.t.

Fixpoint bound_variables (g : ty_ctx) : VarSet.t :=
  match g with
  | nil => VarSet.empty
  | cons (judge v _) g' =>VarSet.union (VarSet.singleton v) (bound_variables g')
  end.
Coercion bound_variables : ty_ctx >-> VarSet.t.

Definition ctxu (g1 g2 : ty_ctx) := g1 ++ g2.
Definition ctx_union (g1 g2 : ty_ctx) (disjoint_proof : disj_vars g1 g2) : ty_ctx
  := ctxu g1 g2.


Fixpoint coerce_judgement_to_ty_ctx (j : Judgement) : ty_ctx :=
  cons j nil.
Coercion coerce_judgement_to_ty_ctx : Judgement >-> ty_ctx.


Fixpoint eq (n m : nat) : bool :=
  match n, m with
  | O, O => true
  | S n', S m' => eq n' m'
  | _, _ => false
  end.

Fixpoint restrict_ty_ctx (g : ty_ctx) (x : var) : ty_ctx :=
  match g with
  | nil => nil
  | cons (judge v t) g' => if (eq x v)
                           then (restrict_ty_ctx g' x)
                           else (cons (judge v t) (restrict_ty_ctx g' x))
  end.


(* Set-Theory Theorems: warning a lot of admits are gonna start being applied for
   things that are obviously true.
 *)

Theorem inter_sym : forall s1 s2 : VarSet.t,
    VarSet.inter s1 s2 = VarSet.inter s2 s1.
Proof.
  intros s1 s2. Admitted.

Theorem union_sym : forall s1 s2 : VarSet.t,
    VarSet.union s1 s2 = VarSet.union s2 s1.
Proof.
  intros s1 s2. Admitted.

Theorem ctxu_sym : forall s1 s2 : ty_ctx,
    ctxu s1 s2 = ctxu s2 s1.
Proof. intros. Admitted.

Theorem ctxu_assoc : forall s1 s2 s3 : ty_ctx,
    ctxu s1 (ctxu s2 s3) = ctxu (ctxu s1 s2) s3.
Proof. intros. Admitted.

Theorem disj_vars_sym :
  forall s1 s2 : ty_ctx,
  forall disj_s1_s2 : (disj_vars s1 s2),
    (disj_vars s2 s1).
Proof. intros. unfold disj_vars in *. rewrite -> inter_sym. assumption.
Qed.

Theorem dvars_distrib :
  forall s1 s2 s3 : ty_ctx,
  forall d1_2 : disj_vars s1 s2,
  forall d12_3 : disj_vars (bound_variables (ctxu s1 s2)) s3,
    (and (disj_vars s1 s3) (disj_vars s2 s3)).
Proof. intros. Admitted.


Theorem ctxu_subset :
  forall g1 g2 g2a g2b : ty_ctx,
  forall g2_decomp : g2 = ctxu g2a g2b,
  forall disj_g12 : disj_vars g1 g2,
    disj_vars g1 g2a.
Proof. intros. Admitted.

Theorem mutuallydisjoint_gets :
  forall g1 g2 g3 : ty_ctx,
  forall disj_g1_g2 : disj_vars g1 g2,
  forall disj_g1_g3 : disj_vars g1 g3,
  forall disj_g2_g2 : disj_vars g2 g3,
    disj_vars (bound_variables (ctxu g1 g2)) g3.
Proof. Admitted.


Theorem mutuallydisjoint_getsv2 :
  forall g1 g2 g3 : ty_ctx,
  forall disj_g1_g2 : disj_vars g1 g2,
  forall disj_g1_g3 : disj_vars g1 g3,
  forall disj_g2_g2 : disj_vars g2 g3,
    disj_vars g1 (bound_variables (ctxu g2 g3)).
Proof. Admitted.


(* Theorem union_subset : forall s s1 s2 : VarSet.t, forall prf : s = VarSet.union s1 s2, *)
(*     VarSet.Subset s1 s. *)
(* Proof. intros s s1 s2 k. Admitted. *)

(* Theorem subset_of_empty : forall s1 s2 : VarSet.t, forall s2_empty : VarSet.Empty s2, *)
(*       forall s1_sub_s2 : VarSet.Subset s1 s2, *)
(*         VarSet.Empty s1. *)
(* Proof. intros. Admitted. *)

(* Theorem inter_with_subset_is_subset_of_inter : forall s1 s2 s2a : VarSet.t, *)
(*     forall s2a_sub_s2 : VarSet.Subset s2a s2, *)
(*     VarSet.Subset (VarSet.inter s1 s2a) (VarSet.inter s1 s2). *)
(* Proof. Admitted. *)

(* Theorem disj_vars_over_sym1 : forall g1 g2 g3 : ty_ctx, *)
(*     forall disj_12 : (disj_vars g1 g2), *)
(*     disj_vars (bound_variables (ctxu g1 g2)) g3 = disj_vars g1 (bound_variables (ctxu g2 g3)). *)
(* Proof. intros. Admitted. *)


(* Set Nested Proofs Allowed. *)
(* Set Printing Coercions. *)
(* Lemma disj_vars_over_intersections : forall ga gb gc : ty_ctx, *)
(*     forall disj_ga_gb : disj_vars ga gb, *)
(*     forall disj_gab_c : disj_vars (bound_variables (ctxu ga gb)) gc, *)
(*       disj_vars (bound_variables (ctxu ga gb)) gc = disj_vars (bound_variables (ctxu ga gc)) gb. *)
(* Proof. intros. Admitted. *)

(* Theorem disj_vars_sym : forall s1 s2 : VarSet.t, (iff (disj_vars s1 s2) (disj_vars s2 s1)). *)
(* Proof. *)
(*   intros s1 s2. unfold disj_vars. *)
(*   unfold iff. *)
(*   refine (conj _ _ ). *)
(*   { intros h. rewrite <- inter_sym. assumption. } *)
(*   { intros h. rewrite -> inter_sym. assumption. } *)
(* Qed. *)

(* Theorem disj_vars_subset : forall g gsub gsup : ty_ctx, *)
(*     forall gsub_subset_gup : VarSet.Subset gsub gsup, *)
(*       disj_vars g gsup -> disj_vars g gsub. *)
(* Proof. *)
(*   intros. unfold disj_vars in H. unfold disj_vars. *)
(*   pose (ik := inter_with_subset_is_subset_of_inter (bound_variables g) *)
(*        (bound_variables gsup) (bound_variables gsub) gsub_subset_gup). *)
(*   exact (subset_of_empty (VarSet.inter (bound_variables g) (bound_variables gsub)) *)
(*                          (VarSet.inter (bound_variables g) (bound_variables gsup)) *)
(*                          H ik). *)
(* Qed. *)

(* Theorem ctx_union_sym : forall g1 g2 : ty_ctx, *)
(*   (* This theorem is actually false, since contexts are currently backed with lists *) *)
(*     forall p1 : (disj_vars g1 g2), forall p2 : (disj_vars g2 g1), *)
(*     ctx_union g1 g2 p1 = ctx_union g2 g1 p2. *)
(* Proof. *)
(*   intros. *)
(*   unfold ctx_union. *)
(*   apply ctxu_sym. *)
(* Qed. *)

(* Theorem ctxu_unions_vars : forall g g1 g2 : ty_ctx, forall disj : disj_vars g1 g2, *)
(*   forall gpartition : g = ctx_union g1 g2 disj, *)
(*   (bound_variables g) = VarSet.union (bound_variables g1) (bound_variables g2). *)
(* Proof. *)
(*   intros g g1 g2 disj gpart. *)
(*   unfold ctx_union in gpart. *)
(* Admitted. *)
