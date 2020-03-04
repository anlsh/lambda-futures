(* Imports *)
From Coq Require Import Arith.EqNat.
From Coq Require Import MSets.
Import ListNotations.
Require Import List.
Require Import lang_spec.
Require Import VarSet.

Inductive Judgement : Type :=
| judge (v : var) (t : type)
.

Definition ty_ctx := (list Judgement).

(* Functions to convert between the different types listed above *)

Fixpoint bound_variables (g : ty_ctx) : VarSet.t :=
  match g with
  | nil => VarSet.empty
  | cons (judge v _) g' => VarSet.union (VarSet.singleton v) (bound_variables g')
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

Notation "g -- x" := (restrict_ty_ctx g x) (at level 71, left associativity).

Theorem restriction_commutative :
  forall g : ty_ctx,
  forall v1 v2 : var,
  (g -- v1 -- v2) = (g -- v2 -- v1).
Proof. Admitted.

Theorem restriction_makes_subset :
  forall g : ty_ctx,
  forall v : var,
    VarSet.Subset (g -- v) g.
Proof. Admitted.

(* Set-Theory Theorems: warning a lot of admits are gonna start being applied for
   things that are obviously true.
 *)

Theorem dvars_distrib :
  forall s1 s2 s3 : ty_ctx,
  forall d1_2 : disj_vars s1 s2,
  forall d12_3 : disj_vars (bound_variables (ctxu s1 s2)) s3,
    (and (disj_vars s1 s3) (disj_vars s2 s3)).
Proof. intros. Admitted.

Theorem ctxu_sym : forall s1 s2 : ty_ctx,
    ctxu s1 s2 = ctxu s2 s1.
Proof. intros. Admitted.

Theorem ctxu_assoc : forall s1 s2 s3 : ty_ctx,
    ctxu s1 (ctxu s2 s3) = ctxu (ctxu s1 s2) s3.
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
