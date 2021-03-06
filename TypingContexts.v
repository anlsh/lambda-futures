(* Imports *)
From Coq Require Import Arith.EqNat.
From Coq Require Import MSets.
Import ListNotations.
Require Import List.
Require Import lang_spec.
Require Import VarSet.
Require Import lang_ops.

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

Theorem restriction_makes_variable_notin :
  forall g : ty_ctx,
  forall v : var,
    ~(VarSet.In v (g -- v)).
Proof. Admitted.

Theorem restr_of_notin_makes_equal :
  forall g : ty_ctx,
  forall x : var,
  forall x_gfree : ~(VarSet.In x (bound_variables g)),
    g = (g -- x).
Proof. Admitted.

Theorem disj_vars_assoc :
  forall g1 g2 g3 : ty_ctx,
  forall disj_g12 : disj_vars g1 g2,
  forall eq_g23 : g2 = g3,
    disj_vars g1 g3.
Proof. Admitted.

Theorem ctx_union_of_eql :
  forall g1 g2 g3 : ty_ctx,
  forall disj_g12 : disj_vars g1 g2,
  forall disj_g13 : disj_vars g1 g3,
  forall eq_23 : g2 = g3,
    ctx_union g1 g2 disj_g12 = ctx_union g1 g3 disj_g13.

Proof. Admitted.

Theorem disj_notin_means_disj_with_added :
  forall g1 g2 g2subv : ty_ctx,
  forall x : var,
  forall x_g1free: ~(VarSet.In x g1),
  forall disj_g12subv : disj_vars g1 g2subv,
  forall g2subv_def : g2subv = (g2 -- x),
    disj_vars g1 g2.

Proof. Admitted.

(* Set-Theory Theorems: warning a lot of admits are gonna start being applied for
   things that are obviously true.
 *)

Theorem bound_of_union_is_union_of_bound
  : forall g1 g2 : ty_ctx,
    forall disj_g12 : disj_vars g1 g2,
      bound_variables (ctx_union g1 g2 disj_g12) = VarSet.union (bound_variables g1)
                                                                (bound_variables g2)
.
Proof. Admitted.

Theorem bound_of_restr
  : forall g : ty_ctx,
    forall x : var,
      bound_variables (g -- x) = VarSet.diff (bound_variables g) (VarSet.singleton x).
Proof. Admitted.

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

Theorem in_only_one_of_disjoint :
  forall g1 g2 : ty_ctx,
  forall v : var,
  forall v_in_g2 : VarSet.In v g2,
  forall disj_g12 : disj_vars g1 g2,
    ~ (VarSet.In v g1).
Proof. Admitted.

Theorem not_in_union_means_not_in_either :
  forall g1 g2 : ty_ctx,
  forall v : var,
  forall v_notin_union : ~(VarSet.In v (VarSet.union g1 g2)),
    ~(VarSet.In v g1).
Proof. Admitted.

Theorem in_union_means_in_one :
  forall g1 g2 : ty_ctx,
  forall v : var,
  forall disj_12 : disj_vars g1 g2,
  forall v_in_union : VarSet.In v (ctx_union g1 g2 disj_12),
    (VarSet.In v g1) \/ (VarSet.In v g2).
Proof. Admitted.

Theorem ctx_union_with_restriction :
  forall g1 g2 g2subv: ty_ctx,
  forall v : var,
  forall v_notin_g1 : ~(VarSet.In v g1),
  forall g2subv_is_g2_sub_v : (g2subv = (g2 -- v)),
  forall disj_g12subv : disj_vars g1 g2subv,
  forall disj_g12 : disj_vars g1 g2,
    (ctx_union g1 g2subv disj_g12subv) = ((ctx_union g1 g2 disj_g12) -- v).
Proof. Admitted.

Theorem restriction_from_union_where_notin_one :
  forall g1 g2 : ty_ctx,
  forall v : var,
  forall v_g1free : ~(VarSet.In v g1),
  forall disj_g12 : disj_vars g1 g2,
  forall disj_g12subv : disj_vars g1 (g2 -- v),
    ((ctx_union g1 g2 disj_g12) -- v) = ctx_union g1 (g2 -- v) disj_g12subv.
Proof. Admitted.

Theorem in_restr_ifnot_same :
  forall v x : var,
  forall v_neq_x : ~(v = x),
  forall g : ty_ctx,
    VarSet.In v (g -- x) <-> VarSet.In v g.
Proof. Admitted.

Theorem var_in_singletonctx_means_equal :
  forall v x : var,
  forall t : type,
  forall v_in_singleton_of_x : VarSet.In v (judge x t),
    v = x.
Proof. Admitted.

Theorem var_in_doubletonctx_means_equal_oneof :
  forall v v1 v2 : var,
  forall t1 t2 : type,
  forall v_in_doubleton : VarSet.In v (bound_variables (ctxu (judge v1 t1) (judge v2 t2))),
    (v = v1) \/ (v = v2).
Proof. Admitted.
