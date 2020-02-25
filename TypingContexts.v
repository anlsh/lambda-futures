Require Import lang_spec.
From Coq Require Import MSets.
Require Import List.
Import ListNotations.

Module VarSet := Make(Nat_as_OT).

(* Definition v_notin_set (x : var) (s : VarSet.t) := *)
(*   VarSet.Empty (VarSet.inter (VarSet.singleton x) s). *)

(* Definition v_notin_set (x : var) (s : VarSet.t) := ~(VarSet.In x s). *)
Fixpoint var_to_varset (v : var) : VarSet.t :=
  VarSet.singleton v
.

Coercion var_to_varset : var >-> VarSet.t.

Definition disj_vars (s1 s2 : VarSet.t) := VarSet.Empty (VarSet.inter s1 s2).

Inductive Judgement : Type :=
| judge (v : var) (t : type)
.

Definition ty_ctx := (list Judgement).

Inductive Contains_tctx_judgement : ty_ctx -> Judgement -> Prop :=
| contains_hd (j : Judgement) (g : ty_ctx)
  : Contains_tctx_judgement (cons j g) j
| contains_tl (j1 j2 : Judgement) (g : ty_ctx) (_ : Contains_tctx_judgement g j2)
  : Contains_tctx_judgement (cons j1 g) j2
.

Fixpoint bound_variables (g : ty_ctx) : VarSet.t :=
  match g with
  | nil => VarSet.empty
  | cons (judge v _) g' =>VarSet.union (VarSet.singleton v) (bound_variables g')
  end.
Coercion bound_variables : ty_ctx >-> VarSet.t.

Inductive ctx_join :=
| join_single (g : ty_ctx)
| join_double (g1 g2 : ty_ctx)
              (disjoint_proof : disj_vars g1 g2)
.

Fixpoint coerce_ctx_join (dj : ctx_join) : ty_ctx :=
  match dj with
  | join_single g => g
  | join_double g1 g2 _ => g1 ++ g2
  end
.
Coercion coerce_ctx_join : ctx_join >-> ty_ctx.

Fixpoint coerce_judgement_to_ty_ctx (j : Judgement) : ty_ctx :=
  cons j nil
.
Coercion coerce_judgement_to_ty_ctx : Judgement >-> ty_ctx.
