Require Import lang_spec.

Require Import List.
Import ListNotations.

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

Inductive ctx_join :=
| join_single (g : ty_ctx)
| join_double (g1 g2 : ty_ctx)
              (disjoint_proof : VarSet.Empty (VarSet.inter (bound_variables g1)
                                                           (bound_variables g2)))
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

Coercion bound_variables : ty_ctx >-> VarSet.t.
