(* Imports *)
Require Import lang_spec.
From Coq Require Import MSets.
Require Import List.
Import ListNotations.
From Coq Require Import Arith.EqNat.

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

Inductive ctx_join :=
| join_double (g1 g2 : ty_ctx)
              (disjoint_proof : disj_vars g1 g2)
.

Fixpoint coerce_ctx_join (dj : ctx_join) : ty_ctx :=
  match dj with
  | join_double g1 g2 _ => g1 ++ g2
  end.
Coercion coerce_ctx_join : ctx_join >-> ty_ctx.

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
