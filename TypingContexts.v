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


Theorem disj_vars_sym : forall s1 s2 : VarSet.t, (iff (disj_vars s1 s2) (disj_vars s2 s1)).
Proof.
  intros s1 s2. unfold disj_vars.

  assert (inter_sym : VarSet.inter s1 s2 = VarSet.inter s2 s1). {
    admit.
   }
  unfold iff.
  refine (conj _ _ ).
  { intros h. rewrite <- inter_sym. assumption. }
  { intros h. rewrite -> inter_sym. assumption. }
Admitted.

Definition ctx_union (g1 g2 : ty_ctx) (disjoint_proof : disj_vars g1 g2) : ty_ctx
  := g1 ++ g2.
Theorem ctx_union_sym : forall g1 g2 : ty_ctx,
  (* This theorem is actually false, since contexts are currently backed with lists *)
    forall p1 : (disj_vars g1 g2), forall p2 : (disj_vars g2 g1),
    ctx_union g1 g2 p1 = ctx_union g2 g1 p2.
Proof.
  intros.
  unfold ctx_union.
  admit.
Admitted.

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
