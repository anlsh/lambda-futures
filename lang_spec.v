Set Warnings "-notation-overridden,-parsing".
From Coq Require Import Arith.

(* Defining variables as nats is basically a convenience because the String_as_OT item
   from the OrderedTypeEx module is broken, so using strings is out *)
Definition var := nat.

Inductive type : Type :=
| Unit
| Arrow (a : type) (b : type)
| Ref (a : type)
.

Inductive const : Type :=
| unit
| cell
| exch
| thread
| handle
.

Inductive expr : Type :=
| evar (x : var)
| econst (c : const)
| lam (x : var) (T : type) (e : expr)
| app (e1 : expr) (e2 : expr)
.

Inductive val : Type :=
| value_var (x : var)
| value_c (c : const)
| value_lam (x : var) (T : type) (e : expr)
| value_exch (v : val).

Inductive config : Type :=
| conc (c1 : config) (c2 : config)
| newplace (x : var) (c : config)
| cellmake (x : var) (v : expr)
| threadval (x : var) (e : expr)
| handledfut (y : var) (x : var)
| usedhandle (y : var)
.

(* Notation and Coercions *)

Notation "t1 '>>' t2" := (Arrow t1 t2) (at level 90, right associativity).
Notation "f @ g" := (app f g) (at level 71, left associativity).

Notation "c1 $$ c2" := (conc c1 c2) (at level 93, left associativity).
Notation "x '<-' e" := (threadval x e) (at level 91).
Notation "h ~ x" := (handledfut h x) (at level 91).
Notation "h ~ 'used'" := (usedhandle h) (at level 91).
Notation "x 'c=' v" := (cellmake x v) (at level 91).
Notation "x ** cfg" := (newplace x cfg) (at level 92, right associativity).

(* Coercions between the various types *)

Definition coerce_const_to_val (c : const) : val :=
  value_c c.
Coercion coerce_const_to_val : const >-> val.

Definition coerce_var_to_val (x : var) : val :=
  value_var x.
Coercion coerce_var_to_val : var >-> val.

Fixpoint coerce_val_to_expr (v : val) : expr :=
  match v with
  | value_var x => (evar x)
  | value_lam x T e => lam x T e
  | value_c c => (econst c)
  | value_exch v => (app (econst exch) (coerce_val_to_expr v))
  end.
Coercion coerce_val_to_expr : val >-> expr.
