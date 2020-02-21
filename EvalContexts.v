(* Evaluation Context Definitions *)

Require Import lang_spec.

Inductive ctx_f : Type :=
| hole
| ecf_left (l : ctx_f) (r : expr)
| ecf_right (v : val) (r : ctx_f)
.

Inductive ctx_e : Type :=
| ece_cons (v : var) (F : ctx_f)
.

Inductive ctx_ff : Type :=
| apply_to_val (F : ctx_f) (v : val)
| exch_with_val (F : ctx_f) (v : val)
.


Inductive ctx_ef : Type :=
| f_ece_cons (x : var) (FF : ctx_ff)
.

(* Functions for substituting into the holes in Evaluation Contexts *)

Fixpoint SubExprInF (hole_item : expr) (F : ctx_f) : expr :=
  match F with
  | hole => hole_item
  | ecf_left F' r => app (SubExprInF hole_item F') r
  | ecf_right v F' => app v (SubExprInF hole_item F')
  end.

Fixpoint SubFInF (hole_item : ctx_f) (F : ctx_f) : ctx_f :=
  match F with
  | hole => hole_item
  | ecf_left F' r => ecf_left (SubFInF hole_item F') r
  | ecf_right v F' => ecf_right v (SubFInF hole_item F')
  end.

Fixpoint SubInE (hole_item : expr) (E : ctx_e) : config :=
  match E with
  | ece_cons v F => (v <- (SubExprInF hole_item F))
  end.

(* Coercions so that the substitution functions can be re-used *)

Fixpoint coerce_FF_to_F (FF : ctx_ff) : ctx_f :=
  match FF with
  | apply_to_val F v => SubFInF (ecf_left hole v) F
  | exch_with_val F v => SubFInF (ecf_left (ecf_right (value_c exch) hole) v)
                                         F
  end.
Coercion coerce_FF_to_F : ctx_ff >-> ctx_f.

Definition coerce_fe_to_e (ef : ctx_ef) : ctx_e :=
  match ef with
  | f_ece_cons x FF => ece_cons x FF
  end.
Coercion coerce_fe_to_e : ctx_ef >-> ctx_e.
