Require Import lang_spec.
Require Import EvalContexts.
Require Import TypingContexts.

Definition v_notin_set (x : var) (s : VarSet.t) :=
  VarSet.Empty (VarSet.inter (VarSet.singleton x) s).

(* TODO There has to be a library function for this somewhere but I can't find it *)
Fixpoint eq (n m : nat) : bool :=
  match n, m with
  | O, O => true
  | S n', S m' => eq n' m'
  | _, _ => false
  end.

Fixpoint substitute (e : expr) (s : expr) (x : var) : expr :=
  match e with
  | evar y =>
    if eq x y then s else e
  | (econst c) => e
  | lam y T e' =>
    if (eq x y) then e else lam y T (substitute e' s x)
  | e1 @ e2 => (substitute e1 s x) @ (substitute e2 s x)
  end.


(* TODO I'm sure that I'm not defining free variables (in exprs and configs) correctly *)
Fixpoint expr_freevars (e : expr) : VarSet.t :=
  match e with
  | evar y => VarSet.singleton y
  | econst c => VarSet.empty
  | lam y T e' => VarSet.diff (expr_freevars e') (VarSet.singleton y)
  | e1 @ e2 => VarSet.union (expr_freevars e1) (expr_freevars e2)
  end.

Fixpoint config_freevars (c : config) : VarSet.t :=
  match c with
  | (c1 $$ c2) => VarSet.union (config_freevars c1) (config_freevars c2)
  | x ** c => VarSet.diff (config_freevars c) (VarSet.singleton x)
  | cellmake x v => VarSet.empty
  | (x <- e) => VarSet.diff (expr_freevars e) (VarSet.singleton x)
  | h ~ x => VarSet.empty
  | h ~ used => VarSet.empty
  end.

Inductive expr_stepsto : expr -> expr -> Prop :=
| step_beta x A e1 e2 : expr_stepsto ((lam x A e1) @ e2) (substitute e1 e2 x)
| step_left e1 e2 e1' :
    expr_stepsto e1 e1' -> expr_stepsto (e1 @ e2) (e1' @ e2)
| step_right e1 e2 e2' :
    expr_stepsto e2 e2' -> expr_stepsto (e1 @ e2) (e1 @ e2')
| step_body x A e e' : expr_stepsto e e' -> expr_stepsto (lam x A e) (lam x A e')
.

(* Structural Congruence and Relations... *)

Inductive structcong : config -> config -> Prop :=
| cong_conc_commut (c1 c2 : config)
  : structcong (c1 $$ c2) (c2 $$ c1)
| cong_conc_assoc (c1 c2 c3 : config)
  : structcong ((c1 $$ c2) $$ c3) (c1 $$ (c2 $$ c3))
| cong_newplace_commut (c : config) (v1 v2 : var)
  : structcong (v1 ** (v2 ** c)) (v2 ** (v1 ** c))
| cong_newplace_distrib (c1 c2 : config) (v : var)
                        (vfree : v_notin_set v (config_freevars c1))
  : structcong ((v ** c1) $$ c2) (v ** (c1 $$ c2))
.

(* TODO This needs to be condensed :| *)
Inductive OperationalStepsTo : config -> config -> Prop :=
| ost_beta (E : ctx_e) (lam_bind : var) (lam_bind_T : type) (lam_body : expr)
           (v : val)
  : OperationalStepsTo (SubInE ((lam lam_bind lam_bind_T lam_body) @ v) E)
                       (SubInE (substitute lam_body v lam_bind) E)
| ost_newthread (E : ctx_e) (v : val) (y : var)
                (vfree : v_notin_set y (config_freevars (SubInE v E)))
  : OperationalStepsTo (SubInE (thread @ v) E)
                       ((y ** (SubInE y E)) $$ (threadval y (v @ y)))
| ost_future_deref (EF : ctx_ef) (y : var) (v : val)
  : OperationalStepsTo ((SubInE y EF) $$ (threadval y v))
                       ((SubInE v EF) $$ (threadval y v))
| ost_handle_new (E : ctx_e) (v : val) (y z : var)
                 (yfree : v_notin_set y (config_freevars (SubInE v E)))
                 (zfree : v_notin_set z (config_freevars (SubInE v E)))
  : OperationalStepsTo (SubInE (handle @ v) E)
                       (y ** z ** (SubInE (v @ y @ z) E) $$ (z ~ y))
| ost_handle_bind (E : ctx_e) (z y : var) (v : val)
  : OperationalStepsTo ((SubInE (z @ v) E) $$ (z ~ y))
                       ((SubInE unit E) $$ (threadval y v) $$ (usedhandle z))
| ost_cell_new (E : ctx_e) (v : val) (y : var)
               (yfree : v_notin_set y (config_freevars (SubInE v E)))
  : OperationalStepsTo (SubInE (cell @ v) E)
                       (y ** ((SubInE y E) $$ y c= v))
| ost_cell_exch (E : ctx_e) (y : var) (v1 v2 : val)
  : OperationalStepsTo ((SubInE (exch @ y @ v1) E) $$ y c= v2)
                       ((SubInE v2 E) $$ y c= v1)
.

Inductive expr_has_type : ty_ctx -> expr -> type -> Prop :=
(* Constants *)
(* TODO Folding typing of constants into typing of expressions might be suspect *)
| ty_const_unit (g : ty_ctx) : expr_has_type g unit Unit
| ty_const_thread (g : ty_ctx) (t : type) : expr_has_type g thread ((t >> t) >> t)
| ty_const_handle (g : ty_ctx) (t1 t2 : type) : expr_has_type g handle ((t1 >> (t1 >> Unit) >> t2) >> t2)
| ty_const_cell (g : ty_ctx) (t : type) : expr_has_type g cell (t >> (Ref t))
| ty_const_exch (g : ty_ctx) (t : type) : expr_has_type g exch ((Ref t) >> t >> t)
(* General Expressions *)
| ty_var (g : ty_ctx) (x : var) (t : type) (xfree : v_notin_set x g)
  : expr_has_type (join_double (judge x t) g xfree) x t
| ty_lam (g : ty_ctx) (x : var) (e : expr) (t1 t2 : type) (xfree : v_notin_set x g)
         (_ : expr_has_type (join_double (judge x t1) g xfree) e t2)
  : expr_has_type g (lam x t1 e) (t1 >> t2)
| ty_app (g : ty_ctx) (e1 e2 : expr) (t1 t2 : type)
         (_ : expr_has_type g e1 (t1 >> t2))
         (_ : expr_has_type g e2 t2)
  : expr_has_type g (e1 @ e2) t2
.
