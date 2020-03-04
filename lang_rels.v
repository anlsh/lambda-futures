Require Import lang_spec.
Require Import lang_ops.
Require Import VarSet.
Require Import EvalContexts.

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
                        (vfree : disj_vars v (config_freevars c2))
  : structcong ((v ** c1) $$ c2) (v ** (c1 $$ c2))
.

(* TODO This needs to be condensed :| *)
Inductive OperationalStepsTo : config -> config -> Prop :=
| ost_beta (E : ctx_e) (lam_bind : var) (lam_bind_T : type) (lam_body : expr)
           (v : val)
  : OperationalStepsTo (SubInE ((lam lam_bind lam_bind_T lam_body) @ v) E)
                       (SubInE (substitute lam_body v lam_bind) E)
| ost_newthread (E : ctx_e) (v : val) (y : var)
                (vfree : disj_vars y (config_freevars (SubInE v E)))
  : OperationalStepsTo (SubInE (thread @ v) E)
                       ((y ** (SubInE y E)) $$ (threadval y (v @ y)))
| ost_future_deref (EF : ctx_ef) (y : var) (v : val)
  : OperationalStepsTo ((SubInE y EF) $$ (threadval y v))
                       ((SubInE v EF) $$ (threadval y v))
| ost_handle_new (E : ctx_e) (v : val) (y z : var)
                 (yfree : disj_vars y (config_freevars (SubInE v E)))
                 (zfree : disj_vars z (config_freevars (SubInE v E)))
  : OperationalStepsTo (SubInE (handle @ v) E)
                       (y ** z ** (SubInE (v @ y @ z) E) $$ (z ~ y))
| ost_handle_bind (E : ctx_e) (z y : var) (v : val)
  : OperationalStepsTo ((SubInE (z @ v) E) $$ (z ~ y))
                       ((SubInE unit E) $$ (threadval y v) $$ (usedhandle z))
| ost_cell_new (E : ctx_e) (v : val) (y : var)
               (yfree : disj_vars y (config_freevars (SubInE v E)))
  : OperationalStepsTo (SubInE (cell @ v) E)
                       (y ** ((SubInE y E) $$ y c= v))
| ost_cell_exch (E : ctx_e) (y : var) (v1 v2 : val)
  : OperationalStepsTo ((SubInE (exch @ y @ v1) E) $$ y c= v2)
                       ((SubInE v2 E) $$ y c= v1)
.
