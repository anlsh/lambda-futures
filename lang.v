Require Import lang_spec.
Require Import EvalContexts.
Require Import TypingContexts.

Require Import List.
Import ListNotations.

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

Inductive expr_has_type : ty_ctx -> expr -> type -> Prop :=
(* Constants *)
(* TODO Folding typing of constants into typing of expressions might be suspect *)
| ty_const_unit (g : ty_ctx) : expr_has_type g unit Unit
| ty_const_thread (g : ty_ctx) (t : type) : expr_has_type g thread ((t >> t) >> t)
| ty_const_handle (g : ty_ctx) (t1 t2 : type) : expr_has_type g handle ((t1 >> (t1 >> Unit) >> t2) >> t2)
| ty_const_cell (g : ty_ctx) (t : type) : expr_has_type g cell (t >> (Ref t))
| ty_const_exch (g : ty_ctx) (t : type) : expr_has_type g exch ((Ref t) >> t >> t)
(* General Expressions *)
| ty_var (g : ty_ctx) (x : var) (t : type) (xfree : disj_vars (VarSet.singleton x) g)
  : expr_has_type (ctx_union (judge x t) g xfree) x t
| ty_lam (g : ty_ctx) (x : var) (e : expr) (t1 t2 : type)
         (xfree : disj_vars (VarSet.singleton x) g)
         (_ : expr_has_type (ctx_union (judge x t1) g xfree) e t2)
  : expr_has_type g (lam x t1 e) (t1 >> t2)
| ty_app (g : ty_ctx) (e1 e2 : expr) (t1 t2 : type)
         (_ : expr_has_type g e1 (t1 >> t2))
         (_ : expr_has_type g e2 t2)
  : expr_has_type g (e1 @ e2) t2
.

Inductive config_has_type : ty_ctx -> config -> ty_ctx -> Prop :=
| ty_config_par (g g1 g2 : ty_ctx) (c1 c2 : config)
                (g_g1 : disj_vars g g1) (g_g2 : disj_vars g g2) (g1_g2 : disj_vars g1 g2)
                (p1 : config_has_type (ctx_union g g1 g_g1) c1 g2)
                (p2 : config_has_type (ctx_union g g2 g_g2) c2 g1)
  : config_has_type g (c1 $$ c2) (ctx_union g1 g2 g1_g2)
| ty_config_ref (g : ty_ctx) (x : var) (t : type) (v : val)
                (disj_prf : disj_vars (VarSet.singleton x) g)
                (vprf : expr_has_type (ctx_union (judge x (Ref t)) g disj_prf) v t)
  : config_has_type g (x c= v) (judge x (Ref t))
| ty_config_reserveplace (g g': ty_ctx) (c : config) (x : var)
                         (h : config_has_type g c g')
  : config_has_type g (x ** c) (restrict_ty_ctx g' x)
| ty_config_threadval (g : ty_ctx) (x : var) (t : type) (e : expr)
                      (x_gfree : disj_vars (VarSet.singleton x) g)
                      (h : expr_has_type (ctx_union (judge x t) g x_gfree) e t)
  : config_has_type g (threadval x e) (judge x t)
| ty_config_handledfut(g : ty_ctx) (x y : var) (t : type)
                      (x_not_y : ~(x = y))
  : config_has_type g (handledfut y x) [ (judge x t) ; (judge y (Arrow t Unit))]
| ty_config_usedfut (g : ty_ctx) (y : var) (t : type)
                    (y_gfree : disj_vars (VarSet.singleton y) g)
  : config_has_type g (usedhandle y) [judge y (Arrow t Unit)]
.

Theorem Congruence_Preserves_Typing
  : forall g g': ty_ctx, forall c1 c2 : config,
    forall ty_prf : config_has_type g c1 g', forall cong_prf : structcong c1 c2,
    (config_has_type g c2 g').
Proof.

  intros G G'.
  intros C_Orig C_Final ty_prf cong_prf.
  destruct cong_prf.
  + inversion ty_prf as [g0 g1 g2 cc0 cc1
                            disj_01 disj_02 disj_12
                            prf_c1 prf_c2  is_g0_G
                            tr1 tr2
                        | | | | | ].
    clear tr1 tr2 H is_g0_G.
    pose (witness := ty_config_par G g2 g1 c2 c1 disj_02 disj_01
                                   (disj_vars_sym g1 g2 disj_12)
                                   prf_c2 prf_c1).
    unfold ctx_union in *.
    rewrite -> ctxu_sym.
    assumption.
  + inversion ty_prf as [g0 g1 g2 c0 c4
                            disj_g01 disj_g02 disj_g12
                            prf_g2 prf_g1
                        | | | | |].
    clear g0 c0 c4 H H0 H1 H2 ty_prf.

    inversion prf_g2 as [ g g2a g2b
                            c0 c4
                            disj_g01_2a disj_g01_2b disj_g2a2b
                            prf_g2b prf_g2a
                        | | | | |].

    clear g c0 c4 H H0 H1.
    rename H2 into g2_is_join2a2b.
    unfold ctx_union in *. rewrite <- g2_is_join2a2b.
    symmetry in g2_is_join2a2b.
    rewrite -> g2_is_join2a2b in prf_g1. rewrite -> (ctxu_sym g2a g2b) in prf_g1.
        rewrite -> ctxu_assoc in prf_g1.
    rewrite <- (ctxu_assoc) in prf_g2a. rewrite -> (ctxu_sym g1 g2b) in prf_g2a.
        rewrite -> (ctxu_assoc) in prf_g2a.

    pose (g2_is_join2b2a := g2_is_join2a2b). rewrite -> ctxu_sym in g2_is_join2b2a.
    pose (disj_g1_2b := ctxu_subset g1 g2 g2b g2a g2_is_join2b2a disj_g12).
    pose (disj_g0_2b := ctxu_subset G g2 g2b g2a g2_is_join2b2a disj_g02).
    pose (disj_g_g2b_g1 := mutuallydisjoint_gets G g2b g1 disj_g0_2b disj_g01
                                                  (disj_vars_sym g1 g2b disj_g1_2b)).


    pose (disj_g1_2a := ctxu_subset g1 g2 g2a g2b g2_is_join2a2b disj_g12).
    pose (disj_g0_2a := ctxu_subset G g2 g2a g2b g2_is_join2a2b disj_g02).
    pose (disj_g_g2b_g2a := mutuallydisjoint_gets G g2b g2a disj_g0_2b disj_g0_2a
                                                  (disj_vars_sym g2a g2b disj_g2a2b)).

    pose (new_prf' := ty_config_par (ctxu G g2b) g1 g2a c2 c3
                                   disj_g_g2b_g1 disj_g_g2b_g2a
                                   disj_g1_2a).
    unfold ctx_union in new_prf'.
    pose (new_prf := new_prf' prf_g2a prf_g1). unfold new_prf' in new_prf. clear new_prf'.

    pose (arg1 := (mutuallydisjoint_getsv2 G g1 g2a disj_g01 disj_g0_2a disj_g1_2a)).
    pose (arg2 := (mutuallydisjoint_gets g1 g2a g2b disj_g1_2a disj_g1_2b disj_g2a2b)).
    rewrite <- ctxu_assoc in prf_g2b.
    pose (final_prf := ty_config_par G (ctxu g1 g2a) g2b c1 (c2 $$ c3)
                                     arg1 disj_g0_2b arg2 prf_g2b new_prf).
    unfold ctx_union in final_prf.
    rewrite <- ctxu_assoc in final_prf.
    exact final_prf.
  + inversion ty_prf as [ | | g g' c0 x h H H0 | | | ].
    clear H H0 H1 c0.
    rewrite <- H2 in *. clear H2.
    admit.
  + admit.
Admitted.

Theorem Subject_Reduction :
  forall G G' : ty_ctx,
  forall C1 C2 : config,
  forall G_C1_G' : config_has_type G C1 G',
  forall C1_StepsTo_C2 : OperationalStepsTo C1 C2,
    config_has_type G C2 G'.
Proof.
  Admitted.
