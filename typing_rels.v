Require Import lang_spec.
Require Import VarSet.
Require Import TypingContexts.
From Coq Require Import MSets.
Import ListNotations.

Inductive expr_has_type : ty_ctx -> expr -> type -> Prop :=
(* Constants *)
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
                      (x_gfree : disj_vars (VarSet.singleton x) g)
                      (y_gfree : disj_vars (VarSet.singleton y) g)
                      (* TODO  The direct use of ctxu is a code smell, but should be fine *)
  : config_has_type g (handledfut y x) (ctxu (judge x t) (judge y (Arrow t Unit)))
| ty_config_usedfut (g : ty_ctx) (y : var) (t : type)
                    (y_gfree : disj_vars (VarSet.singleton y) g)
  : config_has_type g (usedhandle y) (judge y (Arrow t Unit))
.

Theorem config_ty_weakening :
  forall G G' : ty_ctx,
  forall C : config,
  forall x : var,
  forall prf : config_has_type (G -- x) C G',
    config_has_type G C G'.
Proof. Admitted.
