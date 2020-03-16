Require Import lang_spec.
Require Import lang_ops.
Require Import lang_rels.
Require Import typing_rels.
Require Import EvalContexts.
Require Import TypingContexts.
Require Import VarSet.

Require Import List.
Import ListNotations.

Theorem config_gammas_disjoint
  : forall G G' : ty_ctx,
    forall C : config,
    forall prf : config_has_type G C G',
      disj_vars G G'.
Proof.
  intros G G' C prf.
  induction prf.
    + unfold ctx_union in *.
      pose (prf := mutuallydisjoint_gets g1 g2 g g1_g2 (disj_vars_sym g g1 g_g1)).
      apply disj_vars_sym in prf.
      exact prf.
      pose (prf3 := disj_vars_sym g g2 g_g2).
      exact prf3.
    + unfold disj_vars in *.
      simpl in *.
      rewrite -> (union_with_empty (VarSet.singleton x)).
      rewrite -> axiom_inter_sym.
      exact disj_prf.
    + unfold disj_vars in *.
      simpl.
      pose (subset_prf := restriction_makes_subset g' x).
      pose (bound_subset := inter_with_subset (bound_variables g)
                                              (bound_variables g')
                                              (bound_variables (g' -- x))
                                              subset_prf).
      exact (subset_of_empty (VarSet.inter (bound_variables g) (bound_variables g'))
                             (VarSet.inter (bound_variables g) (bound_variables (g' -- x)))
                             IHprf bound_subset).
    + unfold coerce_judgement_to_ty_ctx in *.
      simpl.
      unfold disj_vars in *.
      rewrite -> (union_with_empty (VarSet.singleton x)).
      rewrite -> axiom_inter_sym.
      exact x_gfree.
    + simpl. rewrite -> union_with_empty.
      pose (disj_xy := neq_means_disjoint x y x_not_y).
      unfold disj_vars in *.
      rewrite -> axiom_inter_sym in x_gfree.
      rewrite -> axiom_inter_sym in y_gfree.
      exact (mdisj_rassoc g (VarSet.singleton x) (VarSet.singleton y)
                          x_gfree y_gfree disj_xy).
    + unfold disj_vars in *.
      simpl in *.
      rewrite -> (union_with_empty (VarSet.singleton y)).
      rewrite -> axiom_inter_sym.
      exact y_gfree.
Qed.

Theorem typing_describes_declvars :
  forall g g': ty_ctx,
  forall c : config,
  forall ty_prf : config_has_type g c g',
    (bound_variables g') = (config_declvars c).
Proof.
  intros.
  induction ty_prf.
  +simpl.
    rewrite -> (bound_of_union_is_union_of_bound g1 g2 g1_g2).
    rewrite -> IHty_prf1.
    rewrite -> IHty_prf2.
    rewrite -> (axiom_union_sym (config_declvars c2) (config_declvars c1)).
    reflexivity.
  + simpl. apply union_with_empty.
  + simpl. rewrite -> bound_of_restr. rewrite -> IHty_prf. reflexivity.
  + simpl. apply union_with_empty.
  + simpl. rewrite -> union_with_empty. rewrite -> axiom_union_sym. reflexivity.
  + simpl. rewrite -> union_with_empty. reflexivity.
Qed.

Theorem typed_means_freevar :
  forall g g' : ty_ctx,
  forall c : config,
  forall typing_proof : config_has_type g c g',
  forall v : var,
  forall v_in_g' : VarSet.In v (bound_variables g'),
    VarSet.In v (config_freevars c).
Proof.
  intros g g' c ty_prf v.
  generalize dependent g.
  generalize dependent g'.
  induction c.
  + intros.
    inversion ty_prf as [g0 g1 g2 c0 c3 disj_01 disj_02 disj_12 prf_g2 prf_g1
                        | | | | | ].
    rewrite <- H2 in *.
    clear H H0 H1 H2 c0 c3.
    simpl.
    destruct (in_union_means_in_one g1 g2 v disj_12 v_in_g') as [inl | inr].
    {
      pose (foo := IHc2 g1 (ctx_union g g2 disj_02) prf_g1 inl).
      rewrite -> axiom_union_sym.
      exact (inl_means_in_union v (config_freevars c2) (config_freevars c1) foo).
    }
    {
      pose (foo := IHc1 g2 (ctx_union g g1 disj_01) prf_g2 inr).
      exact (inl_means_in_union v (config_freevars c1) (config_freevars c2) foo).
    }
  + intros.
    simpl.
    rename g' into g'x.
    rename v_in_g' into v_in_g'x.
    inversion ty_prf as [ | | g0 g' c0 x0 prf_g' | | | ].
    rewrite <- H2 in *.
    clear H0 H1 H2 x0 H g0.
    assert (v_eq_x
            : (v = x)
              -> VarSet.In v (VarSet.diff (config_freevars c) (VarSet.singleton x))). {
      intros v_eq_x.
      rewrite -> v_eq_x in *.
      pose (v_notin_g'x := restriction_makes_variable_notin g' x).
      contradiction.
    }
    assert (v_neq_x
            : ~(v = x)
              -> VarSet.In v (VarSet.diff (config_freevars c) (VarSet.singleton x))). {
      clear v_eq_x.
      intros v_neq_x.
      destruct (in_restr_ifnot_same v x v_neq_x g') as [a1 _].
      pose (arg := a1 v_in_g'x).
      pose (arg2 := IHc g' g prf_g' arg).
      destruct (in_diff_ifnot_same v x v_neq_x (config_freevars c)) as [f1 _].
      exact (f1 arg2).
    }
    (* TODO: I have A -> goal, ~A -> goal. I just need to figure out how to compose those
       to get the goal *)
    admit.
  + intros. simpl.
    inversion ty_prf as [ | g0 x0 t val | | | | ].
    rewrite <- H1 in *.
    rewrite <- H2 in *.
    clear H H0 H1 v0 g0 x0 H2 disj_prf vprf ty_prf.
    pose (v_eq_x := var_in_singletonctx_means_equal v x (Ref t) v_in_g').
    rewrite -> v_eq_x.
    exact (inl_means_in_union x (VarSet.singleton x) (expr_freevars val) (in_singleton x)).
  + intros.
    simpl.
    inversion ty_prf as [ | | | g0 x0 t e0 x_gfree _ | | ].
    rewrite <- H2 in *.
    clear H H0 H1 H2 g0 x0 e0.
    pose (v_eq_x := var_in_singletonctx_means_equal v x t v_in_g').
    rewrite -> v_eq_x.
    rewrite -> axiom_union_sym.
    exact (inl_means_in_union x (VarSet.singleton x) (expr_freevars e) (in_singleton x)).
  + intros. simpl.
    inversion ty_prf as [| | | | g0 x0 y0 t x_not_y x_gfree y_gfree H0 H1 H2 |].
    rewrite <- H2 in *.
    clear H H1 H0 x0 y0 g0 x_gfree y_gfree x_not_y ty_prf H2.
    destruct (var_in_doubletonctx_means_equal_oneof v x y t (t >> Unit) v_in_g') as [v_eq_x | v_eq_y].
    {
      rewrite -> axiom_union_sym. rewrite -> v_eq_x.
      exact (inl_means_in_union x (VarSet.singleton x) (VarSet.singleton y) (in_singleton x)).
    }
    {
      rewrite -> v_eq_y.
      exact (inl_means_in_union y (VarSet.singleton y) (VarSet.singleton x) (in_singleton y)).
    }
  + intros. simpl.
    inversion ty_prf as [| | | | | g0 y0 t _].
    clear H H0 H1 ty_prf.
    pose (v_eq_y := var_in_singletonctx_means_equal v y (t >> Unit) v_in_g').
    rewrite -> v_eq_y.
    exact (in_singleton y).
Admitted.

Theorem var_in_doubletonctx_means_equal_oneof :
  forall v v1 v2 : var,
  forall t1 t2 : type,
  forall v_in_doubleton : VarSet.In v (bound_variables (ctxu (judge v1 t1) (judge v2 t2))),
    (v = v1) \/ (v = v2).
Proof. Admitted.

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
  + inversion ty_prf as [ | | g gx c0 x ty_prf_v2 H H0 | | | ].
    clear H H0 H1 c0.
    rewrite <- H2 in *. clear H2.
    inversion ty_prf_v2 as [ | | g2 g' c02 x2 ty_prf_all H2 H02 | | | ].
    rewrite <- H1 in *.
    clear H H1 c02 H2 H02 x2 g2 G' g gx x ty_prf.

    pose (ty_prf_v1 := ty_config_reserveplace G g' c v1 ty_prf_all).
    pose (ty_prf_v1_v2 := ty_config_reserveplace G (g' -- v1) (v1 ** c) v2 ty_prf_v1).

    rewrite -> restriction_commutative in ty_prf_v1_v2.
    exact ty_prf_v1_v2.

  + inversion ty_prf as [g0 g1 g2v c0 c3 disj_01 disj_02v disj_12v prf_g2v prf_g1 | | | | | ].
    clear H H0 H1 H2 c0 c3 ty_prf G' g0.
    inversion prf_g2v as [ | | g g2 c x prf_g2 | | | ].
    clear H H0 H1 g x c.

    assert (if_v_in_g2
            : (VarSet.In v g2)
              -> config_has_type G (v ** (c1 $$ c2)) (ctx_union g1 g2v disj_12v)).
    {
      intros v_in_g2.
      pose (new_disj := config_gammas_disjoint (ctx_union G g1 disj_01) g2 c1 prf_g2).
      pose (v_notin_union := in_only_one_of_disjoint (ctx_union G g1 disj_01)
                                                     g2 v v_in_g2 new_disj).
      Set Printing Coercions.
      rewrite -> bound_of_union_is_union_of_bound in v_notin_union.
      pose (v_notin := notin_union_means_notin_either (bound_variables G) (bound_variables g1)
                                                      v v_notin_union).
      destruct v_notin as [v_notin_G v_notin_g1].
      clear new_disj v_notin_union.
      pose (newprf_g1_int := prf_g1).
      symmetry in H2.
      pose (disj_02 := disj_notin_means_disj_with_added G g2 g2v v
                                                         v_notin_G disj_02v H2).
      pose (disj_12 := disj_notin_means_disj_with_added g1 g2 g2v v
                                                        v_notin_g1 disj_12v H2).
      pose (rw_util := (ctx_union_with_restriction G g2 g2v v v_notin_G H2 disj_02v
                                                   disj_02)).
      rewrite -> rw_util in newprf_g1_int.
      pose (new_prf_g1 := config_ty_weakening (ctxu G g2) g1 c2 v newprf_g1_int).

      pose (new_config_par := ty_config_par G g1 g2 c1 c2 disj_01 disj_02 disj_12
                                            prf_g2 new_prf_g1).
      pose (finalprf := ty_config_reserveplace G (ctx_union g1 g2 disj_12) (c1 $$ c2) v
                                               new_config_par).
      pose (new_disj12v := disj_12v).
      rewrite -> H2 in new_disj12v.
      pose (restr_cfgs_same := restriction_from_union_where_notin_one g1 g2 v v_notin_g1
                                                                      disj_12 new_disj12v).
      rewrite -> restr_cfgs_same in finalprf.
      clear restr_cfgs_same rw_util.
      (* TODO At this point the proof is actually done but for unfolding the definition
         of g2subv... Unfortunately the way I've set up disjoint proofs is really difficult
         to work with, so I'm going to leave this for later

         But anyways, I really should be able to just do an "exact finalprf" here
       *)
      admit.
    }

    assert (if_v_notin_g2
            : ~(VarSet.In v g2)
              -> config_has_type G (v ** (c1 $$ c2)) (ctx_union g1 g2v disj_12v)). {
      clear if_v_in_g2.
      intros v_notin_g2v.
    }

Admitted.

Theorem Subject_Reduction :
  forall G G' : ty_ctx,
  forall C1 C2 : config,
  forall G_C1_G' : config_has_type G C1 G',
  forall C1_StepsTo_C2 : OperationalStepsTo C1 C2,
    config_has_type G C2 G'.
Proof.
  Admitted.
