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

  + inversion ty_prf as [g0 g1 g2subv c0 c3 disj_01 disj_02x disj_12x prf_g2subv prf_g1 | | | | | ].
    clear H H0 H1 H2 c0 c3 ty_prf G' g0.
    inversion prf_g2subv as [ | | g g2v c x prf_g2v | | | ].
    (* unfold ctx_union in *. *)
    (* rewrite <-H2 in *. *)
    (* clear H H0 H1 H2 g x c g2subv. *)
    clear H H0 H1 H2 g x c.
    (* pose (goal := ty_config_reserveplace G (ctx_union g1 g2subv disj_12x) (c1 $$ c2) v). *)
    (* pose (arg1 := ty_config_par G g1 g2subv c1 c2 disj_01 disj_02x disj_12x). *)
Admitted.

Theorem Subject_Reduction :
  forall G G' : ty_ctx,
  forall C1 C2 : config,
  forall G_C1_G' : config_has_type G C1 G',
  forall C1_StepsTo_C2 : OperationalStepsTo C1 C2,
    config_has_type G C2 G'.
Proof.
  Admitted.
