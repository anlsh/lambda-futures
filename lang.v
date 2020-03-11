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

(* Theorem cannot_type_freevars : *)
(*   forall g g' : ty_ctx, *)
(*   forall c : config, *)
(*   forall ty_prf : config_has_type g c g', *)
(*   forall x : var, *)
(*   forall x_cfree : VarSet.In x (config_freevars c), *)
(*   ~(VarSet.In x (bound_variables g')). *)
(* Proof. *)
(*   intros. *)
(*   induction c. *)
(*   + simpl in x_cfree. *)
(*     destruct ty_prf. *)

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
    clear H H0 H1 g x c.

    assert (if_v_in_g2v : (VarSet.In v g2v) -> config_has_type G (v ** (c1 $$ c2)) (ctx_union g1 g2subv disj_12x)). {
      intros v_in_g2v.
      pose (new_disj := config_gammas_disjoint (ctx_union G g1 disj_01) g2v c1 prf_g2v).
      pose (v_notin_union := in_only_one_of_disjoint (ctx_union G g1 disj_01)
                                                     g2v v v_in_g2v new_disj).
      Set Printing Coercions.
      rewrite -> bound_of_union_is_union_of_bound in v_notin_union.
      pose (v_notin := notin_union_means_notin_either (bound_variables G) (bound_variables g1)
                                                      v v_notin_union).
      destruct v_notin as [v_notin_G v_notin_g1].
      clear new_disj v_notin_union.
      pose (newprf_g1_int := prf_g1).
      symmetry in H2.
      pose (disj_g02v := disj_notin_means_disj_with_added G g2v g2subv v
                                                          v_notin_G disj_02x H2).
      pose (disj_g12v := disj_notin_means_disj_with_added g1 g2v g2subv v
                                                          v_notin_g1 disj_12x H2).
      pose (rw_util := (ctx_union_with_restriction G g2v g2subv v v_notin_G H2 disj_02x
                                                   disj_g02v)).
      rewrite -> rw_util in newprf_g1_int.
      pose (new_prf_g1 := config_ty_weakening (ctxu G g2v) g1 c2 v newprf_g1_int).

      pose (new_config_par := ty_config_par G g1 g2v c1 c2 disj_01 disj_g02v disj_g12v
                                            prf_g2v new_prf_g1).
      pose (finalprf := ty_config_reserveplace G (ctx_union g1 g2v disj_g12v) (c1 $$ c2) v
                                               new_config_par).
      pose (new_disj12x := disj_12x).
      rewrite -> H2 in new_disj12x.
      pose (restr_cfgs_same := restriction_from_union_where_notin_one g1 g2v v v_notin_g1
           disj_g12v new_disj12x).
      rewrite -> restr_cfgs_same in finalprf.
      clear restr_cfgs_same rw_util.
      (* TODO At this point the proof is actually done but for unfolding the definition
         of g2subv... Unfortunately the way I've set up disjoint proofs is really difficult
         to work with, so I'm going to leave this for later

         But anyways, I really should be able to just do an "exact finalprf" here
       *)
      Admitted.
    }

    assert (if_v_notin_g2v : ~(VarSet.In v g2v) -> config_has_type (ctxu G g2v) c2 g1). {
      intros.
      pose (g2_is_g2subv := restr_of_notin_makes_equal g2v v H).

      rewrite -> H2 in g2_is_g2subv.
      clear H2.
      symmetry in g2_is_g2subv.
      pose (disj_02 := disj_02x). rewrite -> g2_is_g2subv in disj_02.
      (* rewrite -> g2_is_g2subv in prf_g1. *)
      pose (thingy := ctx_union_of_eql G g2subv g2v disj_02x disj_02 g2_is_g2subv).
      rewrite -> thingy in prf_g1.
      (* pose (new_pconf_prf) *)
      (* assert (ctx_unions_) *)
      (* rewrite <- g2_is_g2subv in new_disj. *)
      (* unfold ctx_union in new_crp2f. *)
      (* rewrite <- g2_is_g2subv in new_crp2f. *)
      (* exact new_crp2f. *)
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
