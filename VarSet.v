From Coq Require Import MSets.
Require Import lang_spec.

Module VarSet := Make(Nat_as_OT).
Definition disj_vars (s1 s2 : VarSet.t) := VarSet.Empty (VarSet.inter s1 s2).

Definition var_to_varset (v : var) := VarSet.singleton v.
Coercion var_to_varset : var >-> VarSet.t.

Theorem axiom_inter_sym : forall s1 s2 : VarSet.t,
    VarSet.inter s1 s2 = VarSet.inter s2 s1.
Proof.
  intros s1 s2. Admitted.

Theorem axiom_union_sym : forall s1 s2 : VarSet.t,
    VarSet.union s1 s2 = VarSet.union s2 s1.
Proof.
  intros s1 s2. Admitted.

Theorem union_with_empty : forall s1 : VarSet.t,
    VarSet.union s1 VarSet.empty = s1.
Proof. Admitted.

Theorem disj_vars_sym :
  forall s1 s2 : VarSet.t,
  forall disj_s1_s2 : (disj_vars s1 s2),
    (disj_vars s2 s1).
Proof. intros. unfold disj_vars in *. rewrite -> axiom_inter_sym. assumption.
Qed.

(* Elementary Set Theory Stuff? *)
Theorem inter_with_subset :
  forall s1 s2 sub_s2 : VarSet.t,
  forall sub_prf : VarSet.Subset sub_s2 s2,
    VarSet.Subset (VarSet.inter s1 sub_s2) (VarSet.inter s1 s2).
Proof. Admitted.

Theorem subset_of_empty :
  forall s sub_s : VarSet.t,
  forall s_empty : VarSet.Empty s,
  forall sub_prf : VarSet.Subset sub_s s,
    VarSet.Empty sub_s.
Proof. Admitted.

Theorem neq_means_disjoint :
  forall x y : var,
  forall neq_xy : ~(x = y),
    VarSet.Empty (VarSet.inter (VarSet.singleton x) (VarSet.singleton y)).
Proof. Admitted.

Theorem mdisj_rassoc :
  forall s1 s2 s3 : VarSet.t,
  forall disj_s12 : VarSet.Empty (VarSet.inter s1 s2),
  forall disj_s13 : VarSet.Empty (VarSet.inter s1 s3),
  forall disj_s23 : VarSet.Empty (VarSet.inter s2 s3),
    VarSet.Empty (VarSet.inter s1 (VarSet.union s2 s3)).
Proof. Admitted.

Theorem notin_union_means_notin_either :
  forall g1 g2 : VarSet.t,
  forall v : var,
  forall v_notin_union : ~(VarSet.In v (VarSet.union g1 g2)),
    ~(VarSet.In v g1) /\ ~(VarSet.In v g2).
Proof. Admitted.

Theorem disj_means_disj_with_subset :
  forall g1 g2 subg2: VarSet.t,
  forall disj_g12 : (disj_vars g1 g2),
  forall prf_subsert : VarSet.Subset subg2 g2,
    (disj_vars g1 subg2).
Proof. Admitted.

Theorem inl_means_in_union :
  forall v : var,
  forall v1 v2 : VarSet.t,
  forall inl : VarSet.In v v1,
    VarSet.In v (VarSet.union v1 v2).
Proof. Admitted.

Theorem in_diff_ifnot_same :
  forall v x : var,
  forall v_neq_x : ~(v = x),
  forall vset : VarSet.t,
    VarSet.In v vset <-> VarSet.In v (VarSet.diff vset (VarSet.singleton x)).
Proof. Admitted.

Theorem in_singleton :
  forall x : var,
    VarSet.In x (VarSet.singleton x).
Proof. Admitted.

Theorem disj_var_singleton_means_notin :
  forall v : var,
  forall varset : VarSet.t,
    ~(VarSet.In v varset) <-> (disj_vars (VarSet.singleton v) varset).
Proof. Admitted.
