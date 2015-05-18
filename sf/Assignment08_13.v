Require Export Assignment08_12.

(* problem #13: 10 points *)

(** **** Exercise: 3 stars (CIf_congruence)  *)
Theorem CIf_congruence : forall b b' c1 c1' c2 c2',
  bequiv b b' -> cequiv c1 c1' -> cequiv c2 c2' ->
  cequiv (IFB b THEN c1 ELSE c2 FI) (IFB b' THEN c1' ELSE c2' FI).
Proof.
unfold cequiv. unfold bequiv. intros. split; induction (H0 st st'); induction (H1 st st'); intros.
  inversion H6; subst.
    apply E_IfTrue.
      rewrite (H st) in H12. apply H12.
      apply (H2 H13).
    apply E_IfFalse.
      rewrite (H st) in H12. apply H12.
      apply (H4 H13).
  inversion H6; subst.
    apply E_IfTrue.
      rewrite <- (H st) in H12. apply H12.
      apply (H3 H13).
    apply E_IfFalse.
      rewrite <- (H st) in H12. apply H12.
      apply (H5 H13).
Qed.


(*-- Check --*)
Check CIf_congruence : forall b b' c1 c1' c2 c2',
  bequiv b b' -> cequiv c1 c1' -> cequiv c2 c2' ->
  cequiv (IFB b THEN c1 ELSE c2 FI) (IFB b' THEN c1' ELSE c2' FI).

