Require Export Assignment08_11.

(* problem #12: 10 points *)

(** **** Exercise: 3 stars, optional (CSeq_congruence)  *)
Theorem CSeq_congruence : forall c1 c1' c2 c2',
  cequiv c1 c1' -> cequiv c2 c2' ->
  cequiv (c1;;c2) (c1';;c2').
Proof.
unfold cequiv; split; intros;
inversion H1; subst; induction (H st st'0); induction (H0 st'0 st').

  apply H2 in H4.
  apply H5 in H7.
  eapply E_Seq. apply H4. apply H7.

  apply H3 in H4.
  apply H6 in H7.
  eapply E_Seq. apply H4. apply H7.
Qed.

(*-- Check --*)
Check CSeq_congruence : forall c1 c1' c2 c2',
  cequiv c1 c1' -> cequiv c2 c2' ->
  cequiv (c1;;c2) (c1';;c2').

