Require Export Assignment08_06.

(* problem #07: 10 points *)

(** **** Exercise: 2 stars (IFB_false)  *)
Theorem IFB_false: forall b c1 c2,
  bequiv b BFalse  ->
  cequiv 
    (IFB b THEN c1 ELSE c2 FI) 
    c2.
Proof.
unfold bequiv. unfold cequiv. intros. split; intros.
  inversion H0; subst.
    assert (H':=(H st)). rewrite H6 in H'. inversion H'.
    apply H7.
  apply E_IfFalse.
    apply (H st).
    apply H0.
Qed.

(*-- Check --*)
Check IFB_false: forall b c1 c2,
  bequiv b BFalse  ->
  cequiv 
    (IFB b THEN c1 ELSE c2 FI) 
    c2.

