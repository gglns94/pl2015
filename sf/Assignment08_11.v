Require Export Assignment08_10.

(* problem #11: 10 points *)

(** **** Exercise: 2 stars (assign_aequiv)  *)
Theorem assign_aequiv : forall X e,
  aequiv (AId X) e -> 
  cequiv SKIP (X ::= e).
Proof.
unfold cequiv. split; intros.

inversion H0. subst.
unfold aequiv in H.
assert (aeval st' e= st' X).
  rewrite <- (H st'). reflexivity.
apply E_Ass with (x:=X) in H1.
assert (st' = update st' X (st' X)).
  apply functional_extensionality. intros. unfold update. destruct (eq_id_dec X x); subst; reflexivity.
rewrite <- H2 in H1. apply H1.

inversion H0. subst.
unfold aequiv in H. rewrite <- (H st). simpl.
assert (st = update st X (st X)).
  apply functional_extensionality. intros. unfold update. destruct (eq_id_dec X x); subst; reflexivity.
rewrite <- H1. apply E_Skip.
Qed.

(*-- Check --*)
Check assign_aequiv : forall X e,
  aequiv (AId X) e -> 
  cequiv SKIP (X ::= e).

