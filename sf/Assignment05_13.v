Require Export Assignment05_12.

(* problem #13: 10 points *)



(** 2 stars, optional (beq_nat_false)  *)
Theorem beq_nat_false : forall n m,
  beq_nat n m = false -> n <> m.
Proof.
  intros.
  generalize dependent m.
  unfold not. induction n as [|n'].
  Case "0". induction m as [|m'].
    SCase "00". intros. inversion H.
    SCase "0S". intros. inversion H0.
  Case "S". induction m as [|m'].
    SCase "S0". intros. inversion H0.
    SCase "SS". intros. apply (IHn' m'). simpl in H. apply H. inversion H0. reflexivity.
Qed. (* Note *)