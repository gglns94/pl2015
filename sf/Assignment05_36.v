Require Export Assignment05_35.

(* problem #36: 10 points *)

Theorem ble_nat_true : forall n m,
  ble_nat n m = true -> n <= m.
Proof.
  induction n as [|n'].
  intros. apply O_le_n.
  induction m as [|m'].
  intros. inversion H.
  intros. apply n_le_m__Sn_le_Sm. apply IHn'. simpl in H. apply H.
Qed. (* Note : forall !!*)