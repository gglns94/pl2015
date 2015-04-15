Require Export Assignment05_38.

(* problem #39: 10 points *)

Theorem ble_nat_false : forall n m,
  ble_nat n m = false -> ~(n <= m).
Proof.
  unfold not. intros. generalize dependent n.
  induction m as [|m'].
  Case "0". intros. destruct n as [|n']. inversion H. inversion H0.
  Case "S". intros. destruct n as [|n']. inversion H. (* n = S n' *)
    simpl in H. apply IHm' in H. apply H.
  apply Sn_le_Sm__n_le_m in H0. apply H0.
Qed.
