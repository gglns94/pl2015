Require Export Assignment05_37.

(* problem #38: 10 points *)

Theorem ble_nat_true_trans : forall n m o,
  ble_nat n m = true -> ble_nat m o = true -> ble_nat n o = true.                               
Proof.
  intros.
  apply le_ble_nat. Search le.
  apply ble_nat_true in H.
  apply ble_nat_true in H0.
apply le_trans with (n := m).
  apply H. apply H0.
Qed.
(* Note: Hint: This theorem can be easily proved without using [induction]. *)
  
