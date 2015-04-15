Require Export Assignment05_34.

(* problem #35: 10 points *)

Theorem lt_S : forall n m,
  n < m ->
  n < S m.
Proof.
  unfold lt. intros.
  apply le_trans with (n := m).
  apply H. apply le_S. apply le_n.
Qed.

