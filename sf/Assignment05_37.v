Require Export Assignment05_36.

(* problem #37: 10 points *)

Theorem le_ble_nat : forall n m,
  n <= m ->
  ble_nat n m = true.
Proof.
  intros. generalize dependent n.
  induction m as [|m'].
  Case "m=0". intros. inversion H. reflexivity.
  Case "m=S". intros. destruct n as [|n'].
    SCase "n=0". reflexivity.
    SCase "n>0". simpl. apply IHm'. apply Sn_le_Sm__n_le_m. apply H.
Qed.  (* Note: Hint: This may be easiest to prove by induction on [m]. *)
