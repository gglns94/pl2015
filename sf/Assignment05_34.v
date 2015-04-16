Require Export Assignment05_33.

(* problem #34: 10 points *)

Lemma plus_n_O : forall n, n + 0 = n.
Proof. intros. induction n. reflexivity. simpl. rewrite IHn. reflexivity. Qed.

Lemma plus_n_1: forall n, S n = 1 + n.
Proof. intros. simpl. reflexivity. Qed.

Lemma plus_assoc : forall m n o, (m + n) + o = m + (n + o).
Proof. intros. induction m. simpl. reflexivity. simpl. rewrite IHm. reflexivity. Qed.

Lemma plus_comm_1 : forall n, n + 1 = 1 + n.
Proof. intros. induction n. reflexivity. simpl. rewrite IHn. simpl. reflexivity. Qed.
(*
Lemma plus_comm : forall n m, n + m = m + n.
Proof. intros. induction n as [|n']. simpl. rewrite plus_n_O. reflexivity. rewrite plus_n_1.
  rewrite <- plus_assoc. rewrite plus_comm_1. rewrite plus_assoc. rewrite plus_assoc. rewrite IHn'. reflexivity.
Qed.
*)
Theorem plus_lt : forall n1 n2 m,
  n1 + n2 < m ->
  n1 < m /\ n2 < m.
Proof.
  unfold lt.
  intros.
  induction m as [|m'].
    Case "m=0". inversion H.
    Case "m=S". apply Sn_le_Sm__n_le_m in H. split.
      apply n_le_m__Sn_le_Sm. apply le_trans with (n := (n1+n2)). apply le_plus_l. apply H.
      apply n_le_m__Sn_le_Sm. apply le_trans with (n := (n1+n2)). rewrite plus_comm.
      apply le_plus_l. apply H.
Qed.