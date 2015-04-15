Require Export Assignment05_13.

(* problem #14: 10 points *)




(** 2 star (ev__even)  *)
Theorem ev__even: forall n : nat,
  ev n -> even n.
Proof.
  intros.
  induction H.
  unfold even. simpl. reflexivity.
  unfold even. simpl. unfold even in IHev. apply IHev.
Qed.