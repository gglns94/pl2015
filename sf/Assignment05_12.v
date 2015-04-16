Require Export Assignment05_11.

(* problem #12: 10 points *)


Lemma exfalso : forall P : Prop,
  False -> P.
Proof.
intros.
inversion H.
Qed.


(** 2 stars (false_beq_nat)  *)
Theorem false_beq_nat : forall n m : nat,
     n <> m ->
     beq_nat n m = false.
Proof.
intros.
generalize dependent m.
  induction n as [|n'].
  Case "0".
    intros. destruct m as [|m']. apply exfalso. apply H. reflexivity. simpl. reflexivity.
  Case "pos".
    intros. destruct m as [|m']. simpl. reflexivity.
    simpl. apply IHn'. unfold not. unfold not in H. intros. rewrite H0 in H. apply H. reflexivity.
Qed. (* Note *)