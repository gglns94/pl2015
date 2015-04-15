Require Export Assignment05_26.

(* problem #27: 10 points *)


Theorem even__ev: forall n : nat,
  even n -> ev n.
Proof.
  intros n.
  induction n as [|n'].
  Case "0". intros. apply ev_0.
  Case "S". apply even__ev_strong. (* Note *)
Qed.

