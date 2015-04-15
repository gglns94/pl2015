Require Export Assignment05_03.

(* problem #04: 10 points *)



Theorem iff_trans : forall P Q R : Prop, 
  (P <-> Q) -> (Q <-> R) -> (P <-> R).
Proof.
  intros.
  inversion H as [HPQ HQP].
  inversion H0 as [HQR HRQ].
  split.
  intros HP. apply HPQ in HP. apply HQR in HP. apply HP.
  intros HR. apply HRQ in HR. apply HQP in HR. apply HR.
Qed.

