Require Export Assignment05_32.

(* problem #33: 10 points *)

Theorem le_plus_l : forall a b,
  a <= a + b.
Proof. 
  intros.
  induction a as [|x].
  simpl. apply O_le_n.
  simpl. induction IHx. apply le_n. apply le_S. apply IHIHx.
Qed.