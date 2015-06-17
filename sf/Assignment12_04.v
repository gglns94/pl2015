Require Export Assignment12_03.

(* problem #04: 10 points *)

Corollary soundness : forall t t' T,
  empty |- t \in T -> 
  t ==>* t' ->
  ~(stuck t').
Proof.
  intros t t' T HT P. induction P; intros [R S].
  destruct (progress x T HT); auto.   
  apply IHP.  apply (preservation x y T HT H).
  unfold stuck. split; auto.
Qed.

(*-- Check --*)
Check soundness : forall t t' T,
  empty |- t \in T -> 
  t ==>* t' ->
  ~(stuck t').

