Require Export Assignment05_25.

(* problem #26: 10 points *)











(** 3 star (even__ev)  
    Note that proving [even__ev] directly is hard.
    You might find it easier to prove [even__ev_strong] first
    and then prove [even__ev] using it.
*)

Lemma even__ev_strong: forall n : nat, 
  (even (pred n) -> ev (pred n)) /\ (even n -> ev n).
Proof.
  intros.
  induction n as [| n'].
  Case "0". simpl. split. intros. apply ev_0. intros. apply ev_0.
  Case "S". induction n' as [|n''].
    SCase "S0". split. intros. simpl. apply ev_0. intros. inversion H.
    SCase "SS". simpl. simpl in IHn'. destruct IHn'. split.
      apply H0.
      intros. apply ev_SS in H. apply H. apply H1.
Qed. (* Note *)
 
      