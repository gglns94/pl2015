Require Export Assignment05_20.

(* problem #21: 10 points *)





(** 2 stars (ev_sum)  *)

Theorem ev_sum : forall n m,
   ev n -> ev m -> ev (n+m).
Proof.
  intros.
  induction H.
  Case "0". induction H0.
    SCase "00". simpl. apply ev_0.
    SCase "0S". simpl. apply ev_SS. apply H0.
  Case "S". simpl. apply ev_SS. apply IHev.
Qed.




