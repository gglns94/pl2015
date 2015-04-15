Require Export Assignment05_24.

(* problem #25: 10 points *)









(** 3 stars, optional (ev_plus_plus)  *)
(** Here's an exercise that just requires applying existing lemmas.  No
    induction or even case analysis is needed, but some of the rewriting
    may be tedious. 
    Hint: You can use [plus_comm], [plus_assoc], [double_plus], [double_even], [ev_sum], [ev_ev__ev].
*)
Check plus_comm.
Check plus_assoc.
Check double_plus.
Check double_even.
Check ev_sum.
Check ev_ev__ev.

Theorem ev_plus_plus : forall n m p,
  ev (n+m) -> ev (n+p) -> ev (m+p).
Proof.
  intros.
  apply ev_sum with (n := n+m) (m := n+p) in H.
  rewrite plus_assoc in H.
  rewrite <- plus_assoc with ( n := n ) (m := m) (p := n) in H.
  rewrite plus_comm with (n:= m) (m := n) in H.
  rewrite plus_assoc in H.
  rewrite <- double_plus in H.
  rewrite <- plus_assoc in H.
  apply ev_ev__ev with (n:=(double n)) in H.
  apply H.
  apply double_even.
  apply H0.
Qed.

