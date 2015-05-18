Require Export Assignment08_09.

(* problem #10: 10 points *)

(** **** Exercise: 2 stars, optional (seq_assoc)  *)
Theorem seq_assoc : forall c1 c2 c3,
  cequiv ((c1;;c2);;c3) (c1;;(c2;;c3)).
Proof.
intros. revert c2 c3.
unfold cequiv; split; intros. 

inversion H. subst. inversion H2. subst.
assert (H' := (E_Seq c2 c3 st'1 st'0 st' H7 H5)).
assert (H'' := (E_Seq c1 (c2;;c3) st st'1 st' H3 H')).
apply H''.

inversion H. subst. inversion H5. subst.
assert (H' := (E_Seq c1 c2 st st'0 st'1 H2 H3)).
assert (H'' := (E_Seq (c1;;c2) c3 st st'1 st' H' H7)).
apply H''.
Qed.

(*-- Check --*)
Check seq_assoc : forall c1 c2 c3,
  cequiv ((c1;;c2);;c3) (c1;;(c2;;c3)).

