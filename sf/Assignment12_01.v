Require Export Assignment12_00.

(* problem #01: 10 points *)

(** **** Exercise: 3 stars, optional (typing_nonexample_3)  *)
(** Another nonexample:
    ~ (exists S, exists T,
          empty |- \x:S. x x : T).
*)

Example typing_nonexample_3 :
  ~ (exists S, exists T,
        empty |- 
          (tabs X S
             (tapp (tvar X) (tvar X))) \in
          T).
Proof.
  intros C. destruct C. destruct H.
  inversion H. subst.  clear H. 
  inversion H5. subst. clear H5.
  inversion H4. subst. clear H4.
  inversion H2. subst. clear H2.
  compute in H1. compute in H3.
  rewrite H1 in H3. inversion H3. clear H1 H3.
  assert (forall T T', T = TArrow T T' -> False).
    intros. revert T' H. induction T; intros; inversion H.
    apply IHT1 in H2. inversion H2.
  apply (H T1 T12 H0).
Qed.

(*-- Check --*)
Check typing_nonexample_3 :
  ~ (exists S, exists T,
        empty |- 
          (tabs X S
             (tapp (tvar X) (tvar X))) \in
          T).

