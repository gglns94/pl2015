Require Export Assignment08_05.

(* problem #06: 10 points *)

(** **** Exercise: 2 stars (skip_right)  *)
(** Prove that adding a SKIP after a command results in an equivalent
    program *)

Theorem skip_right: forall c,
  cequiv 
    (c;; SKIP) 
    c.
Proof.
unfold cequiv. intros. split.
  intros. inversion H. subst. inversion H5. subst. apply H2.
  intros. assert (H':=(E_Seq c SKIP st st' st' H)). apply H'. apply E_Skip.
Qed.

(*-- Check --*)
Check skip_right: forall c,
  cequiv 
    (c;; SKIP) 
    c.

