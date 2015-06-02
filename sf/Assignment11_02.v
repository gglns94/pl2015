Require Export Assignment11_01.

(* problem #02: 10 points *)

(** **** Exercise: 3 stars, advanced (value_is_nf)  *)
(** Hint: You will reach a point in this proof where you need to
    use an induction to reason about a term that is known to be a
    numeric value.  This induction can be performed either over the
    term itself or over the evidence that it is a numeric value.  The
    proof goes through in either case, but you will find that one way
    is quite a bit shorter than the other.  For the sake of the
    exercise, try to complete the proof both ways. *)

Lemma value_is_nf : forall t,
  value t -> step_normal_form t.
Proof.
unfold value. unfold normal_form. unfold not. intros. induction t; induction H.
  inversion H0. inversion H1.
  inversion H0. inversion H1.
  inversion H0. inversion H1.
  inversion H0. inversion H1.
  inversion H.
  inversion H.
  inversion H.
  inversion H0. inversion H1.
  inversion H.
  apply IHt. right. inversion H. apply H2. inversion H0. inversion H1. exists t1'. apply H3.
  inversion H.
  inversion H.
  inversion H.
  inversion H.
Qed.

(*-- Check --*)
Check value_is_nf : forall t,
  value t -> step_normal_form t.

