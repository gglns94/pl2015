Require Export Assignment06_01.

(* problem #02: 10 points *)

(** **** Exercise: 3 stars, optional (not_exists_dist)  *)
(** (The other direction of this theorem requires the classical "law
    of the excluded middle".) *)

Theorem not_exists_dist :
  excluded_middle ->
  forall (X:Type) (P : X -> Prop),
    ~ (exists x, ~ P x) -> (forall x, P x).
Proof.
  unfold excluded_middle. unfold not. intros.
  assert (P x \/ (P x -> False)). (* Note *)
  apply H with (P := P x).
  inversion H1. apply H2.
  assert (exists x : X, P x -> False).
  apply ex_intro with (witness := x). apply H2. apply H0 in H3. inversion H3.
Qed.