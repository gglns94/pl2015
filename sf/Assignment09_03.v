Require Export Assignment09_02.

(* problem #03: 10 points *)

(** **** Exercise: 4 stars (hoare_asgn_wrong)  *)
(** The assignment rule looks backward to almost everyone the first
    time they see it.  If it still seems backward to you, it may help
    to think a little about alternative "forward" rules.  Here is a
    seemingly natural one:
      ------------------------------ (hoare_asgn_wrong)
      {{ True }} X ::= a {{ X = a }}
    Give a counterexample showing that this rule is incorrect
    (informally). Hint: The rule universally quantifies over the
    arithmetic expression [a], and your counterexample needs to
    exhibit an [a] for which the rule doesn't work. *)

Theorem hoare_asgn_wrong:
  exists a, ~ {{ fun st => True }} X ::= a {{ fun st => st X = aeval st a}}.
Proof.
unfold hoare_triple. exists (APlus (AId X) (ANum 1)). unfold not. intros. simpl in H.
assert (H' := (H (update empty_state X 0) (update (update empty_state X 0) X 1))).
assert ((X ::= APlus (AId X) (ANum 1)) / update empty_state X 0
     || update (update empty_state X 0) X 1) as H''.
  constructor. reflexivity.
apply H' in H''. simpl in H''. inversion H''.
reflexivity.
Qed.

(*-- Check --*)
Check hoare_asgn_wrong:
  exists a, ~ {{ fun st => True }} X ::= a {{ fun st => st X = aeval st a}}.

