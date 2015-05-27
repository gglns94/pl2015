Require Export Assignment09_05.

(* problem #06: 10 points *)

(** **** Exercise: 2 stars (slow_assignment)  *)
(** A roundabout way of assigning a number currently stored in [X] to
    the variable [Y] is to start [Y] at [0], then decrement [X] until
    it hits [0], incrementing [Y] at each step. Here is a program that
    implements this idea:
      {{ X = m }}
    Y ::= 0;;
    WHILE X <> 0 DO
      X ::= X - 1;;
      Y ::= Y + 1
    END
      {{ Y = m }} 
    Write an informal decorated program showing that this is correct. *)

Theorem slow_assignment : forall m,
    {{ fun st => st X = m }}
    Y ::= ANum 0;;
    WHILE BNot (BEq (AId X) (ANum 0)) DO
      X ::= AMinus (AId X) (ANum 1);;
      Y ::= APlus (AId Y) (ANum 1)
    END
    {{ fun st => st Y = m }}.
Proof.
destruct m.

unfold hoare_triple. intros. inversion H. subst. inversion H3. subst. inversion H6; subst.
reflexivity.
inversion H4. apply negb_true in H2. apply beq_nat_false in H2. unfold update in H2.
destruct (eq_id_dec Y X). omega. rewrite H0 in H2. omega.

apply hoare_seq with (Q:=(fun st:state => st X + st Y = S m)).
eapply hoare_consequence_post.
eapply hoare_while.
apply hoare_seq with (Q:= (fun st:state => st X + st Y = m)).

  unfold hoare_triple. intros. inversion H. subst. unfold update. simpl. omega.

  unfold hoare_triple. intros. inversion H. subst. unfold update. simpl. inversion H0.
  simpl in H2. apply negb_true in H2. apply beq_nat_false in H2. omega.

unfold assert_implies. intros. inversion H. simpl in H1. apply negb_false in H1. apply beq_nat_true in H1. omega.
unfold hoare_triple. intros. inversion H. subst. unfold update. simpl. omega.
Qed.

(*-- Check --*)
Check slow_assignment : forall m,
    {{ fun st => st X = m }}
    Y ::= ANum 0;;
    WHILE BNot (BEq (AId X) (ANum 0)) DO
      X ::= AMinus (AId X) (ANum 1);;
      Y ::= APlus (AId Y) (ANum 1)
    END
    {{ fun st => st Y = m }}.
  
