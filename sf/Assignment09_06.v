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

(*
  {{ X = m }}
  Y ::= 0;;
  {{ X = m /\ Y = 0}} ->>
  {{ X + Y = m }}
  WHILE X <> 0 DO
    {{ X + Y = m /\ X <> 0 }} ->>
    {{ X + Y = m }}[X|->X-1][Y|->Y-1]
    X ::= X - 1;;
    {{ X + Y = m }}[Y|->Y-1]
    Y ::= Y + 1
    {{ X + Y = m }}
  END
  {{ X + Y = m /\ X = 0 }} ->>
  {{ Y = m }} 
*)

Theorem slow_assignment : forall m,
    {{ fun st => st X = m }}
    Y ::= ANum 0;;
    WHILE BNot (BEq (AId X) (ANum 0)) DO
      X ::= AMinus (AId X) (ANum 1);;
      Y ::= APlus (AId Y) (ANum 1)
    END
    {{ fun st => st Y = m }}.
Proof.
intros.
eapply hoare_seq.
  eapply hoare_consequence_post with 
  (Q' := fun st:state => st X + st Y = m /\ beval st (BNot (BEq (AId X) (ANum 0))) =false).
    eapply hoare_while.
    eapply hoare_consequence_pre.
      eapply hoare_seq.
        eapply hoare_asgn.
        eapply hoare_asgn.
          unfold assert_implies. intros. induction H. simpl in H0. apply negb_true in H0. apply beq_nat_false in H0.
          unfold assn_sub. unfold update. simpl. omega.
      unfold assert_implies. intros. induction H. simpl in H0. apply negb_false in H0. apply beq_nat_true in H0. omega.
  unfold hoare_triple.  intros. inversion H; subst. unfold update. simpl. omega.
Qed.
(*
        sim
    intros. apply hoare_consequence_post with (Q' := fun (st : state) => st X + st Y = m /\ beval st (BNot (BEq (AId X) (ANum 0))) = false).
  - eapply hoare_seq.
    + apply hoare_while. eapply hoare_seq.
       apply hoare_asgn.
      eapply hoare_consequence_pre. apply hoare_asgn.
     intros st H. unfold assn_sub. unfold update. simpl. inversion H.
        rewrite plus_assoc. destruct (st X) eqn:HH.
        simpl in H1. rewrite HH in H1. simpl in H1. inversion H1.
        simpl. rewrite <- minus_n_O. rewrite plus_comm. rewrite plus_assoc.
        simpl. rewrite plus_comm. rewrite plus_n_Sm. rewrite plus_comm.
        apply H0.
    + unfold hoare_triple. intros. inversion H; subst.
      unfold update. simpl. rewrite plus_0_r. reflexivity.
  - intros st H. inversion H. simpl in H1. unfold negb in H1.
    destruct (beq_nat (st X) 0) eqn:HH.
    + apply beq_nat_true in HH. rewrite HH in H0. simpl in H0.
      apply H0.
    + inversion H1.
*)
(*
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
*)

(*-- Check --*)
Check slow_assignment : forall m,
    {{ fun st => st X = m }}
    Y ::= ANum 0;;
    WHILE BNot (BEq (AId X) (ANum 0)) DO
      X ::= AMinus (AId X) (ANum 1);;
      Y ::= APlus (AId Y) (ANum 1)
    END
    {{ fun st => st Y = m }}.
  
