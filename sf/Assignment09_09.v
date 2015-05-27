Require Export Assignment09_08.

(* problem #09: 10 points *)

(** **** Exercise: 4 stars (factorial)  *)
(** Recall that [n!] denotes the factorial of [n] (i.e. [n! =
    1*2*...*n]).  Here is an Imp program that calculates the factorial
    of the number initially stored in the variable [X] and puts it in
    the variable [Y]:
    {{ X = m }} 
  Y ::= 1 ;;
  WHILE X <> 0
  DO
     Y ::= Y * X ;;
     X ::= X - 1
  END
    {{ Y = m! }}

    Fill in the blanks in following decorated program:
    {{ X = m }} ->>
    {{                                      }}
  Y ::= 1;;
    {{                                      }}
  WHILE X <> 0
  DO   {{                                      }} ->>
       {{                                      }}
     Y ::= Y * X;;
       {{                                      }}
     X ::= X - 1
       {{                                      }}
  END
    {{                                      }} ->>
    {{ Y = m! }}
*)

Print fact.

Theorem factorial_dec_correct: forall m,
  {{ fun st => st X = m }} 
  Y ::= ANum 1 ;;
  WHILE BNot (BEq (AId X) (ANum 0))
  DO
     Y ::= AMult (AId Y) (AId X) ;;
     X ::= AMinus (AId X) (ANum 1)
  END
  {{ fun st => st Y = fact m }}.
Proof.
intros.
eapply hoare_seq with (Q:=(fun st:state => (st X = m)/\(st Y = 1))).
eapply hoare_consequence with (P':=(fun st:state => (st Y) * fact (st X) = fact m)).
eapply hoare_while.
eapply hoare_seq with (Q:=(fun st:state => (st Y * fact (st X - 1) = fact m))).
  unfold hoare_triple. intros. inversion H. subst. unfold update. simpl. omega.
  unfold hoare_triple. intros. inversion H. subst. unfold update. simpl.
    induction H0. simpl in H1. apply negb_true in H1. apply beq_nat_false in H1.
    destruct (st X).
      omega.
      simpl. simpl in H0.
      assert (forall n0, n0 - 0 = n0).
      induction n0. reflexivity. simpl. reflexivity.
      rewrite H2. rewrite <- mult_assoc. rewrite (mult_comm (S n) (fact n)). rewrite <- mult_n_Sm.
      rewrite plus_comm. rewrite (mult_comm (fact n) n). apply H0.
unfold assert_implies. intros. induction H. rewrite H. rewrite H0. omega.
unfold assert_implies. intros. induction H. simpl in H0. apply negb_false in H0. apply beq_nat_true in H0.
rewrite H0 in H. simpl in H. omega.
unfold hoare_triple. intros. inversion H. subst. unfold update. simpl. split; reflexivity.
Qed.

(*-- Check --*)
Check factorial_dec_correct: forall m,
  {{ fun st => st X = m }} 
  Y ::= ANum 1 ;;
  WHILE BNot (BEq (AId X) (ANum 0))
  DO
     Y ::= AMult (AId Y) (AId X) ;;
     X ::= AMinus (AId X) (ANum 1)
  END
  {{ fun st => st Y = fact m }}.

