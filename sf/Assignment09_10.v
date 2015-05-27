Require Export Assignment09_09.

(* problem #10: 10 points *)

(** **** Exercise: 3 stars (two_loops)  *)
(** Here is a very inefficient way of adding 3 numbers:
  X ::= 0;;
  Y ::= 0;;
  Z ::= c;;
  WHILE X <> a DO
    X ::= X + 1;;
    Z ::= Z + 1
  END;;
  WHILE Y <> b DO
    Y ::= Y + 1;;
    Z ::= Z + 1
  END

    Show that it does what it should by filling in the blanks in the
    following decorated program.

    {{ True }} ->>
    {{                                        }}
  X ::= 0;;
    {{                                        }}
  Y ::= 0;;
    {{                                        }}
  Z ::= c;;
    {{                                        }}
  WHILE X <> a DO
      {{                                        }} ->>
      {{                                        }}
    X ::= X + 1;;
      {{                                        }}
    Z ::= Z + 1
      {{                                        }}
  END;;
    {{                                        }} ->>
    {{                                        }}
  WHILE Y <> b DO
      {{                                        }} ->>
      {{                                        }}
    Y ::= Y + 1;;
      {{                                        }}
    Z ::= Z + 1
      {{                                        }}
  END
    {{                                        }} ->>
    {{ Z = a + b + c }}
*)

Theorem add_three_numbers_correct: forall a b c,
  {{ fun st => True }}                                   
  X ::= ANum 0;;
  Y ::= ANum 0;;
  Z ::= ANum c;;
  WHILE BNot (BEq (AId X) (ANum a)) DO
    X ::= APlus (AId X) (ANum 1);;
    Z ::= APlus (AId Z) (ANum 1)
  END;;
  WHILE BNot (BEq (AId Y) (ANum b)) DO
    Y ::= APlus (AId Y) (ANum 1);;
    Z ::= APlus (AId Z) (ANum 1)
  END
  {{ fun st => st Z = a + b + c }}.
Proof.
intros.
eapply hoare_seq with (Q := (fun st : state => st X = 0)).
eapply hoare_seq with (Q := (fun st : state => st X = 0 /\ st Y = 0)).
eapply hoare_seq with (Q := (fun st : state => st X = 0 /\ st Y = 0 /\ st Z = c)).
eapply hoare_seq with (Q := (fun st:state => st Y + 1 <= st Z + 1 /\ st Z = c + a /\ st Y = 0)).
  eapply hoare_consequence with (P' := (fun st:state => st Y + 1 <= st Z +1 /\ (st Z + 1)-(st Y + 1) = c+a)).
  eapply hoare_while.
    eapply hoare_seq with (Q:= (fun st:state =>  st Y <= st Z + 1 /\ (st Z+1) - (st Y ) = c + a)).
      unfold hoare_triple. intros. inversion H. subst. unfold update. simpl. omega.
      unfold hoare_triple. intros. inversion H. subst. unfold update. simpl.
      induction H0. apply H0.
  unfold assert_implies. intros. induction H. omega.
  unfold assert_implies. intros. induction H. simpl in H0.
    apply negb_false in H0. apply beq_nat_true in H0. omega.

  eapply hoare_consequence with (P' := (fun st:state => st X + 1 <= st Z +1 /\ (st Z + 1)-(st X + 1) = c /\ st Y = 0)).
  eapply hoare_while.
    eapply hoare_seq with (Q := (fun st:state => st X <= st Z +1 /\ (st Z + 1)-(st X) = c /\ st Y = 0)).
      unfold hoare_triple. intros. induction H0. inversion H; subst. unfold update. simpl. omega.
      unfold hoare_triple. intros. induction H0. inversion H; subst. unfold update. simpl. omega.
  unfold assert_implies. intros. omega.
  unfold assert_implies. intros. induction H. simpl in H0. apply negb_false in H0. apply beq_nat_true in H0.
  induction H. induction H1. split; try split. rewrite H2. omega. omega. omega.

unfold hoare_triple. intros. inversion H. subst. unfold update. simpl. omega.
unfold hoare_triple. intros. inversion H. subst. unfold update. simpl. omega.
unfold hoare_triple. intros. inversion H. subst. unfold update. simpl. reflexivity.
Qed.

(*-- Check --*)
Check add_three_numbers_correct: forall a b c,
  {{ fun st => True }}                                   
  X ::= ANum 0;;
  Y ::= ANum 0;;
  Z ::= ANum c;;
  WHILE BNot (BEq (AId X) (ANum a)) DO
    X ::= APlus (AId X) (ANum 1);;
    Z ::= APlus (AId Z) (ANum 1)
  END;;
  WHILE BNot (BEq (AId Y) (ANum b)) DO
    Y ::= APlus (AId Y) (ANum 1);;
    Z ::= APlus (AId Z) (ANum 1)
  END
  {{ fun st => st Z = a + b + c }}.

