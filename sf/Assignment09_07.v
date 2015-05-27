Require Export Assignment09_06.

(* problem #07: 10 points *)

(** **** Exercise: 3 stars, optional (add_slowly_decoration)  *)
(** The following program adds the variable X into the variable Z
    by repeatedly decrementing X and incrementing Z.
  WHILE X <> 0 DO
     Z ::= Z + 1;;
     X ::= X - 1
  END

    Following the pattern of the [subtract_slowly] example above, pick
    a precondition and postcondition that give an appropriate
    specification of [add_slowly]; then (informally) decorate the
    program accordingly. *)

(*
{{ X = n /\ Y = m }} ->>
{{ X + Y = n + m }}
WHILE X <> 0 DO
  {{ X + Y = n + m /\ X <> 0 }}->>
  {{ X + Y = n + m }}[X|->X-1][Y|->Y+1]
  Y ::= Y + 1;;
  {{ X + Y = n + m }}[X|->X-1]
  X ::= X - 1
  {{ X + Y = n + m }}
END
{{ X + Y = n + m /\ X = 0 }} ->>
{{ Y = n + m }}
*)


Theorem slow_addition_dec_correct : forall n m,
  {{fun st => st X = n /\ st Y = m }}
  WHILE BNot (BEq (AId X) (ANum 0)) DO
     Y ::= APlus (AId Y) (ANum 1);;
     X ::= AMinus (AId X) (ANum 1)
  END
  {{fun st => st Y = n + m}}.
Proof.
intros.
eapply hoare_consequence with (P' := fun st:state => st X + st Y = n + m).
eapply hoare_while.
eapply hoare_consequence_pre.
eapply hoare_seq.
eapply hoare_asgn.
eapply hoare_asgn.
intros st H. induction H. simpl in H0. apply negb_true in H0. apply beq_nat_false in H0.
unfold assn_sub. unfold update. simpl. omega.
intros st H. induction H. omega.
intros st H. induction H. simpl in H0. apply negb_false in H0. apply beq_nat_true in H0. omega.
Qed.
(*
induction n.

unfold hoare_triple. intros. simpl. inversion H; subst.
  induction H0. apply H1.
  inversion H3. apply negb_true in H2. apply beq_nat_false in H2. induction H0. rewrite H0 in H2. omega.

intros.
apply hoare_consequence_pre with 
(P' := (fun st:state =>(st X + st Y = S n + m))).
eapply hoare_consequence_post.
eapply hoare_while.
  apply hoare_seq with
  (Q := (fun st:state => (st X<>0)/\(st X + st Y = S n + S m))).
    unfold hoare_triple. intros. inversion H; subst. unfold update. simpl. induction H0. omega.
    unfold hoare_triple. intros. inversion H. subst. unfold update. simpl. induction H0. split.
      simpl in H1. apply negb_true in H1. apply beq_nat_false in H1. apply H1.
      omega.
  unfold assert_implies. intros. induction H.
  simpl in H0. apply negb_false in H0. apply beq_nat_true in H0. rewrite H0 in H. apply H.
  unfold assert_implies. intros. induction H.
  rewrite H. rewrite H0. reflexivity.
Qed
*)

(*-- Check --*)
Check slow_addition_dec_correct : forall n m,
  {{fun st => st X = n /\ st Y = m }}
  WHILE BNot (BEq (AId X) (ANum 0)) DO
     Y ::= APlus (AId Y) (ANum 1);;
     X ::= AMinus (AId X) (ANum 1)
  END
  {{fun st => st Y = n + m}}.

