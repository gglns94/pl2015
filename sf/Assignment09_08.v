Require Export Assignment09_07.

(* problem #08: 10 points *)

(** The postcondition does not hold at the beginning of the loop,
    since [m = parity m] does not hold for an arbitrary [m], so we
    cannot use that as an invariant.  To find an invariant that works,
    let's think a bit about what this loop does.  On each iteration it
    decrements [X] by [2], which preserves the parity of [X].  So the
    parity of [X] does not change, i.e. it is invariant.  The initial
    value of [X] is [m], so the parity of [X] is always equal to the
    parity of [m]. Using [parity X = parity m] as an invariant we
    obtain the following decorated program:
    {{ X = m }} ->>                              (a - OK)
    {{ parity X = parity m }}
  WHILE 2 <= X DO
      {{ parity X = parity m /\ 2 <= X }}  ->>    (c - OK)
      {{ parity (X-2) = parity m }}
    X ::= X - 2
      {{ parity X = parity m }}
  END
    {{ parity X = parity m /\ X < 2 }}  ->>       (b - OK)
    {{ X = parity m }}

    With this invariant, conditions (a), (b), and (c) are all
    satisfied. For verifying (b), we observe that, when [X < 2], we
    have [parity X = X] (we can easily see this in the definition of
    [parity]).  For verifying (c), we observe that, when [2 <= X], we
    have [parity X = parity (X-2)]. *)


(** **** Exercise: 3 stars, optional (parity_formal)  *)
(** Translate this proof to Coq. Refer to the reduce-to-zero example
    for ideas. You may find the following two lemmas useful: *)

Lemma parity_ge_2 : forall x,
  2 <= x ->
  parity (x - 2) = parity x.
Proof.
  induction x; intro. reflexivity.
  destruct x. inversion H. inversion H1.
  simpl. rewrite <- minus_n_O. reflexivity.
Qed.

Lemma parity_lt_2 : forall x,
  ~ 2 <= x ->
  parity (x) = x.
Proof.
  intros. induction x. reflexivity. destruct x. reflexivity.
    apply ex_falso_quodlibet. apply H. omega.
Qed.

Lemma parity0or1': forall x,
  (parity x = 0 \/ parity x = 1)/\(parity (S x) = 0 \/ parity (S x) = 1).
Proof.
induction x.
  split; try (left; reflexivity); try (right; reflexivity).
  inversion IHx; split.
    inversion H0. left. apply H1. right. apply H1.
    inversion H. left. simpl. apply H1. right. simpl. apply H1.
Qed.

Lemma parity0or1: forall x,
  (parity x = 0 \/ parity x = 1).
Proof.
assert (PO := parity0or1').
intros. apply (PO x).
Qed.

Theorem parity_correct : forall m,
    {{ fun st => st X = m }}
  WHILE BLe (ANum 2) (AId X) DO
    X ::= AMinus (AId X) (ANum 2)
  END
    {{ fun st => st X = parity m }}.
Proof.
intros.
destruct (parity0or1 m);
assert (Hp := H); clear H.

Case "prity m = 0".
eapply hoare_consequence_pre with
(P' := (fun st:state => parity (st X) = 0)).
eapply hoare_consequence_post.
eapply hoare_while.

unfold hoare_triple. intros. induction H0.
inversion H. subst. unfold update. simpl.
unfold beval in H1. apply ble_nat_true in H1. simpl in H1.
apply parity_ge_2 in H1. omega.

unfold assert_implies. intros. induction H.
unfold beval in H0. apply ble_nat_false in H0. simpl in H0.
apply parity_lt_2 in H0. omega.

unfold assert_implies. intros. rewrite <- H in Hp. apply Hp.

Case "parity m = 1".
eapply hoare_consequence_pre with
(P' := (fun st:state => parity (st X) = 1)).
eapply hoare_consequence_post.
eapply hoare_while.

unfold hoare_triple. intros. induction H0.
inversion H. subst. unfold update. simpl.
unfold beval in H1. apply ble_nat_true in H1. simpl in H1.
apply parity_ge_2 in H1. omega.

unfold assert_implies. intros. induction H.
unfold beval in H0. apply ble_nat_false in H0. simpl in H0.
apply parity_lt_2 in H0. omega.

unfold assert_implies. intros. rewrite <- H in Hp. apply Hp.
Qed.

(*-- Check --*)
Check parity_correct : forall m,
    {{ fun st => st X = m }}
  WHILE BLe (ANum 2) (AId X) DO
    X ::= AMinus (AId X) (ANum 2)
  END
    {{ fun st => st X = parity m }}.

