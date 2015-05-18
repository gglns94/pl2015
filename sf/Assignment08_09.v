Require Export Assignment08_08.

(* problem #09: 10 points *)

(** **** Exercise: 2 stars (WHILE_true)  *)
(** Prove the following theorem. _Hint_: You'll want to use
    [WHILE_true_nonterm] here. *)

Lemma WHILE_true_nonterm : forall (b:bexp) (c:com) (st st':state),
  bequiv b BTrue ->
  ((WHILE b DO c END)/st||st' -> False).
Proof.
intros.
remember (WHILE b DO c END) as wh.
induction H0; inversion Heqwh; subst.
  unfold bequiv in H. assert (H':=(H st)). rewrite H0 in H'. inversion H'.
  apply IHceval2. reflexivity.
Qed.

Theorem WHILE_true: forall b c,
     bequiv b BTrue  ->
     cequiv 
       (WHILE b DO c END)
       (WHILE BTrue DO SKIP END).
Proof.
unfold cequiv. split; intros.
  inversion H0; subst. assert (H' := (H st')). rewrite H5 in H'. inversion H'.
  apply WHILE_true_nonterm with (st:=st'0) (st':=st') (c:=c)  in H. 
    inversion H.
    apply H7.
  assert (bequiv BTrue BTrue) as H'. unfold bequiv. reflexivity.
  apply WHILE_true_nonterm with (st:=st) (st':=st') (c:=SKIP)  in H'.
    inversion H'.
    apply H0.
Qed.

(*-- Check --*)
Check WHILE_true: forall b c,
     bequiv b BTrue  ->
     cequiv 
       (WHILE b DO c END)
       (WHILE BTrue DO SKIP END).

