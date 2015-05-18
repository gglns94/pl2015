Require Export Assignment08_03.

(* problem #04: 10 points *)

(** **** Exercise: 4 stars (no_whiles_terminating)  *)
(** Imp programs that don't involve while loops always terminate.
    State and prove a theorem [no_whiles_terminating] that says this. *)

(* Hint *)
Check andb_true_iff.

Theorem no_whiles_terminate: forall c st
    (NOWHL: no_whiles c = true),
  exists st', c / st || st'.
Proof.
intros. revert st. induction c; simpl in NOWHL; try (apply andb_true_iff in NOWHL; induction NOWHL).
  intros. exists st. apply E_Skip.
  intros. exists (update st i (aeval st a)). apply E_Ass. reflexivity.
  intros.
    apply IHc1 with (st := st) in H. induction H.
    apply IHc2 with (st := x) in H0. induction H0.
    exists x0. apply E_Seq with (st' := x). apply H. apply H0.
  intros.
    apply IHc1 with (st := st) in H. induction H.
    apply IHc2 with (st := st) in H0. induction H0.
    destruct (beval st b) eqn:Hb.
      apply E_IfTrue with (st':=x) (c1:=c1) (c2:=c2) in Hb. exists x. apply Hb. apply H.
      assert (Hb' := (E_IfFalse  st x0 b c1 c2 Hb H0)). exists x0. apply Hb'.
  intros. inversion NOWHL.
Qed.

(*-- Check --*)
Check no_whiles_terminate: forall c st
    (NOWHL: no_whiles c = true),
  exists st', c / st || st'.

