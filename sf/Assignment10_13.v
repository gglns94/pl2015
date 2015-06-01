Require Export Assignment10_12.

(* problem #13: 10 points *)

(** **** Exercise: 3 stars, optional  *)
Lemma par_body_n : forall n st,
  st X = 0 /\ st Y = 0 ->
  exists st',
    par_loop / st ==>c*  par_loop / st' /\ st' X = n /\ st' Y = 0.
Proof.
intros.
induction n.
  exists st. split. apply multi_refl. apply H.
  inversion IHn. induction H0.
  exists (update x X (S n)). split.
  apply par_body_n__Sn in H1. eapply multi_trans. apply H0. apply H1.
  split; unfold update. reflexivity. simpl. induction H1. apply H2.
Qed.

(*-- Check --*)
Check par_body_n : forall n st,
  st X = 0 /\ st Y = 0 ->
  exists st',
    par_loop / st ==>c*  par_loop / st' /\ st' X = n /\ st' Y = 0.

