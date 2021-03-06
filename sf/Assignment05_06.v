Require Export Assignment05_05.

(* problem #06: 10 points *)


(** 2 stars, optional (orb_false)  *)
Theorem orb_prop : forall b c,
  orb b c = true -> b = true \/ c = true.
Proof.
  intros.
  rewrite <- H.
    destruct b.
    simpl. left. reflexivity.
    simpl. right. reflexivity.
Qed.

