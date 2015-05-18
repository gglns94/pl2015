Require Export Assignment08_07.

(* problem #08: 10 points *)

(** **** Exercise: 3 stars (swap_if_branches)  *)
(** Show that we can swap the branches of an IF by negating its
    condition *)

Theorem swap_if_branches: forall b e1 e2,
  cequiv
    (IFB b THEN e1 ELSE e2 FI)
    (IFB BNot b THEN e2 ELSE e1 FI).
Proof.
unfold cequiv. split; intros;
  inversion H; subst; destruct (beval st b) eqn:Hb;
    try inversion H5;
    try (rewrite Hb in H1; inversion H1).
    apply (E_IfFalse st). simpl. rewrite Hb. reflexivity. apply H6.
    apply (E_IfTrue st). simpl. rewrite Hb. reflexivity. apply H6.
    apply (E_IfFalse st). apply Hb. apply H6.
    apply (E_IfTrue st). apply Hb. apply H6.
Qed.

(*-- Check --*)
Check swap_if_branches: forall b e1 e2,
  cequiv
    (IFB b THEN e1 ELSE e2 FI)
    (IFB BNot b THEN e2 ELSE e1 FI).

