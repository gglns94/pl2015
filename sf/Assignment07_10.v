Require Export Assignment07_09.

(* problem #10: 10 points *)

(** **** Exercise: 3 stars (update_permute)  *)
Theorem update_permute : forall n1 n2 x1 x2 x3 st,
  x2 <> x1 -> 
  (update (update st x2 n1) x1 n2) x3 = (update (update st x1 n2) x2 n1) x3.
Proof.
unfold update. intros. destruct (eq_id_dec x1 x3); destruct (eq_id_dec x2 x3); try reflexivity.
  subst. apply ex_falso_quodlibet. apply H. reflexivity.
Qed.
(** [] *)

