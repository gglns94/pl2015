Require Export Assignment08_18.

(* problem #19: 10 points *)

Lemma constfold_0plus_sound:
  ctrans_sound constfold_0plus.
Proof.
assert (Hoc := optimize_0plus_com_sound).
unfold ctrans_sound. intros. unfold constfold_0plus. induction c.
  simpl. apply refl_cequiv.

  simpl. apply CAss_congruence. unfold aequiv. intros.
  rewrite <- optimize_0plus_aexp_sound. rewrite <- fold_constants_aexp_sound.
  reflexivity.

  apply trans_cequiv with (c2:=fold_constants_com (c1;;c2)).
  apply fold_constants_com_sound.
  apply optimize_0plus_com_sound.

  apply trans_cequiv with (c2:=fold_constants_com (IFB b THEN c1 ELSE c2 FI)).
  apply fold_constants_com_sound.
  apply optimize_0plus_com_sound.

  apply trans_cequiv with (c2:=fold_constants_com (WHILE b DO c END)).
  apply fold_constants_com_sound.
  apply optimize_0plus_com_sound.
Qed.

(*-- Check --*)
Check constfold_0plus_sound:
  ctrans_sound constfold_0plus.
