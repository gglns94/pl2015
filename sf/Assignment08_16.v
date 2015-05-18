Require Export Assignment08_15.

(* problem #16: 10 points *)

Lemma optimize_0plus_aexp_sound:
  atrans_sound optimize_0plus_aexp.
Proof.
unfold atrans_sound. unfold aequiv. intros. revert st.
 induction a;
  try reflexivity;
  intros;
  remember a1 as a1' eqn:H'; remember a2 as a2' eqn:H'';
  simpl;
  destruct a1'; try(
    destruct n;
      try (simpl; rewrite <- IHa2; reflexivity);
      destruct a2';
        try (destruct n0;
          try (simpl; intuition);
          rewrite H'; rewrite H''; rewrite H' in IHa1; rewrite H'' in IHa2; simpl; rewrite <- IHa1; rewrite <- IHa2; reflexivity);
        rewrite H'; rewrite H''; rewrite H' in IHa1; rewrite H'' in IHa2; simpl; rewrite <- IHa1; rewrite <- IHa2; reflexivity
  ); try (
    destruct a2';
      try (destruct n;
        try (rewrite -> H'; rewrite -> H' in IHa1; rewrite <- IHa1; intuition);
        try (reflexivity);
        rewrite H'; rewrite H''; rewrite H' in IHa1; rewrite H'' in IHa2; simpl; rewrite <- IHa1; rewrite <- IHa2; reflexivity);
      rewrite H'; rewrite H''; rewrite H' in IHa1; rewrite H'' in IHa2; simpl; rewrite <- IHa1; rewrite <- IHa2; reflexivity
  ).
Qed.

(*-- Check --*)
Check optimize_0plus_aexp_sound:
  atrans_sound optimize_0plus_aexp.

