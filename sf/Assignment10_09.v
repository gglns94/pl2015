Require Export Assignment10_08.

(* problem #09: 10 points *)

(** **** Exercise: 3 stars (step__eval)  *)
Lemma step__eval : forall t t' n,
     t ==> t' ->
     t' || n ->
     t || n.
Proof.
  intros t t' n Hs. generalize dependent n.
  induction Hs; intros; inversion H; subst.
    apply E_Plus; apply E_Const.
    apply E_Plus. apply (IHHs n1 H2). apply H4.
    inversion H0; subst. apply E_Plus. apply H3. apply (IHHs n2 H5).
Qed.

(*-- Check --*)
Check step__eval : forall t t' n,
     t ==> t' ->
     t' || n ->
     t || n.

