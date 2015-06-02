Require Export Assignment11_02.

(* problem #03: 10 points *)

(** **** Exercise: 3 stars, optional (step_deterministic)  *)
(** Using [value_is_nf], we can show that the [step] relation is
    also deterministic... *)

Theorem step_deterministic:
  deterministic step.
Proof with eauto.
remember value_is_nf as VINF. clear HeqVINF.
unfold normal_form in VINF. unfold not in VINF.
unfold deterministic.
intros. revert y2 H0. induction H; intros.
  inversion H0; subst. reflexivity. inversion H4.
  inversion H0; subst. reflexivity. inversion H4.
  inversion H0; subst. inversion H. inversion H. rewrite (IHstep t1'0 H5). reflexivity.
  inversion H0; subst. rewrite (IHstep t1'0 H2). reflexivity.
  inversion H0. reflexivity. inversion H1.
  inversion H0; subst. reflexivity. exfalso. apply (VINF t1). eauto. inversion H2. eauto.
  inversion H0; subst. inversion H. exfalso. apply (VINF y2). eauto. inversion H. eauto. rewrite (IHstep t1'0). reflexivity. apply H2.
  inversion H0; subst. reflexivity. inversion H1.
  inversion H0; subst. reflexivity. exfalso. apply (VINF t1). eauto. inversion H2. exists t1'0. apply H3.
  inversion H0; subst. inversion H. exfalso. apply (VINF t0). eauto. inversion H. eauto. rewrite (IHstep t1'0). reflexivity. assumption.
Qed.

(*-- Check --*)
Check step_deterministic:
  deterministic step.

