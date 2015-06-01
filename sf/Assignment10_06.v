Require Export Assignment10_05.

(* problem #06: 10 points *)

Theorem normal_forms_unique:
  deterministic normal_form_of.
Proof.
  unfold deterministic. unfold normal_form_of.  intros x y1 y2 P1 P2.
  inversion P1 as [P11 P12]; clear P1. inversion P2 as [P21 P22]; clear P2. 
  generalize dependent y2.

  induction P11; intros y2 P21 P22.
    inversion P21; subst.
      reflexivity.
      exfalso. apply P12. exists y. apply H.
    inversion P21; subst.
      exfalso. apply P22. exists y. apply H.
      assert (y=y0) as Eeq. eapply step_deterministic_alt. apply H. apply H0. subst.
      apply (IHP11 P12 y2 H1 P22).
Qed.

(*-- Check --*)
Check normal_forms_unique:
  deterministic normal_form_of.

