Require Export Assignment10_09.

(* problem #10: 10 points *)

(** The fact that small-step reduction implies big-step is now
    straightforward to prove, once it is stated correctly. 

    The proof proceeds by induction on the multi-step reduction
    sequence that is buried in the hypothesis [normal_form_of t t']. *)
(** Make sure you understand the statement before you start to
    work on the proof.  *)

Lemma NF : forall t:tm, value t \/ exists t', t ==> t'.
Proof.
induction t.
  left. apply v_const.
  right. induction IHt1.
    induction IHt2.
      inversion H. inversion H0. subst. exists (C (n+n0)). apply ST_PlusConstConst.
      inversion H. inversion H0. subst. exists (P (C n) x). apply ST_Plus2.
        apply v_const.
        apply H2.
    inversion H. exists (P x t2). apply ST_Plus1. apply H0.
Qed.

(** **** Exercise: 3 stars (multistep__eval)  *)
Theorem multistep__eval : forall t t',
  normal_form_of t t' -> exists n, t' = C n /\ t || n.
Proof.
intros. induction H as [NF1 NF2]. assert (NF1' := NF1). induction NF1.
induction x.
  exists n. split. reflexivity. apply E_Const.
  unfold step_normal_form in NF2. unfold normal_form in NF2. unfold not in NF2.
  assert (NF' := (NF (P x1 x2))). inversion NF'. inversion H. apply NF2 in H. inversion H.
apply IHNF1 in NF2. inversion NF2. inversion H0. apply (step__eval x y x0 H) in H2.
exists x0. split. apply H1. apply H2. apply NF1.
Qed.

(*-- Check --*)
Check multistep__eval : forall t t',
  normal_form_of t t' -> exists n, t' = C n /\ t || n.

