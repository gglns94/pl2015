Require Export Assignment12_05.

(* problem #06: 10 points *)

Theorem tloop_diverges:
  ~ exists t, tapp tloop (tnat 0) ==>* t /\ normal_form step t.
Proof.
intros H. inversion H. inversion H0. clear H0. unfold tloop in H1. apply H2.
remember (tapp
       (tfix
          (tabs Loop (TArrow TNat TNat)
             (tabs X TNat (tapp (tvar Loop) (tvar X))))) (tnat 0)) as p.
remember (tapp
       (tapp
          (tabs Loop (TArrow TNat TNat)
             (tabs X TNat (tapp (tvar Loop) (tvar X))))
          (tfix
             (tabs Loop (TArrow TNat TNat)
                (tabs X TNat (tapp (tvar Loop) (tvar X)))))) (tnat 0)) as q.
remember (tapp
       (tabs X TNat
          (tapp
             (tfix
                (tabs Loop (TArrow TNat TNat)
                   (tabs X TNat (tapp (tvar Loop) (tvar X))))) (tvar X)))
       (tnat 0)) as r.
assert (forall t, p ==> t -> t = q) as Hpq.
  intros t Hpq'. rewrite Heqp in Hpq'. inversion Hpq'; subst. inversion H5; subst. inversion H3.
  inversion H6. reflexivity.
assert (forall t, q ==> t -> t = r) as Hqr.
  intros t Hqr'. rewrite Heqq in Hqr'. inversion Hqr'; subst. inversion H5; subst. reflexivity.
  inversion H6. inversion H7; subst. inversion H3. inversion H6.
assert (forall t, r ==> t -> t = p) as Hrp.
  intros t Hrp'. rewrite Heqr in Hrp'. inversion Hrp'; subst. reflexivity. inversion H5.
  inversion H6.
assert (forall t t', (t ==> t')->(t = p)\/(t = q)\/(t = r)->(t' = p)\/(t' = q)\/(t' = r)) as Hpqr.
  intros. induction H3. rewrite H3 in H0. apply Hpq in H0. right. left. apply H0.
  induction H3. rewrite H3 in H0. apply Hqr in H0. right. right. apply H0.
  rewrite H3 in H0. apply Hrp in H0. left. apply H0.
assert (forall t t', (t ==>* t')->(t = p)\/(t = q)\/(t = r)->(t' = p)\/(t' = q)\/(t' = r)) as Hm.
  intros. induction H0. apply H3. apply IHmulti. apply Hpqr in H0. apply H0. apply H3.
assert (p = p \/ p = q \/ p = r) as Hp. left. reflexivity.
assert (Hx := (Hm p x H1 Hp)). 
induction Hx. exists q. rewrite H0. rewrite Heqp. rewrite Heqq.
apply ST_AppFix. constructor. constructor.
induction H0. exists r. rewrite H0. rewrite Heqq. rewrite Heqr.
repeat constructor.
exists p. rewrite H0. rewrite Heqr. rewrite Heqp.
repeat constructor.
Qed.

(*q. simpl. apply Hpq.
  apply Hpqr in H0.  induction H3.
simpl.
inversion Hpqr.
assert (forall t', (p ==>* t')->(t' = p)\/(t' = q)\/(t' = r)) as Hmulti.
  intros. induction H0. left. reflexivity. apply Hpqr in H0. apply IHmulti. ; subst.
inversion H1; subst. subst. eexists. apply ST_AppFix. constructor. constructor.
eexists.
eexists.
 right. right. induction H0. left. reflexivity.  left. reflexivity. inversion H0; subst.
 inversion H5; subst. 
inversion H1; subst. eexists. apply ST_AppFix. constructor. constructor.
(*1 step interpret*)
  inversion H0; subst. inversion H7; subst. inversion H5; subst. inversion H8; subst.
inversion H3; subst. eexists. constructor. constructor. constructor. constructor.
(*2 step interpret*)
  inversion H4; subst. inversion H11; subst.
inversion H5; subst. eexists. constructor. constructor.
(*3 step interpert*) simpl in H7.
  inversion H7; subst. simpl in H7. simpl in H11.
  inversion H9.
(*3 step contradiction*)
  inversion H15. inversion H16.
(*2 step contradiction*)
  inversion H12. inversion H13; subst. inversion H9. inversion H12.
Qed.
*)
(*-- Check --*)
Check tloop_diverges:
  ~ exists t, tapp tloop (tnat 0) ==>* t /\ normal_form step t.

