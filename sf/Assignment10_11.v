Require Export Assignment10_10.

(* problem #11: 10 points *)

(** **** Exercise: 3 stars, optional (interp_tm)  *)
(** Remember that we also defined big-step evaluation of [tm]s as a
    function [evalF].  Prove that it is equivalent to the existing
    semantics.
 
    Hint: we just proved that [eval] and [multistep] are
    equivalent, so logically it doesn't matter which you choose.
    One will be easier than the other, though!  *)

Theorem evalF_eval : forall t n,
  evalF t = n <-> t || n.
Proof.
unfold iff. intros t. induction t.
  intros. split.
    intros. simpl in H. rewrite H. apply E_Const.
    intros. inversion H. subst. reflexivity.
  intros. split.
    intros. simpl in H. rewrite <- H. apply E_Plus.
    apply (IHt1 (evalF t1)). reflexivity.
    apply (IHt2 (evalF t2)). reflexivity.
    intros. inversion H. subst. simpl.
    apply IHt1 in H2. rewrite H2.
    apply IHt2 in H4. rewrite H4.
    reflexivity.
Qed.

(*-- Check --*)
Check evalF_eval : forall t n,
  evalF t = n <-> t || n.

