Require Export Assignment10_07.

(* problem #08: 10 points *)

(** **** Exercise: 3 stars (eval__multistep)  *)
(** The key idea behind the proof comes from the following picture:
       P t1 t2 ==>            (by ST_Plus1) 
       P t1' t2 ==>           (by ST_Plus1)  
       P t1'' t2 ==>          (by ST_Plus1) 
       ...                
       P (C n1) t2 ==>        (by ST_Plus2)
       P (C n1) t2' ==>       (by ST_Plus2)
       P (C n1) t2'' ==>      (by ST_Plus2)
       ...                
       P (C n1) (C n2) ==>    (by ST_PlusConstConst)
       C (n1 + n2)              
    That is, the multistep reduction of a term of the form [P t1 t2]
    proceeds in three phases:
       - First, we use [ST_Plus1] some number of times to reduce [t1]
         to a normal form, which must (by [nf_same_as_value]) be a
         term of the form [C n1] for some [n1].
       - Next, we use [ST_Plus2] some number of times to reduce [t2]
         to a normal form, which must again be a term of the form [C
         n2] for some [n2].
       - Finally, we use [ST_PlusConstConst] one time to reduce [P (C
         n1) (C n2)] to [C (n1 + n2)]. *)

(** To formalize this intuition, you'll need to use the congruence
    lemmas from above (you might want to review them now, so that
    you'll be able to recognize when they are useful), plus some basic
    properties of [==>*]: that it is reflexive, transitive, and
    includes [==>]. *)

Theorem eval__multistep : forall t n,
  t || n -> t ==>* C n.
Proof.
intros.
induction H.
  apply multi_refl.
  apply multi_trans with (y := (P (C n1) t2)).
    induction IHeval1.
      apply multi_refl.
      eapply multi_step.
        apply ST_Plus1.
          apply H1.
          apply IHIHeval1.
          assert (forall a b n, a||n -> (a ==> b) -> b||n) as STEQ.
            intros. revert n H2. induction H3; intros.
              inversion H2. subst. inversion H5. inversion H7. apply E_Const.
              inversion H2. subst. apply E_Plus. apply (IHstep n0 H6). apply H8.
              inversion H4. subst. apply E_Plus. apply H7. apply (IHstep n3 H9).
          apply (STEQ x y n1 H H1).
      apply multi_trans with (y := (P (C n1) (C n2))).
        apply multistep_congr_2.
        apply v_const. apply IHeval2. apply multi_R. apply ST_PlusConstConst.
Qed.

(*-- Check --*)
Check eval__multistep : forall t n,
  t || n -> t ==>* C n.

