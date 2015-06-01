Require Export Assignment10_15.

(* problem #16: 10 points *)

(* Hint: 

   First study the chapter "Auto.v".

   Using [;], [try] and [eauto], you can prove it in 6 lines thanks to:
     Hint Constructors cstep.
 
   You can use the following intro pattern:
     destruct ... as [ | [? [? ?]]].
*)

Theorem cimp_strong_progress : forall c st,
  c = SKIP \/ 
  exists c' st', c / st ==>c c' / st'.
Proof.
intros. revert st. induction c; intros; eauto; right.
  induction (aexp_strong_progress st a); inversion H.
    rewrite H0. eauto.
    eauto.
  induction (IHc1 st). 
    rewrite H. eauto.
    inversion H. inversion H0. eauto.
  induction (bexp_strong_progress st b).
    induction H; rewrite H; eauto.
    induction H. eauto.
  induction (IHc1 st).
    rewrite H. induction (IHc2 st).
      rewrite H0. eauto.
      inversion H0. inversion H1. eauto.
    induction H. induction H. eauto.
Qed.

(*-- Check --*)
Check cimp_strong_progress : forall c st,
  c = SKIP \/ 
  exists c' st', c / st ==>c c' / st'.

