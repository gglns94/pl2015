Require Export Assignment10_14.

(* problem #15: 10 points *)

(* Hint: 

   First study the chapter "Auto.v".

   Using [;], [try] and [eauto], you can prove it in 7 lines thanks to:. 
     Hint Constructors bstep.

   You can use the following intro pattern:
     destruct ... as [[? | ?] | [? ?]].
*)

Theorem bexp_strong_progress: forall st b,
  (b = BTrue \/ b = BFalse) \/
  exists b', b / st ==>b b'.
Proof.
  intros. induction b; eauto; right;
  try (assert (SP := aexp_strong_progress st a); assert (SP' := aexp_strong_progress st a0);
  induction SP; induction SP'; inversion H; inversion H0; try rewrite H1; try rewrite H2; eauto using H1, H2).
  inversion IHb; inversion H.
    rewrite H0. eauto.
    rewrite H0. eauto.
    eexists. eauto using H0.
  inversion IHb1; inversion IHb2; inversion H; inversion H0.
    rewrite H1. rewrite H2. eauto.
    rewrite H1. rewrite H2. eauto.
    rewrite H1. rewrite H2. eauto.
    rewrite H1. rewrite H2. eauto.
    rewrite H1. eauto using H2.
    rewrite H1. eauto using H2.
    rewrite H2. eauto using H1.
    rewrite H2. eauto using H2.
    eauto using H1, H2.
Qed.

(*-- Check --*)
Check bexp_strong_progress: forall st b,
  (b = BTrue \/ b = BFalse) \/
  exists b', b / st ==>b b'.

