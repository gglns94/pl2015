Require Export Assignment10_13.

(* problem #14: 10 points *)

(* Hint: 

   First study the chapter "Auto.v".

   Using [;], [try] and [eauto], you can prove it in 4 lines thanks to: 
     Hint Constructors aval
     Hint Constructors astep.
  
   You can use the following intro pattern:
     destruct ... as [[? ?] | [? ?]].
*)
Hint Constructors aval. Hint Constructors astep.

Theorem aexp_strong_progress: forall st a,
  (exists n, a = ANum n) \/
  exists a', a / st ==>a a'.
Proof.
intros. induction a; eauto.
  induction a1; induction a2; eauto;
  try (inversion IHa2; inversion H; inversion H0; inversion H; eauto using H0; reflexivity);
  try (inversion IHa1; inversion H; inversion H0; inversion H; eauto using H0; reflexivity).
  induction a1; induction a2; eauto;
  try (inversion IHa2; inversion H; inversion H0; inversion H; eauto using H0; reflexivity);
  try (inversion IHa1; inversion H; inversion H0; inversion H; eauto using H0; reflexivity).
  induction a1; induction a2; eauto;
  try (inversion IHa2; inversion H; inversion H0; inversion H; eauto using H0; reflexivity);
  try (inversion IHa1; inversion H; inversion H0; inversion H; eauto using H0; reflexivity).
Qed.

(*-- Check --*)
Check aexp_strong_progress: forall st a,
  (exists n, a = ANum n) \/
  exists a', a / st ==>a a'.

