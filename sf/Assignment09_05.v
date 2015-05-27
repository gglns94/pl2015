Require Export Assignment09_04.

(* problem #05: 10 points *)

(** **** Exercise: 2 stars (if_minus_plus)  *)
(** Prove the following hoare triple using [hoare_if]: *)

Theorem if_minus_plus :
  {{fun st => True}}
  IFB (BLe (AId X) (AId Y))
    THEN (Z ::= AMinus (AId Y) (AId X))
    ELSE (Y ::= APlus (AId X) (AId Z))
  FI
  {{fun st => st Y = st X + st Z}}.
Proof.
eapply hoare_consequence_pre.
apply hoare_if.
  apply hoare_asgn.
  apply hoare_asgn. unfold assn_sub.
  simpl. unfold assert_implies. intros. split; intros.
    induction (st X) eqn:Hstx; induction (st Y) eqn:Hsty.
    simpl. unfold update. simpl. rewrite Hstx. apply Hsty.
    simpl. unfold update. simpl. rewrite Hstx. apply Hsty.
    inversion H0.
    simpl. unfold update. simpl. rewrite Hstx. rewrite Hsty. simpl. apply ble_nat_true in H0. omega. (*how to use omega!*)
    induction (st X) eqn:Hstx; induction (st Z) eqn:Hsty.
    simpl. unfold update. simpl. rewrite Hstx. rewrite Hsty. reflexivity.
    inversion H0.
    simpl. unfold update. simpl. rewrite Hstx. rewrite Hsty. reflexivity.
    simpl. unfold update. simpl. rewrite Hstx. rewrite Hsty. simpl. reflexivity.
Qed.

(*-- Check --*)
Check if_minus_plus :
  {{fun st => True}}
  IFB (BLe (AId X) (AId Y))
    THEN (Z ::= AMinus (AId Y) (AId X))
    ELSE (Y ::= APlus (AId X) (AId Z))
  FI
  {{fun st => st Y = st X + st Z}}. 

