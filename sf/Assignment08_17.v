Require Export Assignment08_16.

(* problem #17: 10 points *)

Lemma optimize_0plus_bexp_sound:
  btrans_sound optimize_0plus_bexp.
Proof.
unfold btrans_sound. intros. induction b;
  try (simpl; apply refl_bequiv);
  try (unfold optimize_0plus_bexp; 
  unfold bequiv;
  intros; unfold beval; simpl;
  rewrite (optimize_0plus_aexp_sound a);
  rewrite (optimize_0plus_aexp_sound a0);
  reflexivity).
  simpl. unfold bequiv. remember (optimize_0plus_bexp b) as b'. simpl. intros. unfold bequiv in IHb. rewrite (IHb st). reflexivity.
  simpl. unfold bequiv. remember (optimize_0plus_bexp b1) as b1'. remember (optimize_0plus_bexp b2) as b2'. simpl. intros.
  unfold bequiv in IHb1. unfold bequiv in IHb2.
  rewrite (IHb1 st). rewrite (IHb2 st). reflexivity.
Qed.

(*-- Check --*)
Check optimize_0plus_bexp_sound:
  btrans_sound optimize_0plus_bexp.

