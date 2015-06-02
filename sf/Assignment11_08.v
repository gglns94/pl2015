Require Export Assignment11_07.

(* problem #08: 10 points *)

(** **** Exercise: 1 star, optional (normalize_ex')  *)
(** For comparison, prove it using [apply] instead of [eapply]. *)

Theorem normalize_ex' : exists e',
  (AMult (ANum 3) (AMult (ANum 2) (ANum 1))) / empty_state 
  ==>a* e'.
Proof.
exists (ANum 6).
apply multi_step with (y := (AMult (ANum 3) (ANum 2))). apply AS_Mult2. apply av_num. apply AS_Mult.
apply multi_step with (y := (ANum 6)). simpl. apply AS_Mult.
simpl. apply multi_refl.
Qed.

(*-- Check --*)
Check normalize_ex' : exists e',
  (AMult (ANum 3) (AMult (ANum 2) (ANum 1))) / empty_state 
  ==>a* e'.

