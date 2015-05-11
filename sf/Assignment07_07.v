Require Export Assignment07_06.

(* problem #07: 10 points *)

(** **** Exercise: 1 star (update_example)  *)
(** Before starting to play with tactics, make sure you understand
    exactly what the theorem is saying! *)

Theorem update_example : forall (n:nat),
  (update empty_state (Id 2) n) (Id 3) = 0.
Proof.
unfold update. intros. destruct (eq_id_dec (Id 2) (Id 3)).
  inversion e.
  reflexivity.
Qed.
(** [] *)

