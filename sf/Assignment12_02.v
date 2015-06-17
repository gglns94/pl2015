Require Export Assignment12_01.

(* problem #02: 10 points *)

(** **** Exercise: 2 stars, optional (typable_empty__closed)  *)
Corollary typable_empty__closed : forall t T, 
    empty |- t \in T  ->
    closed t.
Proof.
  intros t T HT x x_free.
  apply free_in_context with (T := T) (Gamma := empty) in x_free; try assumption.
  inversion x_free as [T' H]. inversion H.
Qed.

(*-- Check --*)
Check typable_empty__closed : forall t T, 
    empty |- t \in T  ->
    closed t.

