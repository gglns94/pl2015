Require Export Assignment12_02.

(* problem #03: 10 points *)

(** **** Exercise: 3 stars (types_unique)  *)
(** Another pleasant property of the STLC is that types are
    unique: a given term (in a given context) has at most one
    type. *)

Lemma type_is_unique: forall t G T T'
    (TYPED: G |- t \in T)
    (TYPED': G |- t \in T'),
  T = T'.
Proof.
intros. generalize dependent T'.
induction TYPED; subst; intros; inversion TYPED'; subst; try reflexivity.
rewrite H in H2. inversion H2. auto.
rewrite (IHTYPED T1 H4). reflexivity.
rewrite <- (IHTYPED2 T0 H4) in H2. apply IHTYPED1 in H2. inversion H2. auto.
apply IHTYPED2 in H5. apply H5.
apply IHTYPED1 in H2. apply IHTYPED2 in H4.
subst. reflexivity.
apply IHTYPED in H1. inversion H1. reflexivity.
apply IHTYPED in H1. inversion H1. reflexivity.
apply IHTYPED1 in H4. subst. apply IHTYPED2 in H5. subst. reflexivity.
apply IHTYPED in H3. subst. reflexivity.
apply IHTYPED in H3. subst. reflexivity.
apply IHTYPED1 in H6. inversion H6. subst. apply IHTYPED2 in H7. apply H7.
apply IHTYPED1 in H2. subst. reflexivity.
apply IHTYPED1 in H6. inversion H6. subst. apply IHTYPED3 in H8. apply H8.
apply IHTYPED in H1. inversion H1. subst. reflexivity.
Qed.

(*-- Check --*)
Check type_is_unique: forall t G T T'
    (HTyped: G |- t \in T)
    (HTyped': G |- t \in T'),
  T = T'.

