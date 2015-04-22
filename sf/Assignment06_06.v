Require Export Assignment06_05.

(* problem #06: 20 points *)

(** **** Exercise: 4 stars, advanced (no_repeats)  *)
(** The following inductively defined proposition... *)

Inductive appears_in {X:Type} (a:X) : list X -> Prop :=
  | ai_here : forall l, appears_in a (a::l)
  | ai_later : forall b l, appears_in a l -> appears_in a (b::l).

(** ...gives us a precise way of saying that a value [a] appears at
    least once as a member of a list [l]. 

    Here's a pair of warm-ups about [appears_in].
*)

Lemma appears_in_app : forall (X:Type) (xs ys : list X) (x:X), 
     appears_in x (xs ++ ys) -> appears_in x xs \/ appears_in x ys.
Proof.
  intros.  generalize dependent ys. 
  induction xs as [|x']. intros. simpl in H. right. apply H.
  simpl. intros. inversion H.
    Case "x=a". left. apply ai_here.
    Case "x!=a". apply IHxs in H1. inversion H1. left. apply ai_later. apply H3. right. apply H3.
Qed.

Lemma app_appears_in : forall (X:Type) (xs ys : list X) (x:X), 
     appears_in x xs \/ appears_in x ys -> appears_in x (xs ++ ys).
Proof.
  intros. induction xs. simpl. inversion H. inversion H0. apply H0. (*Note : inversion = H dec tree*)
  simpl. inversion H. 
    inversion H0. apply ai_here. apply ai_later. apply IHxs. left. apply H2.
    apply ai_later. apply IHxs. right. apply H0.
Qed.