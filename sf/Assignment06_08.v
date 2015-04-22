Require Export Assignment06_07.

Theorem Sn_le_Sm__n_le_m : forall n m,
  S n <= S m -> n <= m.
Proof. 
  intros n m.  generalize dependent n.  induction m.
    intros n. destruct n as [| n'].
      intros h. apply le_n.
      intros contra. inversion contra. inversion H0.
    intros n lte. inversion lte.
      apply le_n.
      apply le_S. apply IHm. apply H0.
Qed.

(* problem #08: 40 points *)

(** **** Exercise: 4 stars, advanced (pigeonhole principle)  *)
(** The "pigeonhole principle" states a basic fact about counting:
   if you distribute more than [n] items into [n] pigeonholes, some 
   pigeonhole must contain at least two items.  As is often the case,
   this apparently trivial fact about numbers requires non-trivial
   machinery to prove, but we now have enough... *)

(** First a pair of useful lemmas (we already proved these for lists
    of naturals, but not for arbitrary lists). *)

Lemma app_length : forall (X:Type) (l1 l2 : list X),
  length (l1 ++ l2) = length l1 + length l2. 
Proof. 
  intros. induction l1. 
    Case "l1=nil". simpl. reflexivity.
    Case "l1!=nil". simpl. rewrite IHl1. reflexivity.
Qed.

Lemma appears_in_app_split : forall (X:Type) (x:X) (l:list X),
  appears_in x l -> 
  exists l1, exists l2, l = l1 ++ (x::l2).
Proof.
  intros.
  induction l.
  - inversion H.
  - inversion H.
    + apply ex_intro with (witness := []). simpl. apply ex_intro with (witness := l). reflexivity.
    + apply IHl in H1. inversion H1.
      * apply ex_intro with (witness := x0::witness). inversion proof.
        apply ex_intro with (witness := witness0). simpl. rewrite proof0. reflexivity.
Qed.
(** Now define a predicate [repeats] (analogous to [no_repeats] in the
   exercise above), such that [repeats X l] asserts that [l] contains
   at least one repeated element (of type [X]).  *)

Inductive repeats {X:Type} : list X -> Prop :=
| rp_here : forall (x:X) (l:list X), appears_in x l -> repeats (x::l)
| rp_later : forall (x:X) (l:list X), repeats l -> repeats (x::l).


(** Now here's a way to formalize the pigeonhole principle. List [l2]
    represents a list of pigeonhole labels, and list [l1] represents
    the labels assigned to a list of items: if there are more items
    than labels, at least two items must have the same label.  This
    proof is much easier if you use the [excluded_middle] hypothesis
    to show that [appears_in] is decidable, i.e. [forall x
    l, (appears_in x l) \/ ~ (appears_in x l)].  However, it is also
    possible to make the proof go through _without_ assuming that
    [appears_in] is decidable; if you can manage to do this, you will
    not need the [excluded_middle] hypothesis. *)


Theorem contradiction_implies_anything : forall P Q : Prop,
  (P /\ ~P) -> Q.
Proof. 
  intros P Q H. inversion H as [HP HNA]. unfold not in HNA. 
  apply HNA in HP. inversion HP.  Qed.

Theorem pigeonhole_principle: forall {X:Type} (l1 l2:list X),
  excluded_middle ->
  (forall x, appears_in x l1 -> appears_in x l2) ->
  length l2 < length l1 ->
  repeats l1.
Proof.
  intros X l1. induction l1 as [|x l1'].
  - intros. inversion H1.
  - intros.
    assert ((appears_in x l1') \/ ~(appears_in x l1')) as Hl1. apply H.
    destruct Hl1 . apply rp_here. apply H2. (* appears_in x l1' *) 

    apply rp_later. (* ~ appears_in x l1' *)
    assert (appears_in x l2). apply (H0 x). apply ai_here.

    (* former Prop *)
    apply appears_in_app_split in H3. destruct H3. destruct proof.
    apply IHl1' with (l2 := witness ++ witness0).
      apply H.
      intros. assert (H3' := H3). apply ai_later with (b := x) in H3. apply H0 in H3. rewrite proof in H3.
      apply appears_in_app in H3. destruct H3.
          apply app_appears_in. left. apply H3.
          apply app_appears_in. right. inversion H3.
              rewrite H5 in H3'. apply contradiction_implies_anything with (P := appears_in x l1').
              split. apply H3'. apply H2. apply H5.
          rewrite proof in H1. rewrite app_length in H1. simpl in H1. rewrite <- plus_n_Sm in H1. apply Sn_le_Sm__n_le_m in H1. rewrite <-  app_length in H1. apply H1.
Qed.