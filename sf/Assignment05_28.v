Require Export Assignment05_27.

(* problem #28: 30 points *)


(** 4 stars (palindromes)  *)
(** A palindrome is a sequence that reads the same backwards as
    forwards.

    - Define an inductive proposition [pal] on [list X] that
      captures what it means to be a palindrome. (Hint: You'll need
      three cases.  Your definition should be based on the structure
      of the list; just having a single constructor
        c : forall l, l = rev l -> pal l
      may seem obvious, but will not work very well.)
 
    - Prove [pal_app_rev] that 
       forall l, pal (l ++ rev l).
    - Prove [pal_rev] that 
       forall l, pal l -> l = rev l.
*)

Inductive pal {X: Type} : list X -> Prop :=
| p_nil : pal []
| p_1: forall (x:X), pal [x]
| p_n: forall (x:X) (l: list X), pal l -> pal (x:: l ++ [x])
. (* Note *)

Theorem pal_app_rev: forall (X: Type) (l: list X),
  pal (l ++ rev l).
Proof.
  intros. induction l as [|n'].
  - simpl. apply p_nil.
  - simpl.
    Lemma snoc_app : forall {X:Type} (l:list X) (n:X),
      (snoc l n = l ++ [n]).
    Proof. intros. induction l as [|n']. simpl. reflexivity. simpl. rewrite IHl. reflexivity. Qed.
    rewrite snoc_app. apply p_n with (x := n') in IHl.
    Lemma app_assoc : forall {X: Type} (l0 : list X) (l1:list X) (l2:list X),
      l0 ++ l1 ++ l2 = (l0 ++ l1) ++ l2.
    Proof. intros. induction l0 as [|x]. simpl. reflexivity. simpl. rewrite IHl0. reflexivity. Qed.
    rewrite app_assoc with (l0 := l) (l1 := (rev l)) (l2 := [n']). apply IHl.
Qed.

Theorem pal_rev: forall (X: Type) (l: list X),
  pal l -> l = rev l.
Proof.
  intros. induction H.
  simpl. reflexivity.
  simpl. reflexivity.
  simpl. rewrite snoc_app.
  Lemma rev_app : forall {X:Type} (x : X) (l : list X),
    rev (l ++[x]) = x::(rev l).
  Proof. intros. induction l as [|x'].
    simpl. reflexivity.
    simpl. rewrite IHl. simpl. reflexivity.
  Qed.
  rewrite rev_app.
  rewrite <- IHpal.
  induction l as [|x'].
    simpl. reflexivity.
    simpl. reflexivity.
Qed.  