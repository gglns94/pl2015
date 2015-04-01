(* DO NOT Require Import other files. *)

Require Import Basics.


Module NatlistProblems.

(*** 
   See the chapter "Lists" for explanations of the following.
 ***)

Inductive natlist : Type :=
  | nil : natlist
  | cons : nat -> natlist -> natlist.

Notation "x :: l" := (cons x l) (at level 60, right associativity).
Notation "[ ]" := nil.
Notation "[ x ; .. ; y ]" := (cons x .. (cons y nil) ..).

Fixpoint app (l1 l2 : natlist) : natlist := 
  match l1 with
  | nil    => l2
  | h :: t => h :: (app t l2)
  end.

Notation "x ++ y" := (app x y) 
                     (right associativity, at level 60).

Definition hd (default:nat) (l:natlist) : nat :=
  match l with
  | nil => default
  | h :: t => h
  end.

Theorem app_assoc : forall l1 l2 l3 : natlist, 
  (l1 ++ l2) ++ l3 = l1 ++ (l2 ++ l3).   
Proof.
  intros l1 l2 l3. induction l1 as [| n l1'].
  - reflexivity.
  - simpl. rewrite -> IHl1'. reflexivity.  
Qed.

Fixpoint snoc (l:natlist) (v:nat) : natlist := 
  match l with
  | nil    => [v]
  | h :: t => h :: (snoc t v)
  end.

Fixpoint rev (l:natlist) : natlist := 
  match l with
  | nil    => nil
  | h :: t => snoc (rev t) h
  end.

Inductive natoption : Type :=
  | Some : nat -> natoption
  | None : natoption.  

Definition option_elim (d : nat) (o : natoption) : nat :=
  match o with
  | Some n' => n'
  | None => d
  end.









(** **** Problem #1 (10 pts) : 2 stars (list_funs) *)
(** Complete the definitions of [nonzeros], [oddmembers] and
    [countoddmembers] below. Have a look at the tests to understand
    what these functions should do. *)

Fixpoint nonzeros (l:natlist) : natlist :=
  match l with
  |  nil => []
  |  h::t => 
    match h with
    | 0 => nonzeros t
    | _ => h::nonzeros t
    end
  end.

Example test_nonzeros:            nonzeros [0;1;0;2;3;0;0] = [1;2;3].
Proof. simpl. reflexivity. Qed.
(** [] *)








(** **** Problem #2 (10 pts): 3 stars, advanced (alternate) *)
(** Complete the definition of [alternate], which "zips up" two lists
    into one, alternating between elements taken from the first list
    and elements from the second.  See the tests below for more
    specific examples.

    Note: one natural and elegant way of writing [alternate] will fail
    to satisfy Coq's requirement that all [Fixpoint] definitions be
    "obviously terminating."  If you find yourself in this rut, look
    for a slightly more verbose solution that considers elements of
    both lists at the same time.  (One possible solution requires
    defining a new kind of pairs, but this is not the only way.)  *)


Inductive opt_pair : Type :=
  | NN : natlist -> natlist -> opt_pair.

Fixpoint alternate (l1 l2 : natlist) : natlist :=
  match NN l1 l2 with
  | NN [] []=> nil
  | NN (h::t) [] => l1
  | NN [] (h::t) => l2
  | NN (h1::t1) (h2::t2) => app [h1; h2] (alternate t1 t2)
  end.

Example test_alternate1:        alternate [1;2;3] [4;5;6] = [1;4;2;5;3;6].
  Proof. simpl. reflexivity. Qed. 
Example test_alternate2:        alternate [1] [4;5;6] = [1;4;5;6].
 Proof. simpl. reflexivity. Qed. 
Example test_alternate3:        alternate [1;2;3] [4] = [1;4;2;3].
 Proof. simpl. reflexivity. Qed. 
Example test_alternate4:        alternate [] [20;30] = [20;30].
 Proof. simpl. reflexivity. Qed. 
(** [] *)









(** **** Problem #3 (60 pts) : 3 stars (list_exercises) *)
(** More practice with lists. *)

Theorem app_nil_end : forall l : natlist, 
  l ++ [] = l.   
Proof.
  intros.
  induction l as [|n].
  - simpl. reflexivity.
  - simpl. rewrite IHl. reflexivity.
Qed.

(** Hint: You may need to first state and prove some lemma about snoc and rev. *)
Theorem rev_involutive : forall l : natlist,
  rev (rev l) = l.
Proof.
  intros. induction l as [|n].
  - simpl. reflexivity.
  - Lemma n_rev_l : forall (n: nat) (l: natlist), rev (n :: l)= snoc (rev l) n.
    Proof.
      intros.
      induction l as [|n'].
      -simpl. reflexivity.
      - simpl. reflexivity.
    Qed.
    rewrite n_rev_l.
    Lemma rev_snoc : forall l n, rev (snoc l n) = n::(rev l).
    Proof. intros. induction l as [|n']. simpl. reflexivity. simpl. rewrite IHl. simpl. reflexivity. Qed.
    rewrite rev_snoc. rewrite IHl. reflexivity. Qed.   
  (* FILL IN HERE *)

(** There is a short solution to the next exercise.  If you find
    yourself getting tangled up, step back and try to look for a
    simpler way. *)
Theorem app_assoc4 : forall l1 l2 l3 l4 : natlist,
  l1 ++ (l2 ++ (l3 ++ l4)) = ((l1 ++ l2) ++ l3) ++ l4.
Proof.
  intros.
  rewrite app_assoc.
  rewrite app_assoc.
  reflexivity.
Qed.
  (* FILL IN HERE *)

Theorem snoc_append : forall (l:natlist) (n:nat),
  snoc l n = l ++ [n].
Proof.
  intros.
  induction l as [|n'].
  - simpl. reflexivity.
  - simpl. rewrite IHl. reflexivity.
Qed.

Theorem distr_rev : forall l1 l2 : natlist,
  rev (l1 ++ l2) = (rev l2) ++ (rev l1).
Proof.
  intros.
  induction l1 as [|n1'].
  simpl. rewrite app_nil_end. reflexivity.
  simpl. rewrite IHl1. 
  Lemma snoc_l1_l2_n : forall l1 l2 n, snoc (l1 ++ l2) n = l1 ++ snoc l2 n.
  Proof.
  intros.
  induction l1 as [|n1'].
  - simpl. reflexivity.
  - simpl. rewrite IHl1. reflexivity.
  Qed.
  rewrite snoc_l1_l2_n. reflexivity.
  Qed.

(** An exercise about your implementation of [nonzeros]: *)
Theorem nonzeros_app : forall l1 l2 : natlist,
  nonzeros (l1 ++ l2) = (nonzeros l1) ++ (nonzeros l2).
Proof.
  intros.
  induction l1 as [|n'].
  - simpl. reflexivity.
  - simpl. rewrite IHl1.
    destruct n' as [|n''].
    reflexivity. simpl. reflexivity.
Qed.








(** **** Problem #4 (20 pts) : 2 stars (beq_natlist) *)
(** Fill in the definition of [beq_natlist], which compares
    lists of numbers for equality.  Prove that [beq_natlist l l]
    yields [true] for every list [l]. 

    You can use [beq_nat] from Basics.v
*)

Fixpoint beq_nat n1 n2 :=
  match n1 with
  | O =>
    match n2 with
    | O => true
    | _ => false
    end
  | S n' =>
    match n2 with
    | O => false
    | S n'' => beq_nat n' n''
    end
  end.

Check beq_nat.

Definition and b1 b2 :=
  match b1 with
  | true => b2
  | false => false
  end.

Fixpoint beq_natlist (l1 l2 : natlist) : bool :=
  match l1 with
  | nil =>
    match l2 with
    | nil => true
    | _ => false
    end
  | h::t =>
    match l2 with
    | nil => false
    | h2::t2 => and (beq_nat h h2) (beq_natlist t t2)
    end
  end.

Example test_beq_natlist1 :   (beq_natlist nil nil = true).
  Proof. simpl. reflexivity. Qed.
 (* FILL IN HERE *)
Example test_beq_natlist2 :   beq_natlist [1;2;3] [1;2;3] = true.
  Proof. simpl. reflexivity. Qed.
Example test_beq_natlist3 :   beq_natlist [1;2;3] [1;2;4] = false.
  Proof. simpl. reflexivity. Qed.

(** Hint: You may need to first prove a lemma about reflexivity of beq_nat. *)
Theorem beq_natlist_refl : forall l:natlist,
  beq_natlist l l = true.
Proof.
  intros.
  induction l as [|n'].
  - simpl. reflexivity.
  - simpl.
    Lemma beq_nat_refl : forall n, beq_nat n n = true.
    Proof. induction n as [|n']. simpl. reflexivity. simpl. rewrite IHn'. reflexivity. Qed.
    rewrite (beq_nat_refl n'). simpl. apply IHl.
Qed. 
(** [] *)

















(** **** Problem #5 (10 pts) : 4 stars, advanced (rev_injective) *)

(** Hint: You can use the lemma [rev_involutive]. *)
Theorem rev_injective: forall l1 l2 : natlist, 
  rev l1 = rev l2 -> l1 = l2.
Proof.
  intros.
  Lemma inj : forall l1 l2, l1 = l2 -> rev l1 = rev l2.
  Proof.
  intros. rewrite H. reflexivity.
  Qed.
  apply (inj (rev l1) (rev l2)) in H.
  rewrite rev_involutive  in H.
  rewrite rev_involutive in H.
  apply H.
Qed.















(** **** Problem #6 (20 pts) : 2 stars (hd_opt) *)
(** Using the same idea, fix the [hd] function from earlier so we don't
   have to pass a default element for the [nil] case.  *)

Definition hd_opt (l : natlist) : natoption :=
  match l with
  | nil => None
  | h::t => Some h
  end.

Example test_hd_opt1 : hd_opt [] = None.
 Proof. simpl. reflexivity. Qed.

Example test_hd_opt2 : hd_opt [1] = Some 1.
Proof. simpl. reflexivity. Qed.

Example test_hd_opt3 : hd_opt [5;6] = Some 5.
Proof. simpl. reflexivity. Qed.


(** This exercise relates your new [hd_opt] to the old [hd]. *)
Theorem option_elim_hd : forall (l:natlist) (default:nat),
  hd default l = option_elim default (hd_opt l).
Proof.
  intros.
  induction l as [|n'].
  - simpl. reflexivity.
  - simpl. reflexivity.
Qed.




End NatlistProblems.
















Module Poly.

Inductive list (X:Type) : Type :=
  | nil : list X
  | cons : X -> list X -> list X.

Fixpoint app (X : Type) (l1 l2 : list X)
                : (list X) :=
  match l1 with
  | nil      => l2
  | cons h t => cons X h (app X t l2)
  end.

Fixpoint snoc (X:Type) (l:list X) (v:X) : (list X) :=
  match l with
  | nil      => cons X v (nil X)
  | cons h t => cons X h (snoc X t v)
  end.

Fixpoint rev (X:Type) (l:list X) : list X :=
  match l with
  | nil      => nil X
  | cons h t => snoc X (rev X t) h
  end.

Fixpoint length (X:Type) (l:list X) : nat :=
  match l with
  | nil   => 0
  | cons h t => S (length X t)
  end.

Arguments nil {X}.
Arguments cons {X} _ _.  (* use underscore for argument position that has no name *)
Arguments length {X} l.
Arguments app {X} l1 l2.
Arguments rev {X} l. 
Arguments snoc {X} l v.

Notation "x :: y" := (cons x y)
                     (at level 60, right associativity).
Notation "[ ]" := nil.
Notation "[ x ; .. ; y ]" := (cons x .. (cons y []) ..).
Notation "x ++ y" := (app x y)
                     (at level 60, right associativity).

Fixpoint map {X Y:Type} (f:X->Y) (l:list X)
             : (list Y) :=
  match l with
  | []     => []
  | h :: t => (f h) :: (map f t)
  end.

Inductive prod (X Y : Type) : Type :=
  pair : X -> Y -> prod X Y.

Arguments pair {X} {Y} _ _.

Notation "( x , y )" := (pair x y).

Notation "X * Y" := (prod X Y) : type_scope.

Definition fst {X Y : Type} (p : X * Y) : X :=
  match p with (x,y) => x end.

Definition snd {X Y : Type} (p : X * Y) : Y :=
  match p with (x,y) => y end.










(** **** Problem #7 (20 pts) : 2 stars (split) *)
(** The function [split] is the right inverse of combine: it takes a
    list of pairs and returns a pair of lists.  In many functional
    programing languages, this function is called [unzip].

    Uncomment the material below and fill in the definition of
    [split].  Make sure it passes the given unit tests. *)

Fixpoint split
           {X Y : Type} (l : list (X*Y))
           : (list X) * (list Y) :=
    match l with
    | nil => pair nil nil
    | h::t =>pair ((fst h)::(fst (split t))) ((snd h)::(snd (split t)))
    end.
Example test_split:
  split [(1,false);(2,false)] = ([1;2],[false;false]).
Proof.
  simpl.
  reflexivity.
 Qed.

Theorem split_map: forall X Y (l: list (X*Y)),
   fst (split l) = map fst l.
Proof.
  intros.
  induction l as [|n'].
  -simpl. reflexivity.
  -simpl. rewrite IHl. simpl. reflexivity.
Qed.
End Poly.