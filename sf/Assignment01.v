(** **** SNU 4190.310, 2015 Spring *)

(** Assignment 01 *)
(** Due: 2015/03/19 14:00 *)

Definition admit {T: Type} : T.  Admitted.

(** **** Problem #1 : 1 star (andb3) *)
(** Do the same for the [andb3] function below. This function should
    return [true] when all of its inputs are [true], and [false]
    otherwise. *)

Definition andb2 (b1:bool) (b2:bool) :bool :=
  match b1 with
  | true => b2
  | false => false
end.

Definition andb3 (b1:bool) (b2:bool) (b3:bool) : bool :=
  match b1 with
  | true =>  andb2 b2 b3
  | false => false
   end.

Example test_andb31:                 (andb3 true true true) = true.
Proof. simpl. reflexivity. Qed.

Example test_andb32:                 (andb3 false true true) = false.
Proof. simpl. reflexivity. Qed.

Example test_andb33:                 (andb3 true false true) = false.
Proof. simpl. reflexivity. Qed.

Example test_andb34:                 (andb3 true true false) = false.
Proof. simpl. reflexivity. Qed.

(** [] *)



(** **** Problem #2: 1 star (factorial) *)
(** Recall the standard factorial function:
<<
    factorial(0)  =  1 
    factorial(n)  =  n * factorial(n-1)     (if n>0)
>>
    Translate this into Coq. 

    Note that plus and multiplication are already defined in Coq.
    use "+" for plus and "*" for multiplication.
*)

Eval compute in 3 * 5.
Eval compute in 3+5*6.

Fixpoint factorial (n:nat) : nat := 
match n with
| 0 => 1
| S k => n * (factorial k)
end.

Example test_factorial1:          (factorial 3) = 6.
Proof. simpl. reflexivity. Qed.
Example test_factorial2:          (factorial 5) = 10 * 12.
Proof. simpl. reflexivity. Qed.
(** [] *)



(** **** Problem #3: 2 stars (blt_nat) *)
(** The [blt_nat] function tests [nat]ural numbers for [l]ess-[t]han,
    yielding a [b]oolean.  Use [Fixpoint] to define it. *)

Fixpoint blt_nat (n m : nat) : bool :=
  match n with
  | 0 => 
    match m with
    | 0 => false
    | S k => true
    end
  | S k =>
    match m with
    | 0 => false
    | S l => blt_nat k l
    end
end.

Example test_blt_nat1:             (blt_nat 2 2) = false.
Proof. simpl. reflexivity. Qed.
Example test_blt_nat2:             (blt_nat 2 4) = true.
Proof. simpl. reflexivity. Qed.
Example test_blt_nat3:             (blt_nat 4 2) = false.
Proof. simpl. reflexivity. Qed.
(** [] *)
