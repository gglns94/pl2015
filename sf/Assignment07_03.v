Require Export Assignment07_02.

(* problem #03: 20 points *)

(** **** Exercise: 3 stars  (bevalR)  *)
(** Write a relation [bevalR] in the same style as
    [aevalR], and prove that it is equivalent to [beval].*)


Inductive bevalR: bexp -> bool -> Prop :=
  | E_BTrue : bevalR (BTrue) true
	| E_BFalse : bevalR (BFalse) false
	| E_BEq : forall (e1 e2: aexp) (n1 n2 : nat),
						aevalR e1 n1 -> aevalR e2 n2 -> bevalR (BEq e1 e2) (beq_nat n1 n2)
	| E_BLe : forall (e1 e2 : aexp) (n1 n2 : nat),
						aevalR e1 n1 -> aevalR e2 n2 -> bevalR (BLe e1 e2) (ble_nat n1 n2)
	| E_BNot : forall (e1 : bexp) (b : bool),
						 bevalR e1 b -> bevalR (BNot e1) (negb b)
	| E_BAnd : forall (e1 e2 : bexp) (b1 b2 : bool),
						 bevalR e1 b1 -> bevalR e2 b2 -> bevalR (BAnd e1 e2) (andb b1 b2)
.

Theorem beval_iff_bevalR : forall b bv,
  bevalR b bv <-> beval b = bv.
Proof.
split.
intros; induction H;
try rewrite aeval_iff_aevalR in H;
try rewrite aeval_iff_aevalR in H0;
try subst;
reflexivity.

generalize dependent bv. induction b; intros; try simpl in H; subst. 
  apply E_BTrue.
  apply E_BFalse.
  apply E_BEq; rewrite aeval_iff_aevalR; reflexivity.
  apply E_BLe; rewrite aeval_iff_aevalR; reflexivity.
  apply E_BNot. apply IHb. reflexivity.
  apply E_BAnd; try apply (IHb1 (beval b1)); try apply (IHb2 (beval b2)); reflexivity.
Qed.
(** [] *)

