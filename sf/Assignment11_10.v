Require Export Assignment11_09.

(* problem #10: 30 points *)

(** Write a type checking function [tyeq: tm -> ty -> bool].
**)

Definition tyeq T T' : bool :=
match T with
| TNat => match T' with | TNat => true | TBool => false end
| TBool => match T' with | TNat => false | TBool => true end
end.

Fixpoint tycheck (t: tm) (T: ty) : bool :=
match t with
| ttrue => tyeq T TBool
| tfalse => tyeq T TBool
| tif t1 t2 t3 => andb (andb (tycheck t1 TBool) (tycheck t2 T)) (tycheck t3 T)
| tzero => tyeq T TNat
| tsucc t1 => andb (tycheck t1 T) (tyeq T TNat)
| tpred t1 => andb (tycheck t1 T) (tyeq T TNat)
| tiszero t1 => andb (tycheck t1 TNat) (tyeq T TBool)
end.

Example tycheck_ex1:
  tycheck
    (tif (tiszero (tpred (tsucc (tsucc tzero)))) ttrue (tiszero (tsucc tzero))) 
    TBool 
  = true.
Proof. reflexivity. Qed.

Example tycheck_ex2:
  tycheck
    (tif (tiszero (tpred (tsucc (tsucc tzero)))) tzero (tiszero (tsucc tzero))) 
    TBool 
  = false.
Proof. reflexivity. Qed.

(** Prove that the type checking function [tyeq: tm -> ty -> bool] is correct.

    Hint: use the lemma [andb_prop].
**)

Check andb_prop.

Theorem tycheck_correct1: forall t T
    (TYCHK: tycheck t T = true),
  |- t \in T.
Proof.
induction t; induction T; intros; try (inversion TYCHK; subst); try constructor;
try (apply andb_true_iff in H0; induction H0; try (apply andb_true_iff in H; induction H)).
  apply IHt1. apply H.
  apply IHt2. apply H1.
  apply IHt3. apply H0.
  apply IHt1. apply H.
  apply IHt2. apply H1.
  apply IHt3. apply H0.
  inversion H0.
  apply IHt. apply H.
  inversion H0.
  apply IHt. apply H.
  apply IHt. apply H.
  inversion H0.
Qed.

Theorem tycheck_correct2: forall t T
    (HASTY: |- t \in T),
  tycheck t T = true.
Proof.
induction t; induction T; intros; try reflexivity; inversion HASTY; subst.
simpl. apply andb_true_iff. split. apply andb_true_iff. split.
apply (IHt1 TBool H2). apply (IHt2 TBool H4). apply (IHt3 TBool H5).
simpl. apply andb_true_iff. split. apply andb_true_iff. split.
apply (IHt1 TBool H2). apply (IHt2 TNat H4). apply (IHt3 TNat H5).
simpl. apply andb_true_iff. split.
apply (IHt TNat H0). reflexivity.
simpl. apply andb_true_iff. split.
apply (IHt TNat H0). reflexivity.
simpl. apply andb_true_iff. split.
apply (IHt TNat H0). reflexivity.
Qed.

(*-- Check --*)

Check (conj tycheck_ex1 tycheck_ex2 :
 (tycheck
    (tif (tiszero (tpred (tsucc (tsucc tzero)))) ttrue (tiszero (tsucc tzero))) 
    TBool 
  = true)
 /\
 (tycheck
    (tif (tiszero (tpred (tsucc (tsucc tzero)))) tzero (tiszero (tsucc tzero))) 
    TBool 
  = false)).

Check tycheck_correct1: forall t T
    (TYCHK: tycheck t T = true),
  |- t \in T.

Check tycheck_correct2: forall t T
    (HASTY: |- t \in T),
  tycheck t T = true.
