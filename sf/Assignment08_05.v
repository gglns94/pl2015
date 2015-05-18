Require Export Assignment08_04.

(* problem #05: 20 points *)

(** Write a function which compiles an [aexp] into a stack
    machine program. The effect of running the program should be the
    same as pushing the value of the expression on the stack. *)

Fixpoint s_compile (e : aexp) : list sinstr :=
match e with
  | ANum n => [SPush n]
  | AId i => [SLoad i]
  | APlus e1 e2 => (s_compile e1)++(s_compile e2)++[(SPlus)]
  | AMinus e1 e2 => (s_compile e1)++(s_compile e2)++[(SMinus)]
  | AMult e1 e2 => (s_compile e1)++(s_compile e2)++[(SMult)]
end.

(** After you've defined [s_compile], prove the following to test
    that it works. *)

Example s_compile1 :
    s_compile (AMinus (AId X) (AMult (ANum 2) (AId Y)))
  = [SLoad X; SPush 2; SLoad Y; SMult; SMinus].
Proof.
  reflexivity.
Qed.

(** **** Exercise: 3 stars, advanced (stack_compiler_correct)  *)
(** The task of this exercise is to prove the correctness of the
    compiler implemented in the previous exercise.  Remember that
    the specification left unspecified what to do when encountering an
    [SPlus], [SMinus], or [SMult] instruction if the stack contains
    less than two elements.  (In order to make your correctness proof
    easier you may find it useful to go back and change your
    implementation!)

    Prove the following theorem, stating that the [compile] function
    behaves correctly.  You will need to start by stating a more
    general lemma to get a usable induction hypothesis; the main
    theorem will then be a simple corollary of this lemma. *)

Lemma rev_comp : forall (st:state) (l:list nat) (s:list sinstr) (e:aexp),
s_execute st l (s_compile e ++ s) = s_execute st ((aeval st e)::l) s.
Proof.
intros. revert st l s. induction e;
  try (intros; simpl; repeat rewrite <- ass_app; rewrite IHe1; rewrite IHe2);
  try reflexivity.
Qed.

Lemma s_compile_correct_foralll : forall (st : state) (l : list nat) (e : aexp),
s_execute st l (s_compile e) = aeval st e :: l.
Proof.
  intros. revert st l. induction e; intros; simpl;
    repeat rewrite rev_comp;
    reflexivity.
Qed.

Theorem s_compile_correct : forall (st : state) (e : aexp),
  s_execute st [] (s_compile e) = [ aeval st e ].
Proof.
  intros. apply s_compile_correct_foralll with (l:=[]).
Qed.

(*-- Check --*)
Check s_compile1 :
    s_compile (AMinus (AId X) (AMult (ANum 2) (AId Y)))
  = [SLoad X; SPush 2; SLoad Y; SMult; SMinus].

Check s_compile_correct : forall (st : state) (e : aexp),
  s_execute st [] (s_compile e) = [ aeval st e ].

