(*could parametrize by what is currently bool for more diverse return types*)

(** Definition of a machine, and some machines.*)
CoInductive oracle_machine {i o} :=
| Halts : bool -> oracle_machine
| Steps : oracle_machine -> oracle_machine
| Calls : i -> (o -> oracle_machine) -> oracle_machine
.


Definition machine := @oracle_machine Empty_set Empty_set.


(* The eval_machine proposition asserts that a machine halts with output bool b. *)
Inductive eval_oracle_machine {i o} (oracle: i -> o -> Prop) : @oracle_machine i o -> bool -> Prop :=
| EvalHalts b :
    eval_oracle_machine oracle (Halts b) b
| EvalSteps m b :
    eval_oracle_machine oracle m b ->
    eval_oracle_machine oracle (Steps m) b
| EvalCalls input output continuation b :
    oracle input output ->
    eval_oracle_machine oracle (continuation output) b -> 
    eval_oracle_machine oracle (Calls input continuation) b
.

Definition eval_tm : machine -> bool -> Prop := eval_oracle_machine (fun i => fun o => True). 


(* Some simple Turing machines: looper, collatz, dumb. *)
CoFixpoint looper : machine := Steps looper.

Require Import Nat.

CoFixpoint collatz (x:nat) :machine :=
  if leb x 1
  then Halts true
  else if even x
       then Steps (collatz (div2 x))
       else Steps (collatz (3*x+1))
.

Definition halter (b:bool) : machine := Halts b.


(** Definition of a language, and some languages.*)
Definition language input := input -> Prop.

Definition halt_tm : language machine := fun m => exists b, eval_tm m b.

Definition superhalt_tm : language oracle_machine := fun om => exists b, eval_oracle_machine (fun i : machine => fun o : bool => eval_tm i o) om b.

Definition a_tm : language machine := fun m => eval_tm m true.

Definition l_true : language bool := eq true.


(** Definition of deciding a language.*)
Definition decides {input} (im : input -> machine) (l:language input) : Prop :=
  forall i:input,
  exists b:bool,
    eval_tm (im i) b /\ (l i <-> b=true).

Definition decidable {input} (l : language input) : Prop :=
  exists (im : input -> machine),
    decides im l.

Hint Constructors eval_oracle_machine.

Theorem halter_decides_l_true: decides halter (l_true).
Proof.
  intro i.
  exists i.
  split.
  constructor.
  unfold l_true.
  firstorder.
Qed.

Definition isReduction {input0 input1} (f: (input1 -> machine) -> (input0 -> machine))
           (l0:language input0) (l1:language input1) : Prop :=
  forall (m1 : input1 -> machine),
    decides m1 l1
    -> decides (f m1) l0.

Definition hasReduction {input0 input1} (l0:language input0) (l1:language input1) : Prop :=
  exists (f: (input1 -> machine) -> (input0 -> machine)),
    isReduction f l0 l1.

Theorem reduction_decidable {input0 input1}:
  forall (l0 : language input0) (l1 : language input1),
    hasReduction l0 l1
    -> decidable l1
    -> decidable l0.
Proof.
  intros.
  inversion H0.
  inversion H.
  unfold decidable.
  exists (x0 x).
  apply H2.
  assumption.
Qed.

  
Definition undecidable {input} (l : language input) : Prop :=
  ~ decidable l.


Theorem reduction_undecidable {input0 input1}:
  forall (l0 : language input0) (l1 : language input1),
    hasReduction l0 l1
    -> undecidable l0
    -> undecidable l1.
Proof.
  intros.
  intro.
  apply H0.
  eapply reduction_decidable.
  eassumption.
  assumption.
Qed.


(** Proving the Halting Problem is undecidable.*)

Definition frob (m : machine) : machine :=
  match m with
    | Halts b => Halts b
    | Steps m' => Steps m'
    | Calls input continuation => Calls input continuation
  end.

Lemma frob_eq m : m = frob m.
Proof.
  destruct m; reflexivity.
Qed.
  
CoFixpoint invert_output (m: machine): machine :=
  match m with
    | Halts true => looper
    | Halts false => Halts true
    | Steps m => Steps (invert_output m)
    | Calls input continuation => Calls input (fun output => invert_output (continuation output))
  end.

Lemma looper_loops :
  forall b, ~ eval_tm looper b.
Proof.
  remember looper.
  rewrite (frob_eq looper) in Heqm.
  induction 1; intros.
  - discriminate.
  - injection Heqm.
    rewrite (frob_eq looper).
    assumption.
  - discriminate.
Qed.

Lemma invert_output_lemma:
  forall m,
    eval_tm m false
    <-> halt_tm (invert_output m).
Proof.
  split.
  { remember false.
    induction 1; subst.
    exists true.
    rewrite (frob_eq (invert_output _)).
    apply EvalHalts.
    destruct IHeval_oracle_machine.
    reflexivity.
    exists x.
    rewrite (frob_eq (invert_output _)).
    simpl.
    apply EvalSteps.
    assumption.
    destruct input. }
  { destruct 1.
    remember (invert_output m).
    rewrite (frob_eq (invert_output _)) in Heqm0.
    revert m Heqm0.
    induction H; intros.
    { destruct m.
      { destruct b0.
        { discriminate. }
        { apply EvalHalts. }
      }
      { discriminate. }
      { destruct e. }
    }
    { destruct m0.
      { apply IHeval_oracle_machine.
        destruct b0.
        { injection Heqm0.
          intro.
          rewrite (frob_eq looper) in H0.
          apply H0. }
        { discriminate. } }
      { injection Heqm0.
        intro.
        constructor.
        apply IHeval_oracle_machine.
        rewrite <- frob_eq.
        assumption.
      }
      { destruct e. }
    }
    { destruct input. }
  }
Qed.

Lemma only_one_value:
  forall m a b,
    eval_tm m a
    -> eval_tm m b
    -> a = b.
Proof.
  induction 1.
  inversion 1.
  reflexivity.
  inversion 1.
  subst.
  apply IHeval_oracle_machine.
  assumption.
  destruct input.
Qed.
  
  

Definition troll_machine (halt_solver: machine -> machine) (tested: machine): machine :=
  invert_output (halt_solver tested).

Axiom quineify: forall (pre_quine: machine -> machine), machine.
Axiom quine_behavior:
  forall (pre_quine: machine -> machine) (b: bool),
    eval_tm (quineify pre_quine) b <-> eval_tm (pre_quine (quineify pre_quine)) b.

(*CoFixpoint troll_quine (halt_solver: machine -> machine): machine :=
  (invert_output (halt_solver (troll_quine halt_solver))).*)

Require Import Coq.Setoids.Setoid.
Theorem halting_problem_undecidable: undecidable halt_tm.
Proof.
  intro.
  destruct H as [halt_solver Hd].
  pose (quineify (troll_machine halt_solver)) as quine.
  destruct Hd with quine.
  destruct H.
  pose proof (quine_behavior (troll_machine halt_solver)).
  pose proof (invert_output_lemma (halt_solver quine)).
  absurd (false = true).
  discriminate.
  destruct x.
  { eapply only_one_value.
    { apply <- H2.
      destruct (proj2 H0 eq_refl).
      exists x.
      apply H1.
      assumption. }
    { assumption. }
  }
  { apply H0.
    destruct (proj1 H2 H).
    exists x.
    apply <- H1.
    assumption. }
Qed.

           
(*Definition atm_undecidable: (undecidable atm).*)


Theorem superhalting_problem_undecidable: undecidable superhalt_tm.
Proof.









Theorem l_leq_superhalt


(*whatever!*)
