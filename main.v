(*could parametrize by what is currently bool for more diverse return types*)

(** Definition of a machine, and some machines.*)
CoInductive machine :=
| Halts : bool -> machine
| Steps : machine -> machine
.

CoFixpoint looper : machine := Steps looper.

CoFixpoint collatz (x:nat) :machine :=
  if (true)
  then if (true)
       then Steps (collatz x)
       else Steps (collatz (3*x+1))
  else Halts true.

Definition dumb (b:bool) : machine := Halts b.


(** Definition of a language, and some languages.*)
Definition language input := input -> Prop.

Inductive eval_tm : machine -> bool -> Prop :=
| EvalHalts b : eval_tm (Halts b) b
| EvalSteps m b : eval_tm m b -> eval_tm (Steps m) b.

Definition halt_tm : language machine := fun m => exists b, eval_tm m b.

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

Hint Constructors eval_tm.

Theorem dumb_decides_l_true: decides dumb (l_true).
Proof.
  intro i.
  exists i.
  split.
  auto.
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
    destruct IHeval_tm.
    reflexivity.
    exists x.
    rewrite (frob_eq (invert_output _)).
    simpl.
    apply EvalSteps.
    assumption. }
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
    }
    { destruct m0.
      { apply IHeval_tm.
        destruct b0.
        { injection Heqm0.
          intro.
          rewrite (frob_eq looper) in H0.
          apply H0. }
        { discriminate. } }
      { injection Heqm0.
        intro.
        constructor.
        apply IHeval_tm.
        rewrite <- frob_eq.
        assumption.
      }
    }
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
  apply IHeval_tm.
  assumption.
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
      destruct (proj2 H0 eq_refl).
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

           
Definition atm_undecidable: (undecidable atm).

(*whatever!*)