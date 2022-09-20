(* Instantiate Interfaces with BankersQueue *)
From Coq Require Import List RelationClasses.
From Clairvoyance Require Import Core Approx ApproxM List Misc BankersQueue Cost Interfaces.

Import ListNotations.

Set Primitive Projections.
Set Implicit Arguments.
Set Contextual Implicit.
Set Maximal Implicit Insertion.

Definition a := nat.

Inductive Op : Type :=
| Empty
| Push
| Pop
| New (x : a)  (* As argument to push *)
.

Inductive Value : Type :=
| Q (q : Queue a)
| E (x : a)
.

Definition queue_eval_op (o : Op) (vs : list Value) : list Value :=
  match o, vs with
  | Empty, _ => [Q empty]
  | Push, Q q :: E x :: _ => [Q (push q x)]
  | Pop, Q q :: _ =>
    match pop q with
    | None => []
    | Some (x, q) => [E x; Q q]
    end
  | New x, _ => [E x]
  | _, _ => []
  end.

#[global] Instance queue_pure_impl : PureImpl Op Value := queue_eval_op.

Definition cost (_ : Op) (_ : list Value) : nat := 7.

Inductive ValueA : Type :=
| QA (q : T (QueueA a))
| EA (x : T a)
.

Definition queue_exec_op (o : Op) (vs : list ValueA) : M (list ValueA) :=
  match o, vs with
  | Empty, _ => let~ q := emptyA in ret [QA q]
  | Push, QA q :: EA x :: _ => let~ q' := pushA q x in ret [QA q']
  | Pop, QA q :: _ =>
    let! pop_q := popA q in
    match pop_q with
    | None => ret []
    | Some (x, q) => ret [EA x; QA q]
    end
  | New x, _ => ret [EA (Core.Thunk x)]
  | _, _ => ret []
  end.

#[global] Instance queue_cv_impl : CvImpl Op ValueA := queue_exec_op.

#[global] Instance Exact_Value : Exact Value ValueA := fun v =>
  match v with
  | Q q => QA (exact q)
  | E x => EA (exact x)
  end.

#[global] Instance Lub_ValueA : Lub ValueA := fun v v' =>
  match v, v' with
  | QA q, QA q' => QA (lub q q')
  | EA x, EA x' => EA (lub x x')
  | _, _ => EA Undefined
  end.

Inductive LessDefined_ValueA : LessDefined ValueA :=
| less_defined_QA {q q'} : q `less_defined` q' -> LessDefined_ValueA (QA q) (QA q')
| less_defined_EA {x x'} : x `less_defined` x' -> LessDefined_ValueA (EA x) (EA x')
.

#[local] Existing Instance LessDefined_ValueA.

#[local] Instance PreOrder_LessDefined_ValueA : PreOrder (less_defined (a := ValueA)).
Admitted.

#[local] Instance LubLaw_ValueA : LubLaw ValueA.
Admitted.

#[local] Instance exec_op_mon (o : Op) :
  Morphisms.Proper (Morphisms.respectful less_defined less_defined)
    (exec_op (op := Op) (valueA := ValueA) o).
Proof.
  intros ? ? E. destruct o; cbn.
  - reflexivity.
  - destruct E as [ | ? ? ? ? E1 E].
    + reflexivity.
    + destruct E1; [ | reflexivity ].
      destruct E as [ | ? ? ? ? E2 E]; [ reflexivity | ].
      destruct E2;  [ reflexivity | ].
      apply bind_mon; [ apply thunk_mon, pushA_mon; auto | intros; apply ret_mon ].
      constructor; constructor. auto.
  - destruct E as [ | ? ? ? ? E1 E ]; [ reflexivity | ].
    destruct E1; [ | reflexivity ].
    apply bind_mon; [ apply popA_mon; auto | intros ? ? []; [ reflexivity | ] ].
    destruct H0. destruct x0, y.
    apply ret_mon. repeat (assumption + constructor).
  - apply ret_mon. repeat constructor.
Qed.

#[global] Instance ImplApprox_Queue : ImplApprox Op Value ValueA.
Proof.
  econstructor; try typeclasses eauto.
Qed.
