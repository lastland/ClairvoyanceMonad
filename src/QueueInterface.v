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
| Push (x : a)
| Pop
.

Definition queue_eval_op (o : Op) (vs : list (Queue a)) : list (Queue a) :=
  match o, vs with
  | Empty, _ => [empty]
  | Push x, q :: _ => [push q x]
  | Pop, q :: _ =>
    match pop q with
    | None => []
    | Some (x, q) => [q]
    end
  | _, _ => []
  end.

#[global] Instance PureImpl_Queue : PureImpl Op (Queue a) := queue_eval_op.

#[global] Instance CostSpec_Queue : CostSpec Op (Queue a) :=
  fun o vs =>
    match o with
    | Empty => 1
    | Push _ => 1
    | Pop => 1
    end.

Definition cost (_ : Op) (_ : list (Queue a)) : nat := 7.

Definition TQueueA := T (QueueA a).

Definition queue_exec_op (o : Op) (vs : list TQueueA) : M (list TQueueA) :=
  match o, vs with
  | Empty, _ => let~ q := emptyA in ret [q]
  | Push x, q :: _ => let~ q' := pushA q (Thunk x) in ret [q']
  | Pop, q :: _ =>
    let! pop_q := popA q in
    match pop_q with
    | None => ret []
    | Some (x, q) => ret [q]
    end
  | _, _ => ret []
  end.

#[global] Instance CvImpl_Queue : CvImpl Op TQueueA := queue_exec_op.

#[local] Instance exec_op_mon (o : Op) :
  Morphisms.Proper (Morphisms.respectful less_defined less_defined)
    (exec_op (op := Op) (valueA := TQueueA) o).
Proof.
  intros ? ? E. destruct o; cbn.
  - reflexivity.
  - destruct E as [ | ? ? ? ? E1 E].
    + reflexivity.
    + apply bind_mon; [ apply thunk_mon, pushA_mon; reflexivity + auto | intros; apply ret_mon ].
      constructor; constructor + auto.
  - destruct E as [ | ? ? ? ? E1 E ]; [ reflexivity | ].
    apply bind_mon; [ apply popA_mon; auto | intros ? ? []; [ reflexivity | ] ].
    destruct x1, y0.
    apply ret_mon. repeat (constructor + apply H).
Qed.

#[global] Instance ImplApprox_Queue : ImplApprox Op (Queue a) TQueueA.
Proof.
  econstructor; try typeclasses eauto.
Defined.

(* "debt" in BankersQueue *)
Definition potential : TQueueA -> nat := fun Tq =>
  match Tq with
  | Undefined => 0
  | Thunk qA => 2 * sizeX 0 (frontA qA) - 2 * nbackA qA
  end.

Lemma potential_lub_QueueA : forall qA qA' : TQueueA, cobounded qA qA' -> potential (lub qA qA') <= potential qA + potential qA'.
Proof.
  unfold TQueueA. apply @LubDebt_T, @LubDebt_QueueA.
Qed.

#[global] Instance HasAmortizedCost_Queue : HasAmortizedCost Op (Queue a) TQueueA.
Proof.
  apply Build_HasAmortizedCost with (potential := potential).
  - exact @potential_lub_QueueA.
  - admit.
Admitted.
