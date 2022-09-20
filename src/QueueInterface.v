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

Definition eval_op_queue (o : Op) (vs : list (Queue a)) : list (Queue a) :=
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

#[global] Instance PureImpl_Queue : PureImpl Op (Queue a) := eval_op_queue.

#[global] Instance CostSpec_Queue : CostSpec Op (Queue a) :=
  fun o vs =>
    match o with
    | Empty | Push _ | Pop => 1
    end.

Definition QAa := QueueA a.

Definition exec_op_queue (o : Op) (vs : list QAa) : M (list QAa) :=
  match o, vs with
  | Empty, _ => let! q := emptyA in ret [q]
  | Push x, q :: _ => let! q' := pushA (Thunk q) (Thunk x) in ret [q']
  | Pop, q :: _ =>
    let! pop_q := popA (Thunk q) in
    match pop_q with
    | None => ret []
    | Some (x, q) => let! q := force q in ret [q]
    end
  | _, _ => ret []
  end.

#[global] Instance CvImpl_Queue : CvImpl Op QAa := exec_op_queue.

#[local] Instance exec_op_mon (o : Op) :
  Morphisms.Proper (Morphisms.respectful less_defined less_defined)
    (exec_op (op := Op) (valueA := QAa) o).
Proof.
  intros ? ? E. destruct o; cbn.
  - reflexivity.
  - destruct E as [ | ? ? ? ? E1 E].
    + reflexivity.
    + apply bind_mon; [ apply pushA_mon; reflexivity + auto | intros; apply ret_mon ].
      constructor; [ auto | constructor ].
  - destruct E as [ | ? ? ? ? E1 E ]; [ reflexivity | ].
    apply bind_mon; [ apply popA_mon; auto | intros ? ? []; [ reflexivity | ] ].
    destruct x1, y0.
    apply bind_mon; [ apply force_mon, H | intros ].
    apply ret_mon. constructor; [ assumption | constructor ].
Qed.

#[global] Instance ImplApprox_Queue : ImplApprox Op (Queue a) QAa.
Proof.
  econstructor; try typeclasses eauto.
Defined.

(* "debt" in BankersQueue *)
Definition potential : QAa -> nat := fun qA =>
  2 * sizeX 0 (frontA qA) - 2 * nbackA qA.

Lemma potential_lub_QueueA : forall qA qA' : QAa, cobounded qA qA' -> potential (lub qA qA') <= potential qA + potential qA'.
Proof.
  apply @LubDebt_QueueA.
Qed.

#[global] Instance HasAmortizedCost_Queue : HasAmortizedCost Op (Queue a) QAa.
Proof.
  apply Build_HasAmortizedCost with (potential := potential).
  - exact @potential_lub_QueueA.
  - admit.
Admitted.
