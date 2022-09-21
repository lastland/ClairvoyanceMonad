(* Instantiate Interfaces with BankersQueue *)
From Coq Require Import List RelationClasses.
From Clairvoyance Require Import Core Approx ApproxM List Misc BankersQueue Cost Interfaces.

Import ListNotations.

Set Primitive Projections.
Set Implicit Arguments.
Set Contextual Implicit.
Set Maximal Implicit Insertion.

#[global] Instance HasBottom_QueueA {a} : HasBottom (QueueA a) :=
  fun q => MkQueueA (nfrontA q) Undefined (nbackA q) Undefined.

#[global] Instance BottomIsLeast_QueueA {a} : BottomIsLeast (QueueA a).
Admitted.

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

#[global] Instance CvImpl_QueueA : CvImpl Op QAa := exec_op_queue.

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

#[global] Instance ApproxOrder_Queue : ApproxOrder Op (Queue a) QAa.
Proof.
  econstructor; try typeclasses eauto.
Defined.

#[global] Instance MonotoneCvImpl_QueueA : MonotoneCvImpl CvImpl_QueueA.
Proof.
Admitted.

(* "debt" in BankersQueue *)
#[local] Instance Potential_QueueA : Potential QAa := fun qA =>
  2 * sizeX 0 (frontA qA) - 2 * nbackA qA.

#[local] Instance PotentialLub_QueueA : PotentialLub QAa.
Proof.
  apply @LubDebt_QueueA.
Qed.

#[local] Instance PotentialBottom_QueueA : PotentialBottom QAa.
Proof. exact (fun _ => eq_refl). Qed.

#[local] Instance HasPotential_QueueA : HasPotential QAa.
Proof.
  econstructor; typeclasses eauto.
Defined.

#[global] Instance Physicist'sArgument_QueueA :
   Physicist'sArgument CostSpec_Queue CvImpl_QueueA.
Proof.
  econstructor.
Admitted.

Theorem HasAmortizedCost_Queue :
   HasAmortizedCost CostSpec_Queue CvImpl_QueueA.
Proof.
  apply physicist's_argument_soundness.
Qed.
