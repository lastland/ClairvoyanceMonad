(* Instantiate Interfaces with BankersQueue *)
From Coq Require Import List.
From Clairvoyance Require Import Core Approx ApproxM List Misc BankersQueue Cost Interfaces.

Import ListNotations.

Set Primitive Projections.
Set Implicit Arguments.
Set Contextual Implicit.
Set Maximal Implicit Insertion.

#[global] Instance BottomOf_QueueA {a} : BottomOf (QueueA a) :=
  fun q => MkQueueA (nfrontA q) Undefined (nbackA q) Undefined.

#[global] Instance BottomIsLeast_QueueA {a} : BottomIsLeast (QueueA a).
Admitted.

Definition a := nat.
Definition value := Queue a.
Definition valueA := QueueA a.
Notation stack := (list value) (only parsing).
Notation stackA := (list valueA) (only parsing).

Inductive op : Type :=
| Empty
| Push (x : a)
| Pop
.

Definition eval : Eval op value :=
  fun (o : op) (args : list value) => match o, args with
  | Empty, _ => [empty]
  | Push x, q :: _ => [push q x]
  | Pop, q :: _ =>
    match pop q with
    | None => []
    | Some (x, q) => [q]
    end
  | _, _ => []
  end.

Definition budget : Budget op value :=
  fun (o : op) (args : list value) => match o with
  | Empty | Push _ | Pop => 7
  end.

Definition exec : Exec op valueA :=
  fun (o : op) (args : list valueA) => match o, args with
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

#[export] Existing Instances eval budget exec.

Lemma monotonic_exec (o : op) : Monotonic (exec o).
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

Definition approx_algebra : ApproxAlgebra value valueA.
Proof. econstructor; try typeclasses eauto. Defined.
#[export] Existing Instance approx_algebra.

Lemma well_defined_exec : WellDefinedExec.
Proof. constructor; exact monotonic_exec. Qed.
#[export] Existing Instance well_defined_exec.

(* "debt" in BankersQueue *)
Definition potential : Potential valueA := (* ... *)
  fun qA => 2 * sizeX 0 (frontA qA) - 2 * nbackA qA.
#[export] Existing Instance potential.

Lemma well_defined_potential : WellDefinedPotential.
Proof.
  constructor; [ apply @LubDebt_QueueA | exact (fun _ => eq_refl) ].
Qed.
#[export] Existing Instance well_defined_potential.

Theorem physicist's_argument : Physicist'sArgument.
Proof.
  red.
Admitted.
#[export] Existing Instance physicist's_argument.

Theorem amortized_cost : AmortizedCostSpec.
Proof. apply physicist's_method. Qed.
