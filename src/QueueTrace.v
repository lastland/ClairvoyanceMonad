(* Amortized analysis of Realtime Bankers Queue *)

From Clairvoyance Require Import Core Cost RealtimeBankersQueue.

From Coq Require Import List.
Import ListNotations.

Set Implicit Arguments.
Set Contextual Implicit.

Inductive operation (a q : Type) : Type :=
| Empty : operation a q
| Push : q -> a -> operation a q
| Pop : q -> operation a q
.

Definition trace (a : Type) : Type := list (operation a nat).

Definition map_operation {a Q Q'} (f : Q -> Q') (o : operation a Q) : operation a Q' :=
  match o with
  | Empty => Empty
  | Push q x => Push (f q) x
  | Pop q => Pop (f q)
  end.

Definition lookups {a} {Q} (o : operation a nat) (s : list Q) (qdef : Q) : operation a Q :=
  map_operation (fun n => nth n s qdef) o.

Definition eval_operation {a} (o : operation a (Queue a)) : Queue a :=
  match o with
  | Empty => empty
  | Push q x => push q x
  | Pop q =>
    match pop q with
    | None => empty
    | Some (_, q) => q
    end
  end.

Fixpoint eval_trace_from {a} (os : trace a) (s : list (Queue a)) : list (Queue a) :=
  match os with
  | [] => s
  | o :: os =>
    let o := lookups o s empty in
    let q := eval_operation o in
    eval_trace_from os (s ++ [q])
  end.

Definition eval_trace {a} (os : trace a) : list (Queue a) :=
  eval_trace_from os [].

Definition evalA_operation {a} (o : operation a (QueueA a)) : M (QueueA a) :=
  match o with
  | Empty => ret emptyA
  | Push x q => pushA (Thunk x) (Thunk q)
  | Pop q => let! q := popA (Thunk q) in
    match q with
    | None => ret emptyA
    | Some (_, q) => force q
    end
  end.

Fixpoint evalA_trace_from {a} (os : trace a) (s : list (QueueA a)) : M (list (QueueA a)) :=
  match os with
  | [] => ret s
  | o :: os =>
    let o := lookups o s emptyA in
    let! q := evalA_operation o in
    evalA_trace_from os (s ++ [q])
  end.

Definition evalA_trace {a} (os : trace a) : M (list (QueueA a)) :=
  evalA_trace_from os [].

Section CostSpecification.

Context {a} (op_bound : operation a (Queue a) -> nat).

Fixpoint total_bound_from (os : list (operation a nat)) (s : list (Queue a)) : nat :=
  match os with
  | [] => 0
  | o :: os =>
    let o := map_operation (fun n => nth n s empty) o in
    let q := eval_operation o in
    op_bound o + total_bound_from os (s ++ [q])
  end.

Definition total_bound (os : list (operation a nat)) : nat :=
  total_bound_from os [].

Local Open Scope NAT.

Definition amortized_spec : Prop :=
  forall os : trace a,
    cost_of (evalA_trace os) <= total_bound os.

Definition cost_after (os : trace a) (o : operation a nat) : NAT.t :=
  cost_of (evalA_trace (os ++ [o])) - cost_of (evalA_trace os).       (* difference between running with the operation and running without *)

Definition bound_after (os : trace a) (o : operation a nat) : nat :=
  let o := lookups o (eval_trace os) empty in
  op_bound o.

Definition worstcase_spec : Prop :=
  forall (os : trace a) (o : operation a nat),
    cost_after os o <= bound_after os o.

Theorem worstcase_amortized : worstcase_spec -> amortized_spec.
Admitted.

End CostSpecification.

Section ConcreteSpec.

Context {a : Type}.

(* All bounded by a constant *)
Definition operation_bound (o : operation a (Queue a)) : nat := 7.

Theorem worstcase_cost : worstcase_spec operation_bound.
Admitted.

Theorem amortized_cost : amortized_spec operation_bound.
Proof.
  apply worstcase_amortized, @worstcase_cost.
Qed.

End ConcreteSpec.
