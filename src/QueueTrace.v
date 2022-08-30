From Clairvoyance Require Import Core Cost Approx BankersQueue RealtimeBankersQueue.

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

Fixpoint eval_trace_from {a} (t : trace a) (s : list (Queue a)) : list (Queue a) :=
  match t with
  | [] => s
  | o :: t =>
    let o := lookups o s empty in
    let q := eval_operation o in
    eval_trace_from t (s ++ [q])
  end.

Definition eval_trace {a} (t : trace a) : list (Queue a) :=
  eval_trace_from t [].

Definition evalA_operation {a} (o : operation a (QueueA a)) : M (QueueA a) :=
  match o with
  | Empty => ret emptyA
  | Push q x => pushA (Thunk q) (Thunk x)
  | Pop q => let! q := popA (Thunk q) in
    match q with
    | None => ret emptyA
    | Some (_, q) => force q
    end
  end.

Fixpoint evalA_trace_from {a} (t : trace a) (s : list (QueueA a)) : M (list (QueueA a)) :=
  match t with
  | [] => ret s
  | o :: t =>
    let o := lookups o s emptyA in
    let! q := evalA_operation o in
    evalA_trace_from t (s ++ [q])
  end.

Definition evalA_trace {a} (t : trace a) : M (list (QueueA a)) :=
  evalA_trace_from t [].

Import Tick.Notations.

#[global]
Instance Bottom_QueueA {a} : Bottom (QueueA a) := MkQueueA Undefined Undefined Undefined.

#[global]
Instance Lub_QueueA {a} : Lub (QueueA a). Admitted.

Definition coforce {a} `{Bottom a} (x : T a) : Tick a :=
  match x with
  | Undefined => bottom
  | Thunk x => Tick.ret x
  end.

Definition evalD_operation {a} (o : operation a (Queue a)) (d : QueueA a)
  : Tick (operation a (QueueA a)) :=
  match o with
  | Empty => Tick.ret Empty
  | Push q x =>
    let+ (q, _) := pushD q x d in
    let+ q := coforce q in
    Tick.ret (Push q x)
  | Pop q =>
    let+ q := popD q (Some (Thunk d, Undefined)) in
    let+ q := coforce q in
    Tick.ret (Pop q)
  end.

Definition unsnoc {a} (xs : list a) : option (list a * a).
Admitted.

Definition lookupsD {a} (o : operation a nat) (s : list (Queue a)) (d : operation a (QueueA a))
  : Tick (list (QueueA a)).
Admitted.

Definition evalD_trace_from {a} (t : trace a) (s : list (Queue a)) (d : list (QueueA a))
  : Tick (list (QueueA a)) :=
  match t with
  | [] => Tick.ret d
  | o :: t =>
    let o' := lookups o s empty in
    match unsnoc d with None => Tick.ret []  (* should not happen *)
    | Some (d, qD) =>
      let+ oD := evalD_operation o' qD in
      let+ d' := lookupsD o s oD in
      Tick.ret (lub d d')
    end
  end.

Definition evalD_trace {a} (t : trace a) (d : list (QueueA a)) : Tick unit :=
  let+ _ := evalD_trace_from t [] d in Tick.ret tt.

Definition evalD_trace0 {a} (t : trace a) : Tick unit :=
  evalD_trace t (List.map (fun _ => bottom) t).

Section CostSpecification.

Context {a} (op_bound : operation a (Queue a) -> nat).

Fixpoint aggreg_bound_from (t : list (operation a nat)) (s : list (Queue a)) : nat :=
  match t with
  | [] => 0
  | o :: t =>
    let o := map_operation (fun n => nth n s empty) o in
    let q := eval_operation o in
    op_bound o + aggreg_bound_from t (s ++ [q])
  end.

Definition aggreg_bound (t : list (operation a nat)) : nat :=
  aggreg_bound_from t [].

Definition amortized_spec : Prop :=
  forall t : trace a,
    (cost_of (evalA_trace t) <= aggreg_bound t)%NAT.

Definition cost_after (t : trace a) (o : operation a nat) : NAT.t :=
  cost_of (evalA_trace (t ++ [o])) - cost_of (evalA_trace t).

Definition bound_after (t : trace a) (o : operation a nat) : nat :=
  let o := lookups o (eval_trace t) empty in
  op_bound o.

Definition worstcase_spec : Prop :=
  forall (t : trace a) (o : operation a nat),
    (cost_after t o <= bound_after t o)%NAT.

Theorem worstcase_amortized : worstcase_spec -> amortized_spec.
Admitted.

Definition cost_afterD (t : trace a) (o : operation a nat) : nat :=
  Tick.cost (evalD_trace0 (t ++ [o])) - Tick.cost (evalD_trace0 t).

Definition worstcase_specD : Prop :=
  forall (t : trace a) (o : operation a nat),
    cost_afterD t o <= bound_after t o.

Theorem cost_eval_trace_AD {t : trace a}
  : (cost_of (evalA_trace t) = Tick.cost (evalD_trace0 t))%NAT.
Proof.
Admitted.

Lemma cost_after_AD {t : trace a} {o : operation a nat}
  : (cost_after t o = cost_afterD t o)%NAT.
Proof.
  unfold cost_after, cost_afterD.
Admitted.

Theorem worstcase_spec_AD : worstcase_specD -> worstcase_spec.
Admitted.

End CostSpecification.

Section ConcreteSpec.

Context {a : Type}.

(* All bounded by a constant *)
Definition operation_bound (o : operation a (Queue a)) : nat := 7.

Theorem worstcase_costD : worstcase_specD operation_bound.
Admitted.

Theorem worstcase_cost : worstcase_spec operation_bound.
Proof.
  apply worstcase_spec_AD, @worstcase_costD.
Qed.

Theorem amortized_cost : amortized_spec operation_bound.
Proof.
  apply worstcase_amortized, @worstcase_cost.
Qed.

End ConcreteSpec.
