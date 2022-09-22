(** 
*)

From Equations Require Import Equations.

From Coq Require Import Arith List Lia Setoid Morphisms.
Import ListNotations.
From Clairvoyance Require Import Core Approx ApproxM List Misc Cost.

Set Primitive Projections.

(* * Preamble: miscellaneous definitions *)

(** Order structure on approximation values [valueA].
    Core operations ([exact], [less_defined], [lub], [bottom_of])
    and their properties. *)
Class ApproxAlgebra (t tA : Type) : Type :=
  { AO_Exact         :> Exact t     tA
  ; AO_LessDefined   :> LessDefined tA
  ; AO_Lub           :> Lub         tA
  ; AO_BottomOf      :> BottomOf    tA

  ; AO_PreOrder      :> PreOrder (less_defined (a := tA))
  ; AO_LubLaw        :> LubLaw        tA
  ; AO_BottomIsLeast :> BottomIsLeast tA
  }.

(* lookups xs [n; m; p] = [xs!!n; xs!!m; xs!!p], or None if out of bounds *)
Fixpoint lookups {A} (xs : list A) (ns : list nat) : option (list A) :=
  match ns with
  | [] => Some []
  | n :: ns =>
    option_bind (nth_error xs n) (fun x =>
    option_map (cons x) (lookups xs ns))
  end.

Definition Monotonic {a b} `{LessDefined a, LessDefined b} (f : a -> b) : Prop :=
  forall x y, x `less_defined` y -> f x `less_defined` f y.

Definition sumof {a} (f : a -> nat) : list a -> nat :=
  fold_right (fun x s => f x + s) 0.

Lemma sumof_app {a} (f : a -> nat)  (x y : list a) : sumof f (x ++ y) = sumof f x + sumof f y.
Proof.
  induction x as [ | x0 ? IH ]; cbn; [ auto | rewrite IH ]. lia.
Qed.

Definition SubadditiveMeasure {a : Type} (f : a -> nat) `{LessDefined a, Lub a} : Prop :=
  forall x y : a, cobounded x y -> f (lub x y) <= f x + f y.

Definition ZeroMeasure {a : Type} (f : a -> nat) `{BottomOf a} : Prop :=
  forall x, f (bottom_of x) = 0.

Lemma less_defined_lookups {a aA} {EE : Exact a aA} {LD : LessDefined aA}
    {f : aA -> nat} {ns : list nat} {xs ys : list a}
  : lookups xs ns = Some ys ->
    forall ysD : list aA, ysD `is_approx` ys ->
    exists xsD : list aA, xsD `is_approx` xs /\
      sumof f xsD <= sumof f ysD /\
      lookups xsD ns = Some ysD.
Proof. Admitted.

Lemma less_defined_lookups_None {a aA} {EE : Exact a aA} {LD : LessDefined aA}
    {ns : list nat} {xs : list a} {xsD : list aA}
  : lookups xs ns = None ->
    xsD `is_approx` xs -> lookups xsD ns = None.
Proof. Admitted.

Lemma nth_lub {a} `{LessDefined a, Lub a} {xs ys : list a} {x : a} {n : nat}
  : nth_error xs n = Some x ->
    cobounded xs ys ->
    exists y, nth_error ys n = Some y /\
      cobounded x y /\
      nth_error (lub xs ys) n = Some (lub x y).
Proof.
Admitted.

Lemma lookups_lub {a} `{LessDefined a, Lub a} {xs ys xs' : list a} {ns : list nat}
  : lookups xs ns = Some xs' ->
    cobounded xs ys ->
    exists ys',
      lookups ys ns = Some ys' /\
      cobounded xs' ys' /\
      lookups (lub xs ys) ns = Some (lub xs' ys').
Proof.
  intros Hns Hcob; revert xs' Hns; induction ns as [ | ? ? IH ]; cbn; intros xs'.
  - intros Hs; inversion Hs; clear Hs; subst.
    exists []; split; [ | split ]; do 3 econstructor.
  - destruct (nth_error _ _) as [ x | ] eqn:Hx; cbn; [ | discriminate ].
    destruct (lookups xs _) as [ xs'' | ] eqn:Hxs; cbn; [ | discriminate ].
    intros HH; inversion HH; clear HH; subst.
    specialize (IH _ eq_refl). destruct IH as (ys' & Hys & Hcobs & Hlub).
    destruct (nth_lub Hx Hcob) as (y & Hy & Hcoby & Hlub1).
    exists (y :: ys').
    rewrite Hy; cbn. rewrite Hys; cbn. split; [ reflexivity | ].
    rewrite Hlub1; cbn.
    split; [ apply cobounded_cons; auto | ].
    rewrite Hlub; cbn. reflexivity.
Qed.

Notation pr := (pointwise_relation _).

Lemma uc_ext {a} `{LessDefined a} : Proper (pr (pr eq) ==> iff) (uc (a := a)).
Proof.
  apply proper_sym_impl_iff; [ typeclasses eauto | ].
  unfold uc; intros ? ? Hf Hg *.
  rewrite <- Hf. apply Hg.
Qed.

(** * General interface for lazy data structures *)

Section Interface.

Context {op value valueA : Type}.
Context {approx_algebra : ApproxAlgebra value valueA}.

Definition Eval : Type := op -> list value -> list value.
Existing Class Eval.

Context {eval : Eval}.

Definition event : Type := (op * list nat).
Definition trace : Type := list event.
Notation stack := (list value) (only parsing).
Notation stackA := (list valueA) (only parsing).

Definition eval_event '((o, ns) : event) (vs : stack) : stack :=
  match lookups vs ns with
  | None => vs  (* noop *)
  | Some xs => vs ++ eval o xs
  end.

Fixpoint eval_trace_from (es : trace) (xs : stack) : stack :=
  match es with
  | [] => xs
  | e :: es => eval_trace_from es (eval_event e xs)
  end.

Definition eval_trace (es : trace) : stack := eval_trace_from es [].

(* The cost may depend on the input *)
Definition Budget : Type := op -> list value -> nat.
Existing Class Budget.

Context {budget : Budget}.

Definition budget_event '((o, ns) : event) (vs : stack) : nat :=
  match lookups vs ns with
  | None => 0
  | Some xs => budget o xs
  end.

Fixpoint budget_trace_from (es : trace) (vs : stack) : nat :=
  match es with
  | [] => 0
  | e :: es => budget_event e vs + budget_trace_from es (eval_event e vs)
  end.

Definition budget_trace (es : trace) : nat := budget_trace_from es [].

Definition Exec : Type := op -> list valueA -> M (list valueA).
Existing Class Exec.

Context {exec : Exec}.

Definition exec_event '((o, ns) : event) (vs : stackA) : M (stackA) :=
  match lookups vs ns with
  | None => ret vs  (* noop *)
  | Some xs => let! ys := exec o xs in ret (vs ++ ys)
  end.

Fixpoint exec_trace_from (es : trace) (vs : stackA) : M (stackA) :=
  match es with
  | [] => ret vs
  | e :: es => let! vs := exec_event e vs in exec_trace_from es vs
  end.

Definition exec_trace (es : trace) : M (stackA) :=
  exec_trace_from es [].
 
Class WellDefinedExec : Prop :=
  { monotonic_exec : forall o, Monotonic (exec o)
  }.

Context {wd_exec : WellDefinedExec}.

Lemma exec_trace_from_mon os : Proper (less_defined ==> less_defined) (exec_trace_from os).
Proof.
Admitted.

(** Amortized cost specification. *)
Section AmortizedCostSpec.

(** The cost of executing the whole trace is less than
    its aggregated bound. *)
Definition AmortizedCostSpec : Prop :=
  forall os : trace, (cost_of (exec_trace os) <= budget_trace os)%NAT.

(** Equivalent formulation as a weakest precondition. *)
Definition AmortizedCostSpec' : Prop :=
  forall os : trace, exec_trace os [[ fun _ c => c <= budget_trace os ]].

Theorem has_amortized_cost' :
  AmortizedCostSpec <-> AmortizedCostSpec'.
Admitted.

End AmortizedCostSpec.

(** Clairvoyant Physicist's method *)

(* TODO: These classes are a bit of a mess. Find a good way to package all of the required operations and facts together. *)

Definition Potential : Type := valueA -> nat.
Existing Class Potential.

Context {potential : Potential}.

Class WellDefinedPotential : Prop :=
  { potential_lub    : SubadditiveMeasure potential
  ; potential_bottom : ZeroMeasure potential
  }.

Context {wd_potential : WellDefinedPotential}.

Lemma potential_lub_list (potential_lub : SubadditiveMeasure potential) : SubadditiveMeasure (sumof potential).
Proof.
  intros x y.
  induction 1 as [ | ? ? ? ? ? ? IH ] using cobounded_list_ind;
    cbn; [ reflexivity | ].
  rewrite IH, potential_lub by assumption.
  clear. generalize (potential x) (potential y). lia.
Qed.

Lemma potential_lub_list_ : SubadditiveMeasure (sumof potential).
Proof. exact (potential_lub_list potential_lub). Qed.

Lemma potential_bottom_list (potential_bottom : ZeroMeasure potential) : ZeroMeasure (sumof potential).
Proof.
  intros x; induction x as [ | ? ? IH ]; cbn; [ reflexivity | ].
  rewrite potential_bottom, IH. reflexivity.
Qed.

Lemma potential_bottom_list_ : ZeroMeasure (sumof potential).
Proof. exact (potential_bottom_list potential_bottom). Qed.

(** Theorem statement: "the implementation [exec] simulates [_eval]
    with amortized cost bounded above by [budget] plus a potential
    difference." *)
(* Note: lazy evaluation works backwards.
   We are first given an [output] demand,
   obtained as an approximation of the reference output via [eval_op],
   and we have to find a matching [input] demand. *)
Definition Physicist'sArgument : Prop :=
  forall (o : op) (vs : list value),
    forall output : stackA, output `is_approx` eval o vs ->
    exists input : stackA, input `is_approx` vs /\
    exec o input [[ fun r c =>
      output `less_defined` r /\
      sumof potential input + c <= budget o vs + sumof potential output ]].
Existing Class Physicist'sArgument.

Context {exec_cost : Physicist'sArgument}.

Section Soundness.

Lemma exec_event_cost (e : event) (vs : stack) output
  : output `is_approx` eval_event e vs ->
    exists input, input `is_approx` vs /\
    exec_event e input [[ fun r c =>
      output `less_defined` r /\
      sumof potential input + c <= budget_event e vs + sumof potential output ]].
Proof.
  destruct e as [o ns].
  unfold eval_event, exec_event.
  destruct (lookups vs ns) eqn:E; intros Hout.
  - rewrite exact_list_app in Hout. apply less_defined_app_inv in Hout.
    destruct Hout as (out1 & out2 & Hout & Hout1 & Hout2).
    apply exec_cost in Hout2. destruct Hout2 as (input & Hin & HH).
    destruct (less_defined_lookups (f := potential) E _ Hin) as (input' & Hin' & Hpotential & HH').
    exists (lub input' out1).
    split; [ apply lub_least_upper_bound; auto | ].
    destruct (lookups_lub (ys := out1) HH') as (y1 & Hx & Hcob1 & Hy);
      [ eauto | ].
    rewrite Hy.
    mgo_. relax; [ | intros ? ? Hr; mgo_; rewrite Nat.add_0_r; exact Hr ].
    eapply optimistic_corelax;
      [ eapply monotonic_exec, lub_upper_bound_l; eauto | | ].
    { unfold uc; intros * ? ? []; split.
      - rewrite H1. apply less_defined_app; reflexivity + assumption.
      - rewrite <- H2. lia. }
    relax; [ apply HH | cbn; intros r c [Hr Hc] ].
    split; [ rewrite Hout; apply less_defined_app; [ apply lub_upper_bound_r; eauto | assumption ] | ].
    rewrite potential_lub_list_ by eauto. rewrite Hout, sumof_app.
    rewrite E, Hpotential.
    revert Hc. generalize (budget o l). lia.
  - exists output. rewrite (less_defined_lookups_None E Hout).
    split; [ auto | ]. mgo_. split; [ reflexivity | lia ].
Qed.

Lemma physicist's_method_aux
  : forall (os : trace) (vs : list value),
    forall output, output `is_approx` eval_trace_from os vs ->
    exists input, input `is_approx` vs /\
      exec_trace_from os input [[ fun r c =>
        output `less_defined` r /\ sumof potential input + c <= budget_trace_from os vs + sumof potential output ]].
Proof.
  induction os as [ | [o ns] os IH ]; intros vs output Hout; cbn.
  - exists output. split; [apply Hout | ].
    apply optimistic_ret. split; [ reflexivity | lia ].
  - cbn in Hout. specialize (IH (eval_event (o, ns) vs) output Hout).
    destruct IH as (input & Hin & IH).
    destruct (exec_event_cost _ _ _ Hin) as (inp & Hinp & HH).
    exists inp. split; [ auto | ].
    mgo_. relax; [ apply HH | cbn; intros ? ? [HI HJ] ].
    eapply optimistic_corelax; [ apply exec_trace_from_mon; eassumption | | ].
    { eapply uc_ext; [ intros ? ?; rewrite Nat.add_assoc; reflexivity | apply uc_acost ]. }
    relax; [ apply IH | cbn; intros ? ? [HK HL] ].
    split; [ auto | ].
    lia.
Qed.

Theorem physicist's_method : AmortizedCostSpec.
Proof.
  apply has_amortized_cost'.
  intros os. destruct (physicist's_method_aux os [] (bottom_of (exact (eval_trace_from os [])))) as (d0 & Hd0 & HH).
  { apply bottom_is_least. }
  inversion Hd0; clear Hd0; subst.
  apply (optimistic_mon HH); cbn.
  intros ? ? [_ INEQ]. fold (budget_trace os) in INEQ.
  rewrite potential_bottom_list_, Nat.add_0_r in INEQ.
  exact INEQ.
Qed.

End Soundness.

End Interface.

Arguments Eval : clear implicits.
Arguments Budget : clear implicits.
Arguments Exec : clear implicits.
Arguments ApproxAlgebra : clear implicits.
Arguments Potential : clear implicits.

(* TODO: Can we prove a completeness theorem? For a more sophisticated method perhaps? *)
(* TODO: Can we prove lower bounds? This would be useful to check that [exec]
   isn't accidentally doing nothing. Also to know whether our upper bound is tight. *)

(*
Section RealTimeCost.

Context {op : Type} (j : Budget op) (j' : St.Impl op).

Notation op' := (op * list nat)%type.

Definition RealTimeCost : Prop :=
  forall (os : list op') (o : op) (ns : list nat),
  forall h c0 xs,
    eval (St.eval_trace (j := j') os []) empty_heap h c0 xs ->
    ( St.cost_from (St.eval_op o ns xs) h
    <= NAT.of_nat (cost_op (j := j) o ns (eval_trace os []))
    )%NAT.

End RealTimeCost.

Definition ImplRealTimeCost
    (op : Type) (j : Budget op) (j' : Cv.Impl op) {AO : ApproxAlgebra j j'}
  : Prop :=
  forall (os : list (op * list nat)) (o : op) (ns : list nat),
    ( cost_of (exec_trace (j := j') (os ++ [(o, ns)]) [])
    <= cost_of (exec_trace (j := j') os []) + cost_op o ns (eval_trace (j := j) os [])
    )%NAT.
*)
