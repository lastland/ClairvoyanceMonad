(** 
*)

From Equations Require Import Equations.

From Coq Require Import Arith List Lia Setoid Morphisms.
Import ListNotations.
From Clairvoyance Require Import Core Approx ApproxM List Misc Cost.

Set Primitive Projections.
(* Set Implicit Arguments.
Set Contextual Implicit.
Set Maximal Implicit Insertion. *)

(* lookups xs [n; m; p] = [xs!!n; xs!!m; xs!!p], or None if out of bounds *)
Fixpoint lookups {A} (xs : list A) (ns : list nat) : option (list A) :=
  match ns with
  | [] => Some []
  | n :: ns =>
    option_bind (nth_error xs n) (fun x =>
    option_map (cons x) (lookups xs ns))
  end.

Class PureImpl (op value : Type) : Type :=
  eval_op : op -> list value -> list value.

Definition event (op : Type) : Type := (op * list nat).
Definition trace (op : Type) : Type := list (event op).
Notation stack := list (only parsing).

Section Pure.

Context {op value : Type} {pure_impl : PureImpl op value}.

Definition eval_event '((o, ns) : event op) (vs : stack value) : stack value :=
  match lookups vs ns with
  | None => vs  (* noop *)
  | Some xs => vs ++ eval_op o xs
  end.

Fixpoint eval_trace_from (es : trace op) (xs : stack value) : stack value :=
  match es with
  | [] => xs
  | e :: es => eval_trace_from es (eval_event e xs)
  end.

Definition eval_trace (es : trace op) : stack value := eval_trace_from es [].

End Pure.

(* The cost may depend on the input *)
Class CostSpec (op value : Type) : Type :=
  cost_op : op -> list value -> nat.

Section Cost.

Context {op value : Type} {pure_impl : PureImpl op value} {cost_spec : CostSpec op value}.

Definition cost_event '((o, ns) : event op) (vs : stack value) : nat :=
  match lookups vs ns with
  | None => 0
  | Some xs => cost_op o xs
  end.

Fixpoint cost_trace_from (es : trace op) (vs : stack value) : nat :=
  match es with
  | [] => 0
  | e :: es => cost_event e vs + cost_trace_from es (eval_event e vs)
  end.

Definition cost_trace (es : trace op) : nat := cost_trace_from es [].

End Cost.

Class CvImpl (op valueA : Type) : Type :=
  exec_op : op -> list valueA -> M (list valueA).

Section Cv.

Context {op valueA : Type} {cv_impl : CvImpl op valueA}.

Definition exec_event '((o, ns) : event op) (vs : stack valueA) : M (stack valueA) :=
  match lookups vs ns with
  | None => ret vs  (* noop *)
  | Some xs => let! ys := exec_op o xs in ret (vs ++ ys)
  end.

Fixpoint exec_trace_from (es : trace op) (vs : stack valueA) : M (stack valueA) :=
  match es with
  | [] => ret vs
  | e :: es => let! vs := exec_event e vs in exec_trace_from es vs
  end.

Definition exec_trace (es : trace op) : M (stack valueA) :=
  exec_trace_from es [].

End Cv.

(** Order structure on approximation values [valueA].
    Core operations ([exact], [less_defined], [lub], [bottom_of])
    and their properties. *)
Class ApproxOrder (op value valueA : Type) : Type :=
  { AO_Exact :> Exact value valueA
  ; AO_LessDefined :> LessDefined valueA
  ; AO_PreOrder :> PreOrder (less_defined (a := valueA))
  ; AO_Lub :> Lub valueA
  ; AO_LubLaw :> LubLaw valueA
  ; AO_HasBottom :> HasBottom valueA
  ; AO_BottomIsLeast :> BottomIsLeast valueA
  }.

(* Monotonicity of [exec_op] *)
Class MonotoneCvImpl {op value valueA}
    {approx_order : ApproxOrder op value valueA}
    (cv_impl : CvImpl op valueA) : Prop :=
  exec_op_mon : forall o, Proper (less_defined ==> less_defined) (exec_op (valueA := valueA) o).

(** Amortized cost specification. *)
Section HasAmortizedCost.

Context {op value valueA : Type}
  {pure_impl : PureImpl op value}
  {cost_spec : CostSpec op value}
  {cv_impl : CvImpl op valueA}.

(** The cost of executing the whole trace is less than
    its aggregated bound. *)
Definition HasAmortizedCost : Prop :=
  forall os : trace op,
    (cost_of (exec_trace os) <= cost_trace os)%NAT.

(** Equivalent formulation as a weakest precondition. *)
Definition HasAmortizedCost' : Prop :=
  forall os : trace op,
    exec_trace os [[ fun _ c => c <= cost_trace os ]].

Context
  {approx_order : ApproxOrder op value valueA}.

Theorem has_amortized_cost' :
  HasAmortizedCost <-> HasAmortizedCost'.
Admitted.

End HasAmortizedCost.

Arguments HasAmortizedCost : clear implicits.
Arguments HasAmortizedCost {op value valueA pure_impl} cost_spec cv_impl.

Arguments HasAmortizedCost' : clear implicits.
Arguments HasAmortizedCost' {op value valueA pure_impl} cost_spec cv_impl.

(** Clairvoyant Physicist's method *)

(* TODO: These classes are a bit of a mess. Find a good way to package all of the required operations and facts together. *)

Class Potential (a : Type) : Type :=
  potential : a -> nat.

Definition sumof {A} (f : A -> nat) : list A -> nat :=
  fold_right (fun x s => f x + s) 0.

#[global]
Instance Potential_list {a} `{Potential a} : Potential (list a) := sumof potential.

Class PotentialLub (a : Type) `{Potential a, LessDefined a, Lub a} : Prop :=
  potential_lub : forall x y : a, cobounded x y -> potential (lub x y) <= potential x + potential y.

#[global]
Instance PotentialLub_list {a} `{PotentialLub a} : PotentialLub (list a).
Proof.
  intros x y.
  induction 1 as [ | ? ? ? ? ? ? IH ] using cobounded_list_ind;
    cbn; [ reflexivity | ].
  rewrite IH, potential_lub by assumption.
  clear. generalize (potential x) (potential y). lia.
Qed.

Lemma potential_app {a} `{Potential a} (x y : list a)
  : potential (x ++ y) = potential x + potential y.
Proof.
  induction x as [ | x0 ? IH ]; cbn; [ auto | rewrite IH ]. lia.
Qed.

Class PotentialBottom (a : Type) `{Potential a, HasBottom a} : Prop :=
  potential_bottom : forall x : a, potential (bottom_of x) = 0.

#[global] Instance PotentialBottom_list {a} `{PotentialBottom a} : PotentialBottom (list a).
Proof.
  intros x; induction x as [ | ? ? IH ]; cbn; [ reflexivity | ].
  rewrite potential_bottom, IH. reflexivity.
Qed.

Class HasPotential {op value} valueA
    {approx_order : ApproxOrder op value valueA} : Type :=
  { _Potential :> Potential valueA
  ; _PotentialLub :> PotentialLub valueA
  ; _PotentialBottom :> PotentialBottom valueA
  }.

Section Physicist'sArgument.

Context {op value valueA : Type}
  {approx_order : ApproxOrder op value valueA}
  {pure_impl : PureImpl op value}
  {cost_spec : CostSpec op value}
  {cv_impl : CvImpl op valueA}.

(** Theorem statement: "the implementation [cv_impl] simulates [pure_impl]
    with amortized cost bounded above by [cost_spec] plus a potential
    difference." *)
(* Note: lazy evaluation works backwards.
   We are first given an [output] demand,
   obtained as an approximation of the reference output via [eval_op],
   and we have to find a matching [input] demand. *)
Class Physicist'sArgument : Type :=
  { for_some_potential :> HasPotential valueA
  ; exec_cost : forall (o : op) (vs : list value),
      forall output : stack valueA, output `is_approx` eval_op o vs ->
      exists input : stack valueA, input `is_approx` vs /\
      exec_op o input [[ fun r c =>
        output `less_defined` r /\
        potential input + c <= cost_op o vs + potential output ]]
  }.

End Physicist'sArgument.

Arguments Physicist'sArgument : clear implicits.
Arguments Physicist'sArgument {op value valueA approx_order pure_impl} cost_spec cv_impl.

(* Auxiliary lemmas *)

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

Section Soundness.

Context {op value valueA : Type}
  {approx_order : ApproxOrder op value valueA}
  {pure_impl : PureImpl op value}
  {cost_spec : CostSpec op value}
  {cv_impl : CvImpl op valueA}
  {monotone_cv_impl : MonotoneCvImpl cv_impl}
  {pa : Physicist'sArgument cost_spec cv_impl}.

Lemma exec_cost_event (e : event op) (vs : stack value) output
  : output `is_approx` eval_event e vs ->
    exists input, input `is_approx` vs /\
    exec_event e input [[ fun r c =>
      output `less_defined` r /\
      potential input + c <= cost_event e vs + potential output ]].
Proof.
  destruct e as [o ns].
  unfold eval_event, exec_event.
  destruct (lookups vs ns) eqn:E; intros Hout.
  - rewrite exact_list_app in Hout. apply less_defined_app_inv in Hout.
    destruct Hout as (out1 & out2 & Hout & Hout1 & Hout2).
    apply exec_cost in Hout2. destruct Hout2 as (input & Hin & HH).
    destruct (less_defined_lookups (f := potential) E _ Hin) as (input' & Hin' & Hpotential & HH'); change (sumof (A := valueA) potential) with (potential (a := list valueA)) in Hpotential.
    exists (lub input' out1).
    split; [ apply lub_least_upper_bound; auto | ].
    destruct (lookups_lub (ys := out1) HH') as (y1 & Hx & Hcob1 & Hy);
      [ eauto | ].
    rewrite Hy.
    mgo_. relax; [ | intros ? ? Hr; mgo_; rewrite Nat.add_0_r; exact Hr ].
    eapply optimistic_corelax;
      [ eapply exec_op_mon, lub_upper_bound_l; eauto | | ].
    { unfold uc; intros * ? ? []; split.
      - rewrite H1. apply less_defined_app; reflexivity + assumption.
      - rewrite <- H2. lia. }
    relax; [ apply HH | cbn; intros r c [Hr Hc] ].
    split; [ rewrite Hout; apply less_defined_app; [ apply lub_upper_bound_r; eauto | assumption ] | ].
    rewrite potential_lub by eauto. rewrite Hout, potential_app.
    rewrite E, Hpotential.
    revert Hc. generalize (cost_op o l). lia.
  - exists output. rewrite (less_defined_lookups_None E Hout).
    split; [ auto | ]. mgo_. split; [ reflexivity | lia ].
Qed.

Lemma eval_trace_from_mon os : Proper (less_defined ==> less_defined) (exec_trace_from os).
Proof.
Admitted.

Notation pr := (pointwise_relation _).

Lemma uc_ext {a} `{LessDefined a} : Proper (pr (pr eq) ==> iff) (uc (a := a)).
Proof.
  apply proper_sym_impl_iff; [ typeclasses eauto | ].
  unfold uc; intros ? ? Hf Hg *.
  rewrite <- Hf. apply Hg.
Qed.

Lemma physicist's_method_aux
  : forall (os : trace op) (vs : list value),
    forall output, output `is_approx` eval_trace_from os vs ->
    exists input, input `is_approx` vs /\
      exec_trace_from os input [[ fun r c =>
        output `less_defined` r /\ potential input + c <= cost_trace_from os vs + potential output ]].
Proof.
  induction os as [ | [o ns] os IH ]; intros vs output Hout; cbn.
  - exists output. split; [apply Hout | ].
    apply optimistic_ret. split; [ reflexivity | lia ].
  - cbn in Hout. specialize (IH (eval_event (o, ns) vs) output Hout).
    destruct IH as (input & Hin & IH).
    destruct (exec_cost_event _ _ _ Hin) as (inp & Hinp & HH).
    exists inp. split; [ auto | ].
    mgo_. relax; [ apply HH | cbn; intros ? ? [HI HJ] ].
    eapply optimistic_corelax; [ apply eval_trace_from_mon; eassumption | | ].
    { eapply uc_ext; [ intros ? ?; rewrite Nat.add_assoc; reflexivity | apply uc_acost ]. }
    relax; [ apply IH | cbn; intros ? ? [HK HL] ].
    split; [ auto | ].
    lia.
Qed.

Theorem physicist's_method : HasAmortizedCost cost_spec cv_impl.
Proof.
  apply has_amortized_cost'.
  intros os. destruct (physicist's_method_aux os [] (bottom_of (exact (eval_trace_from os [])))) as (d0 & Hd0 & HH).
  { apply bottom_is_least. }
  inversion Hd0; clear Hd0; subst.
  apply (optimistic_mon HH); cbn.
  intros ? ? [_ INEQ]. fold (cost_trace os) in INEQ.
  rewrite potential_bottom, Nat.add_0_r in INEQ.
  exact INEQ.
Qed.

End Soundness.

(*
Section RealTimeCost.

Context {op : Type} (j : CostSpec op) (j' : St.Impl op).

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
    (op : Type) (j : CostSpec op) (j' : Cv.Impl op) {AO : ApproxOrder j j'}
  : Prop :=
  forall (os : list (op * list nat)) (o : op) (ns : list nat),
    ( cost_of (exec_trace (j := j') (os ++ [(o, ns)]) [])
    <= cost_of (exec_trace (j := j') os []) + cost_op o ns (eval_trace (j := j) os [])
    )%NAT.
*)
