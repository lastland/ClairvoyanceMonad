(** 
*)

From Equations Require Import Equations.

From Coq Require Import Arith List Lia Setoid Morphisms.
Import ListNotations.
From Clairvoyance Require Import Core Approx ApproxM List Misc Cost Tick.

Import Tick.Notations.

Set Primitive Projections.

(* * Preamble: miscellaneous definitions *)

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

Class SubadditiveMeasure {a : Type} (f : a -> nat) `{LessDefined a, Lub a} : Prop :=
  subadditive_measure : forall x y : a, cobounded x y -> f (lub x y) <= f x + f y.

Class ZeroMeasure {a : Type} (f : a -> nat) `{BottomOf a} : Prop :=
  zero_measure : forall x, f (bottom_of x) = 0.

Lemma sumof_bottom {aA} `{BottomOf aA} {f : aA -> nat}
    {Hf_bottom : ZeroMeasure f}
  : forall xs : list aA, sumof f (bottom_of xs) = 0.
Proof.
  induction xs; cbn; [ reflexivity | ].
  rewrite Hf_bottom. auto.
Qed.

Lemma option_map_inv {a b} (f : a -> b) (x : option a) y
  : option_map f x = Some y ->
    exists x', x = Some x' /\ f x' = y.
Proof.
  destruct x; [ injection 1; eauto | discriminate ].
Qed.

Fixpoint lub_nth {a} `{Lub a} (n : nat) (x : a) (ys : list a) : list a :=
  match n, ys with
  | O, y :: ys => lub x y :: ys
  | S n, y :: ys => y :: lub_nth n x ys
  | _, [] => [] (* should not happen *)
  end.

Lemma sumof_lub_nth {a aA} {AA : IsApproxAlgebra a aA} {f : aA -> nat}
    {Hf_lub : SubadditiveMeasure f}
  : forall n x (ys : list aA),
      (exists y, nth_error ys n = Some y /\ cobounded x y) ->
      sumof f (lub_nth n x ys) <= f x + sumof f ys.
Proof.
  induction n as [ | n IH ]; intros x ys [y [Hnth Hxy] ].
  - destruct ys; cbn in *; [ discriminate | ].
    injection Hnth; intros ->.
    rewrite Hf_lub; auto. lia.
  - destruct ys; cbn in *; [ discriminate | ].
    rewrite IH; [ lia | eauto ].
Qed.

Lemma less_defined_lub_nth {a aA} {AA : IsApproxAlgebra a aA}
  : forall n (x : aA) ys w ws,
      ys `less_defined` ws ->
      nth_error ws n = Some w ->
      x `less_defined` w ->
      lub_nth n x ys `less_defined` ws.
Proof.
  induction n as [ | n IH]; intros x ys w [ | w' ws ]; cbn; try discriminate.
  - intros Hys; inv Hys.
    intros Hw; inv Hw.
    constructor; [ | auto].
    apply lub_least_upper_bound; auto.
  - intros Hys; inv Hys.
    intros Hw.
    constructor; [ auto | ].
    eapply IH; eauto.
Qed.

Lemma nth_error_exact {a aA} `{Exact a aA}
  : forall n xs, nth_error (exact xs) n = exact (nth_error xs n).
Proof.
  induction n as [ | n IH]; intros []; cbn; f_equal.
  apply IH.
Qed.

Lemma nth_error_exact' {a aA} `{Exact a aA}
  : forall n xs (y : a),
      nth_error xs n = Some y ->
      nth_error (exact xs) n = Some (exact y).
Proof.
  intros *; rewrite nth_error_exact. intros ->; reflexivity.
Qed.

Lemma less_defined_nth_error {a} `{LessDefined a}
  : Proper (less_defined ==> eq ==> less_defined) (@nth_error a).
Proof.
  intros xs ys Hxs n _ <-. revert xs ys Hxs; induction n as [| n IH]; cbn; intros ? ? []; try constructor; auto.
Qed.

Lemma less_defined_nth_error' {a} `{LessDefined a}
  : forall n xs ys (y : a),
      xs `less_defined` ys ->
      nth_error ys n = Some y ->
      exists x,
        nth_error xs n = Some x /\ x `less_defined` y.
Proof.
  intros * H0; apply less_defined_nth_error in H0.
  specialize (H0 n n eq_refl). destruct H0; try discriminate.
  intros Hy; inv Hy; eauto.
Qed.

Lemma nth_lub_nth {a} `{Lub a}
  : forall n (x y : a) ys,
    nth_error ys n = Some y ->
    nth_error (lub_nth n x ys) n = Some (lub x y).
Proof.
  induction n as [ | n IH ]; intros x y []; cbn; try discriminate.
  - intros Hy; inv Hy; reflexivity.
  - apply IH.
Qed.

Lemma nth_lub_nth' {a aA} `{IsApproxAlgebra a aA}
  : forall n m (x y : aA) ys,
    nth_error ys m = Some y ->
    cobounded x y ->
    nth_error ys n `less_defined` nth_error (lub_nth m x ys) n.
Proof.
  induction n as [ | n IH]; intros [] ? ? []; cbn; try discriminate + constructor.
  - inv H0. apply lub_upper_bound_r. auto.
  - inv H0; reflexivity.
  - intros HH; inv HH; reflexivity.
  - apply IH.
Qed.

Lemma lookups_lub_nth {a aA} `{IsApproxAlgebra a aA}
  : forall n x xs ns,
      (exists x', nth_error xs n = Some x' /\ cobounded x x') ->
      lookups xs ns `less_defined` lookups (lub_nth n x xs) ns.
Proof.
  intros * [x' [Hn Hx'] ]. induction ns as [ | n' ns IH]; cbn.
  - do 2 constructor.
  - assert (HH := nth_lub_nth' n' n _ _ _ Hn Hx').
    destruct HH; cbn; [ constructor | ].
    destruct IH; constructor; constructor; auto.
Qed.

#[global] Instance less_defined_option_map {a b} `{LessDefined a, LessDefined b}
  : Proper ((less_defined ==> less_defined) ==> less_defined ==> less_defined) (@option_map a b).
Proof.
  intros f f' Hf ? ? []; constructor.
  apply Hf. auto.
Qed.

#[global] Instance less_defined_cons {a} `{LessDefined a}
  : Proper (less_defined ==> less_defined ==> less_defined) (@cons a).
Proof. constructor; auto. Qed.

Lemma less_defined_option_bind {a b} `{LessDefined a, LessDefined b}
  : Proper (less_defined ==> (less_defined ==> less_defined) ==> less_defined) (@option_bind a b).
Proof.
  intros ? ? [] f g Hf; cbn.
  - constructor.
  - apply Hf; auto.
Qed.

Lemma less_defined_lookups {a} `{LessDefined a}
  : Proper (less_defined ==> eq ==> less_defined) (@lookups a).
Proof.
  intros xs ys Hxs ns _ <-; revert xs ys Hxs; induction ns as [| n ns IH ]; cbn.
  - constructor. constructor.
  - intros; apply less_defined_option_bind.
    + apply less_defined_nth_error; auto.
    + intros ? ? Hx. apply less_defined_option_map.
      { apply less_defined_cons. auto. }
      { apply IH. auto. }
Qed.

Lemma lookupsD_Some {a aA} {AA : IsApproxAlgebra a aA}
    {f : aA -> nat} {ns : list nat} {xs ys : list a}
    {Hf_bottom : ZeroMeasure f}
    {Hf_lub : SubadditiveMeasure f}
  : lookups xs ns = Some ys ->
    forall ysD : list aA, ysD `is_approx` ys ->
    exists xsD : list aA, xsD `is_approx` xs /\
      sumof f xsD <= sumof f ysD /\
      Some ysD `less_defined` lookups xsD ns.
Proof.
  revert xs ys; induction ns as [ | n ns IH ]; cbn; intros xs ys.
  - injection 1; intros <- ysD HysD.
    inversion HysD; clear HysD; subst.
    exists (bottom_of (exact xs)).
    split; [ apply bottom_is_least | ]. split; [ | reflexivity ].
    apply Nat.eq_le_incl, sumof_bottom.
  - destruct nth_error eqn:Hn; cbn; [ | discriminate ]. intros Hys ysD HysD.
    apply option_map_inv in Hys. destruct Hys as [ ys' [Hys' <-] ].
    inversion HysD; clear HysD; subst.
    apply IH with (ysD := xs0) in Hys'; [ | eauto ].
    destruct Hys' as [xsD [HxsD [Hsumof Hns] ] ].
    assert (Hex := nth_error_exact' _ _ _ Hn).
    destruct (less_defined_nth_error' n _ _ (exact a0) HxsD) as [x' [HxsD' Hx'] ]; [ auto |].
    exists (lub_nth n x xsD); split; [ | split ].
    + eapply less_defined_lub_nth; eauto.
    + cbn. etransitivity; [ apply sumof_lub_nth | ]; eauto 8. lia.
    + erewrite nth_lub_nth; [ cbn | eauto ].
      rewrite <- lookups_lub_nth by eauto 8.
      change (Some (x :: xs0)) with (option_map (cons x) (Some xs0)).
      apply less_defined_option_map; [ | auto ].
      apply less_defined_cons. apply lub_upper_bound_l; eauto.
Qed.

Lemma less_defined_lookups_None {a aA} {EE : Exact a aA} {LD : LessDefined aA}
    {ns : list nat} {xs : list a} {xsD : list aA}
  : lookups xs ns = None ->
    xsD `is_approx` xs -> lookups xsD ns = None.
Proof.
  revert xs xsD; induction ns as [ | n ns IH]; cbn; intros ? ? ? ?; [discriminate | ].
  assert (H' := less_defined_nth_error xsD (exact xs) H0 n n eq_refl).
  rewrite nth_error_exact in H'.
  destruct (nth_error xs n); inv H'; cbn in H |- *; [ | reflexivity ].
  erewrite IH; eauto.
  destruct lookups; [ discriminate | reflexivity ].
Qed.

Lemma nth_lub {a} `{LessDefined a, Lub a} {xs ys : list a} {x : a} {n : nat}
  : nth_error xs n = Some x ->
    cobounded xs ys ->
    exists y, nth_error ys n = Some y /\
      cobounded x y /\
      nth_error (lub xs ys) n = Some (lub x y).
Proof.
  revert xs ys; induction n as [ | n IH]; intros [ | ? xs] ys Hxs [zs [Hxz Hyz] ]; try discriminate.
  - inv Hxs; inv Hxz; inv Hyz. cbn. eexists; split; [ reflexivity | eauto ].
  - cbn in Hxs; inv Hxz; inv Hyz. cbn. apply IH; eauto.
Qed.

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

Class WellFormed (a : Type) : Type :=
  well_formed : a -> Prop.

#[local] Instance WellFormed_list {a} `{WellFormed a} : WellFormed (list a) :=
  List.Forall well_formed.

#[local] Instance WellFormed_option {a} `{WellFormed a} : WellFormed (option a) :=
  fun xs => match xs with
            | None => True
            | Some y => well_formed y
            end.

Lemma well_formed_nth_error {a} `{WellFormed a} (xs : list a) n
  : well_formed xs -> well_formed (nth_error xs n).
Proof.
  revert xs; induction n as [|n IH]; intros []; cbn; auto.
  - apply Forall_inv.
  - intros HH; eapply IH, Forall_inv_tail, HH.
Qed.

Lemma well_formed_lookups {a} `{WellFormed a} (xs : list a) (ns : list nat)
  : well_formed xs -> well_formed (lookups xs ns).
Proof.
  intros Hxs; induction ns as [|n ns IH]; cbn.
  - constructor.
  - assert (HH := well_formed_nth_error xs n Hxs). destruct nth_error; [ | constructor ].
    cbn. destruct lookups; constructor; auto.
Qed.

(** * General interface for lazy data structures *)

Section Interface.

Context {op value valueA : Type}.
Context {wf : WellFormed value}.
Context {approx_algebra : IsApproxAlgebra value valueA}.

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

Definition Demand : Type := op -> list value -> list valueA -> Tick (list valueA).
Existing Class Demand.

Context {demand : Demand}.

Definition appD {a b} (vs : list a) (vys : list b) : list b * list b :=
  (firstn (length vs) vys, skipn (length vs) vys).

(*
Definition bind_optionD {a b aA bA} (xs : option a) (ys : a -> option bA -> Tick aA) (
*)

Fixpoint nth_errorD (xs : list value) (n : nat) (xD : option valueA) : list valueA :=
  match n, xs with
  | O, x :: xs =>
    match xD with
    | Some xD => xD :: bottom_of (exact xs)
    | None => []  (* should not happen *)
    end
  | S n, x :: xs => bottom_of (exact x) :: nth_errorD xs n xD
  | _, [] => bottom_of (exact xs)
  end.

Fixpoint lookupsD (vs : stack) (ns : list nat) (xsD : option (list valueA)) : stackA :=
  match ns with
  | [] => bottom_of (exact vs)
  | n :: ns =>
    match nth_error vs n with
    | None => bottom_of (exact vs)
    | Some x =>
      match xsD with
      | None | Some [] => bottom_of (exact vs) (* Some [] should not happen *)
      | Some (xD :: xsD) => lub (nth_errorD vs n (Some xD)) (lookupsD vs ns (Some xsD))
      end
    end
  end.

Definition demand_event '((o, ns) : event) (vs : stack) (vysD : stackA) : Tick stackA :=
  match lookups vs ns with
  | None => Tick.ret vysD
  | Some xs =>
    let ys := eval o xs in
    let (vsD, ysD) := appD vs vysD in
    let+ xsD := demand o xs ysD in
    Tick.ret (lookupsD vs ns (Some xsD))
  end%tick.

Fixpoint demand_trace_from (es : trace) (xs : stack) (ysD : stackA) : Tick stackA :=
  match es with
  | [] => Tick.ret ysD
  | e :: es =>
    let+ xsD := demand_trace_from es (eval_event e xs) ysD in
    demand_event e xs xsD
  end.

Definition demand_trace (es : trace) : Tick unit :=
  let+ _ := demand_trace_from es [] (bottom_of (exact (eval_trace es))) in
  Tick.ret tt.

Definition WfEval : Prop := forall o vs, well_formed vs -> well_formed (eval o vs).
Existing Class WfEval.

Context {wf_eval : WfEval}.

Lemma wf_eval_event : forall e s, well_formed s -> well_formed (eval_event e s).
Proof.
  intros [] s Hs; cbn.
  assert (HH := well_formed_lookups s l Hs).
  destruct lookups; auto. apply Forall_app. split; auto.
  apply wf_eval. auto.
Qed.
 
Class WellDefinedExec : Prop :=
  { monotonic_exec : forall o, Monotonic (exec o)
  }.

Context {wd_exec : WellDefinedExec}.

Lemma exec_event_mon e : Proper (less_defined ==> less_defined) (exec_event e).
Proof.
  destruct e; cbn; intros ? ? Hs.
  destruct (less_defined_lookups _ _ Hs l l eq_refl).
  - apply ret_mon; auto.
  - apply bind_mon; [ apply monotonic_exec; auto | ].
    intros; apply ret_mon, less_defined_app; auto.
Qed.

Lemma exec_trace_from_mon os : Proper (less_defined ==> less_defined) (exec_trace_from os).
Proof.
  induction os; intros ? ? Hs; cbn.
  - apply ret_mon. auto.
  - apply bind_mon; [ apply exec_event_mon; auto | auto ].
Qed.

Definition pure_demand {a aA b bA} `{Exact a aA, Exact b bA, LessDefined aA, LessDefined bA}
    (f : a -> b) (fD : a -> bA -> Tick aA) : Prop :=
  forall x yD,
    yD `less_defined` exact (f x) ->
    Tick.val (fD x yD) `less_defined` exact x.

Definition cv_demand {a aA b bA} `{Exact a aA, Exact b bA, LessDefined aA, LessDefined bA}
    (f : a -> b) (fA : aA -> M bA) (fD : a -> bA -> Tick aA) : Prop :=
  forall x yD,
    yD `less_defined` exact (f x) ->
    forall n xD, Tick.MkTick n xD = fD x yD ->
    fA xD [[ fun yA m => yD `less_defined` yA /\ m <= n ]].

Definition PureDemand : Prop := forall o, pure_demand (eval o) (demand o).
Definition CvDemand : Prop := forall o, cv_demand (eval o) (exec o) (demand o).
Existing Class PureDemand.
Existing Class CvDemand.

Context {pd : PureDemand}.
Context {cd : CvDemand}.

Lemma cv_demand_trace_from : forall t xs ysD,
  ysD `less_defined` exact (eval_trace_from t xs) ->
  forall n xsD, Tick.MkTick n xsD = demand_trace_from t xs ysD ->
    exec_trace_from t xsD [[ fun ys m => ysD `less_defined` ys /\ m <= n ]].
Proof.
Admitted.

Lemma cv_demand_trace : forall t, exec_trace t [[ fun _ n => n <= Tick.cost (demand_trace t) ]].
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

Lemma forall_iff {A} (P Q : A -> Prop)
  : (forall x, P x <-> Q x) -> (forall x, P x) <-> (forall x, Q x).
Proof.
  intros H; split; intros; apply H; auto.
Qed.

(* The right-to-left implication (which is the one we actually need)
   assumes excluded middle.
   TODO: Perhaps redefine [(_ <= _)%NAT] (in AmortizedCostSpec) with a double negation.
   Then it's the other direction that would use excluded middle,
   but we don't care as much about it. *)
Theorem has_amortized_cost' :
  AmortizedCostSpec' <-> AmortizedCostSpec.
Proof.
  apply forall_iff; intros; symmetry; apply cost_of_bound_iff.
Qed.

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
#[local] Existing Instance potential_lub.
#[local] Existing Instance potential_bottom.

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
    well_formed vs ->
    forall output : stackA, output `is_approx` eval o vs ->
    exists input : stackA, input `is_approx` vs /\
    exec o input [[ fun r c =>
      output `less_defined` r /\
      sumof potential input + c <= budget o vs + sumof potential output ]].
Existing Class Physicist'sArgument.

Section Soundness.

Context {exec_cost : Physicist'sArgument}.

Lemma exec_event_cost (e : event) (vs : stack) output
  : well_formed vs ->
    output `is_approx` eval_event e vs ->
    exists input, input `is_approx` vs /\
    exec_event e input [[ fun r c =>
      output `less_defined` r /\
      sumof potential input + c <= budget_event e vs + sumof potential output ]].
Proof.
  destruct e as [o ns].
  unfold eval_event, exec_event.
  destruct (lookups vs ns) eqn:E; intros Hwf Hout.
  - rewrite exact_list_app in Hout. apply less_defined_app_inv in Hout.
    destruct Hout as (out1 & out2 & Hout & Hout1 & Hout2).
    apply exec_cost in Hout2.
    2:{ change (well_formed (Some l)). rewrite <- E. apply well_formed_lookups. auto. }
    destruct Hout2 as (input & Hin & HH).
    destruct (lookupsD_Some (f := potential) E _ Hin) as (input' & Hin' & Hpotential & HH').
    exists (lub input' out1).
    split; [ apply lub_least_upper_bound; auto | ].
    inv HH'. symmetry in H0.
    destruct (lookups_lub (ys := out1) H0) as (y1 & Hx & Hcob1 & Hy);
      [ eauto | ].
    rewrite Hy.
    mgo_. relax; [ | intros ? ? Hr; mgo_; rewrite Nat.add_0_r; exact Hr ].
    eapply optimistic_corelax.
    { eapply monotonic_exec. etransitivity; [ eassumption | apply lub_upper_bound_l; eauto ]. }
    { unfold uc; intros * ? ? []; split.
      - rewrite H3. apply less_defined_app; reflexivity + assumption.
      - rewrite <- H4. lia. }
    relax; [ apply HH | cbn; intros r c [Hr Hc] ].
    split; [ apply less_defined_app; [ apply lub_upper_bound_r; eauto | assumption ] | ].
    rewrite potential_lub_list_ by eauto. rewrite sumof_app.
    rewrite E, Hpotential.
    revert Hc. generalize (budget o l). lia.
  - exists output. rewrite (less_defined_lookups_None E Hout).
    split; [ auto | ]. mgo_. split; [ reflexivity | lia ].
Qed.

Lemma physicist's_method_aux
  : forall (os : trace) (vs : list value),
    well_formed vs ->
    forall output, output `is_approx` eval_trace_from os vs ->
    exists input, input `is_approx` vs /\
      exec_trace_from os input [[ fun r c =>
        output `less_defined` r /\ sumof potential input + c <= budget_trace_from os vs + sumof potential output ]].
Proof.
  induction os as [ | [o ns] os IH ]; intros vs Hwf output Hout; cbn.
  - exists output. split; [apply Hout | ].
    apply optimistic_ret. split; [ reflexivity | lia ].
  - cbn in Hout. specialize (IH (eval_event (o, ns) vs) (wf_eval_event (o, ns) vs Hwf) output Hout).
    destruct IH as (input & Hin & IH).
    destruct (exec_event_cost _ _ _ Hwf Hin) as (inp & Hinp & HH).
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
  intros os.
  destruct (physicist's_method_aux os [] (Forall_nil _) (bottom_of (exact (eval_trace_from os [])))) as (d0 & Hd0 & HH).
  { apply bottom_is_least. }
  inversion Hd0; clear Hd0; subst.
  apply (optimistic_mon HH); cbn.
  intros ? ? [_ INEQ]. fold (budget_trace os) in INEQ.
  rewrite potential_bottom_list_, Nat.add_0_r in INEQ.
  exact INEQ.
Qed.

End Soundness.

Definition Physicist'sArgumentD : Prop :=
  forall (o : op) (vs : list value), well_formed vs ->
  forall output : stackA, output `is_approx` eval o vs ->
  forall input n, Tick.MkTick n input = demand o vs output ->
  sumof potential input + n <= budget o vs + sumof potential output.
Existing Class Physicist'sArgumentD.

Section SoundnessD.

Context {demand_cost : Physicist'sArgumentD}.

Theorem demand_physicist's_argument : Physicist'sArgument.
Proof.
  red. red in demand_cost.
  intros o vs Hvs output Houtput. specialize (demand_cost o vs Hvs output Houtput _ _ eq_refl).
  exists (Tick.val (demand o vs output)).
  split.
  - apply pd. auto.
  - eapply optimistic_mon; [ eapply cd; [ eassumption | reflexivity ] | ].
    cbn beta. intros ? ? []; split; [ auto | lia ].
Qed.
#[export] Existing Instance demand_physicist's_argument.

End SoundnessD.

End Interface.

Arguments Eval : clear implicits.
Arguments Budget : clear implicits.
Arguments Exec : clear implicits.
Arguments Demand : clear implicits.
Arguments IsApproxAlgebra : clear implicits.
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
    (op : Type) (j : Budget op) (j' : Cv.Impl op) {AO : IsApproxAlgebra j j'}
  : Prop :=
  forall (os : list (op * list nat)) (o : op) (ns : list nat),
    ( cost_of (exec_trace (j := j') (os ++ [(o, ns)]) [])
    <= cost_of (exec_trace (j := j') os []) + cost_op o ns (eval_trace (j := j) os [])
    )%NAT.
*)
