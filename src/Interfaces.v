(** 
*)

From Equations Require Import Equations.

From Coq Require Import Arith List Lia Setoid Morphisms.
Import ListNotations.
From Clairvoyance Require Import Core Approx ApproxM List Misc BankersQueue Launchbury Cost.

Set Primitive Projections.
Set Implicit Arguments.
Set Contextual Implicit.
Set Maximal Implicit Insertion.

Definition option_bind {A B} (o : option A) (k : A -> option B) : option B :=
  match o with
  | None => None
  | Some a => k a
  end.

(* lookups xs [n; m; p] = [xs!!n; xs!!m; xs!!p], or None if out of bounds *)
Fixpoint lookups {A} (xs : list A) (ns : list nat) : option (list A) :=
  match ns with
  | [] => Some []
  | n :: ns =>
    option_bind (nth_error xs n) (fun x =>
    option_map (cons x) (lookups xs ns))
  end.

Module Pure.

Record Impl (op : Type) : Type :=
  { value : Type
  ; raw_eval_op : op -> list value -> list value
  }.

Definition eval_op {op : Type} {j : Impl op} (o : op) (ns : list nat) (xs : list j.(value))
  : list j.(value) :=
  match lookups xs ns with
  | None => xs  (* noop *)
  | Some vs => xs ++ j.(raw_eval_op) o vs
  end.

Fixpoint eval_ops {op : Type} {j : Impl op} (os : list (op * list nat)) (xs : list j.(value))
  : list j.(value) :=
  match os with
  | [] => xs
  | (o, ns) :: os => eval_ops os (eval_op o ns xs)
  end.

Module Cost.

Record Impl (op : Type) : Type :=
  { impl :> Pure.Impl op
    (* The cost may depend on the input *)
  ; raw_cost : op -> list impl.(value) -> nat
  }.

Definition cost {op : Type} {j : Impl op} (o : op) (ns : list nat) (vs : list j.(value)) : nat :=
  match lookups vs ns with
  | None => 0
  | Some xs => j.(raw_cost) o xs
  end.

Fixpoint eval {op : Type} {j : Impl op} (os : list (op * list nat)) (xs : list j.(value))
  : nat :=
  match os with
  | [] => 0
  | (o, ns) :: os => cost o ns xs + eval os (eval_op o ns xs)
  end.

End Cost.

End Pure.

Coercion Pure.Cost.impl : Pure.Cost.Impl >-> Pure.Impl.

Notation raw_cost_op := Pure.Cost.raw_cost.
Notation cost_op := Pure.Cost.cost.
Notation cost_ops := Pure.Cost.eval.

Module Cv.

Record Impl (op : Type) : Type :=
  { value : Type
  ; raw_eval_op : op -> list value -> M (list value)
  }.

Definition eval_op {op : Type} {j : Impl op} (o : op) (ns : list nat) (xs : list j.(value))
  : M (list j.(value)) :=
  match lookups xs ns with
  | None => ret xs  (* noop *)
  | Some vs => let! vs := j.(raw_eval_op) o vs in ret (xs ++ vs)
  end.

Fixpoint eval_ops {op : Type} {j : Impl op} (os : list (op * list nat)) (xs : list j.(value))
  : M (list j.(value)) :=
  match os with
  | [] => ret xs
  | (o, ns) :: os => let! xs := eval_op o ns xs in eval_ops os xs
  end.

End Cv.

Class ImplApprox (op : Type) (j : Pure.Impl op) (j' : Cv.Impl op) : Type :=
  { ImplExact :> Exact j.(Pure.value) j'.(Cv.value)
  ; ImplLessDefined :> LessDefined j'.(Cv.value)
  ; ImplPreOrder :> PreOrder (less_defined (a := j'.(Cv.value)))
  ; ImplLub :> Lub j'.(Cv.value)
  ; ImplLubLaw :> LubLaw j'.(Cv.value)
  ; raw_eval_mon : forall o,
      Proper (less_defined ==> less_defined) (j'.(Cv.raw_eval_op) o)
  }.

Definition sumof {A} (f : A -> nat) : list A -> nat :=
  fold_right (fun x s => f x + s) 0.

Class ImplCost (op : Type) (j : Pure.Cost.Impl op) (j' : Cv.Impl op) {IA : ImplApprox j j'} : Type :=
  { debt (* = potential *) : j'.(Cv.value) -> nat
  ; debts := sumof debt
  ; debt_lub : forall x y, debt (lub x y) <= debt x + debt y
  ; raw_eval_cost : forall (o : op) (vs : list j.(Pure.value)),
      forall output, output `is_approx` j.(Pure.raw_eval_op) o vs ->
      exists input, input `is_approx` vs /\
      j'.(Cv.raw_eval_op) o input [[ fun r c =>
        output `less_defined` r /\
        debts input + c <= j.(raw_cost_op) o vs + debts output ]]
  }.

Arguments ImplCost : clear implicits.
Arguments ImplCost {op} j j' {IA}.

Lemma less_defined_app {a} {LD : LessDefined a} (xs1 xs2 ys1 ys2 : list a)
  : xs1 `less_defined` ys1 -> xs2 `less_defined` ys2 ->
    (xs1 ++ xs2) `less_defined` (ys1 ++ ys2).
Proof.
  intros H J; induction H; cbn; [ auto | constructor; auto ].
Qed.

Lemma less_defined_app_inv {a} {LD : LessDefined a} (xs0 xs1 xs2 : list a)
  : xs0 `less_defined` (xs1 ++ xs2) ->
    exists xs01 xs02, xs0 = xs01 ++ xs02 /\
      xs01 `less_defined` xs1 /\ xs02 `less_defined` xs2.
Proof.
  revert xs0. induction xs1 as [ | x xs1 IH]; intros xs0 Hxs0; cbn.
  - exists [], xs0. split; [reflexivity | split; [ constructor | assumption ] ].
  - cbn in Hxs0. inversion Hxs0; clear Hxs0; subst.
    specialize (IH _ H3). destruct IH as (xs01 & xs02 & Hxs0 & Hxs1 & Hxs2).
    exists (x0 :: xs01), xs02.
    split; [ cbn; f_equal; auto | ].
    split; [ constructor; auto | auto ].
Qed.

Lemma exact_list_app {a aA} {EE : Exact a aA} (xs1 xs2 : list a)
  : exact (xs1 ++ xs2) = exact xs1 ++ exact xs2.
Proof. apply map_app. Qed.

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

Context {op : Type} (j : Pure.Cost.Impl op) (j' : Cv.Impl op)
  {IA : ImplApprox j j'} {IC : ImplCost j j'}.

Lemma debts_lub x y : cobounded x y -> debts (lub x y) <= debts x + debts y.
Proof.
  induction 1 as [ | ? ? ? ? ? ? IH ] using cobounded_list_ind;
    cbn; [ reflexivity | ].
  rewrite IH, debt_lub. clear. generalize (debt x) (debt y). lia.
Qed.

Lemma debts_app x y : debts (x ++ y) = debts x + debts y.
Proof.
  induction x as [ | ? ? IH ]; cbn; [ auto | rewrite IH ].
  generalize (debt a); lia.
Qed.

Lemma eval_cost (o : op) (ns : list nat) (vs : list j.(Pure.value)) output
  : output `is_approx` Pure.eval_op o ns vs ->
    exists input, input `is_approx` vs /\
    Cv.eval_op o ns input [[ fun r c =>
      output `less_defined` r /\
      debts input + c <= cost_op o ns vs + debts output ]].
Proof.
  unfold Cv.eval_op, Pure.eval_op.
  destruct (lookups vs ns) eqn:E; intros Hout.
  - rewrite exact_list_app in Hout. apply less_defined_app_inv in Hout.
    destruct Hout as (out1 & out2 & Hout & Hout1 & Hout2).
    apply raw_eval_cost in Hout2. destruct Hout2 as (input & Hin & HH).
    destruct (less_defined_lookups (f := debt) E Hin) as (input' & Hin' & Hdebt & HH').
    exists (lub input' out1).
    split; [ apply lub_least_upper_bound; auto | ].
    destruct (lookups_lub (ys := out1) HH') as (y1 & Hx & Hcob1 & Hy);
      [ eauto | ].
    rewrite Hy.
    mgo. relax; [ | intros ? ? Hr; mgo; rewrite Nat.add_0_r; exact Hr ].
    eapply optimistic_corelax;
      [ apply raw_eval_mon, lub_upper_bound_l; eauto | | ].
    { unfold uc; intros * ? ? []; split.
      - rewrite H1. apply less_defined_app; [ reflexivity | assumption ].
      - rewrite <- H2. lia. }
    relax; [ apply HH | cbn; intros r c [Hr Hc] ].
    split; [ rewrite Hout; apply less_defined_app; [apply lub_upper_bound_r |]; eauto | ].
    rewrite debts_lub by eauto. rewrite Hout, debts_app.
    unfold debts, cost_op. rewrite E, Hdebt.
    revert Hc. generalize (raw_cost_op j o l). lia.
  - exists output. rewrite (less_defined_lookups_None E Hout).
    split; [ auto | ]. mgo. split; [ reflexivity | lia ].
Qed.

Lemma eval_ops_mon os
  : Proper (less_defined ==> less_defined) (Cv.eval_ops os).
Proof.
Admitted.

Notation pr := (pointwise_relation _).

Lemma uc_ext {a} `{LessDefined a} : Proper (pr (pr eq) ==> iff) (uc (a := a)).
Proof.
  apply proper_sym_impl_iff; [ typeclasses eauto | ].
  unfold uc; intros ? ? Hf Hg *.
  rewrite <- Hf. apply Hg.
Qed.

Lemma ImplCostSoundness_aux
  : forall (os : list (op * list nat)) (vs : list j.(Pure.value)),
    forall output, output `is_approx` Pure.eval_ops os vs ->
    exists input, input `is_approx` vs /\
      Cv.eval_ops os input [[ fun r c =>
        output `less_defined` r /\ debts input + c <= cost_ops (j := j) os vs + debts output ]].
Proof.
  induction os as [ | [o ns] os IH ]; intros vs output Hout; cbn.
  - exists output. split; [apply Hout | ].
    apply optimistic_ret. split; [ reflexivity | lia ].
  - cbn in Hout. specialize (IH (Pure.eval_op o ns vs) output Hout).
    destruct IH as (input & Hin & IH).
    destruct (eval_cost _ _ _ Hin) as (inp & Hinp & HH).
    exists inp. split; [ auto | ].
    mgo. relax; [ apply HH | cbn; intros ? ? [HI HJ] ].
    eapply optimistic_corelax; [ apply eval_ops_mon; eassumption | | ].
    { eapply uc_ext; [ intros ? ?; rewrite Nat.add_assoc; reflexivity | apply uc_acost ]. }
    relax; [ apply IH | cbn; intros ? ? [HK HL] ].
    split; [ auto | ].
    lia.
Qed.

Theorem ImplCostSoundness
  : forall os : list (op * list nat),
    forall d, d `is_approx` Pure.eval_ops os [] ->
      Cv.eval_ops os [] [[ fun r c =>
        d `less_defined` r /\ c <= cost_ops (j := j) os [] + debts d ]].
Proof.
  intros os d Hd. destruct (ImplCostSoundness_aux os [] Hd) as (d0 & Hd0 & HH).
  inversion Hd0; clear Hd0; subst.
  exact HH.
Qed.

End Soundness.

(* Stateful semantics of laziness *)
Module St.

Import L.Notations.

Record Impl (op : Type) : Type :=
  { value : Type
  ; raw_eval_op : op -> list value -> L R (list value)
  }.

Definition eval_op {op : Type} {j : Impl op} (o : op) (ns : list nat) (xs : list j.(value))
  : L R (list j.(value)) :=
  match lookups xs ns with
  | None => L.ret xs  (* noop *)
  | Some vs => let^ vs := j.(raw_eval_op) o vs in L.ret (xs ++ vs)
  end.

Fixpoint eval_ops {op : Type} {j : Impl op} (os : list (op * list nat)) (xs : list j.(value))
  : L R (list j.(value)) :=
  match os with
  | [] => L.ret xs
  | (o, ns) :: os => let^ xs := eval_op o ns xs in eval_ops os xs
  end.

(* The cost of "evaluating to WHNF": start with an empty heap, run the computation,
   it doesn't matter what the final heap [h] and result [x] are. *)
Definition cost_from {a} (u : L R a) (h : heap) : NAT.t :=
  fun c => exists x, eval u empty_heap h c x.

End St.

Section RealTimeCost.

Context {op : Type} (j : Pure.Cost.Impl op) (j' : St.Impl op).

Notation op' := (op * list nat)%type.

Definition RealTimeCost : Prop :=
  forall (os : list op') (o : op) (ns : list nat),
  forall h c0 xs,
    eval (St.eval_ops (j := j') os []) empty_heap h c0 xs ->
    ( St.cost_from (St.eval_op o ns xs) h
    <= NAT.of_nat (cost_op (j := j) o ns (Pure.eval_ops os []))
    )%NAT.

End RealTimeCost.

Definition ImplRealTimeCost
    (op : Type) (j : Pure.Cost.Impl op) (j' : Cv.Impl op) {IA : ImplApprox j j'}
  : Prop :=
  forall (os : list (op * list nat)) (o : op) (ns : list nat),
    ( cost_of (Cv.eval_ops (j := j') (os ++ [(o, ns)]) [])
    <= cost_of (Cv.eval_ops (j := j') os []) + cost_op o ns (Pure.eval_ops (j := j) os [])
    )%NAT.

(* Example *)
Module Queue.

Definition a := nat.

Inductive Op : Type :=
| Init (x : a)
| Empty
| Push
| Pop
.

Inductive Value : Type :=
| Q (q : Queue a)
| E (x : a)
.

Definition raw_eval (o : Queue.Op) (vs : list Value) : list Value :=
  match o, vs with
  | Empty, _ => [Q empty]
  | Push, Q q :: E x :: _ => [Q (push q x)]
  | Pop, Q q :: _ =>
    match pop q with
    | None => []
    | Some (x, q) => [E x; Q q]
    end
  | Init x, _ => [E x]
  | _, _ => []
  end.

Canonical j : Pure.Impl Queue.Op :=
  {| Pure.value := Value ; Pure.raw_eval_op := raw_eval |}.

Definition cost (_ : Queue.Op) (_ : list Value) : nat := 7.

Module Cv.

Inductive Value : Type :=
| Q (q : T (QueueA a))
| E (x : T a)
.

Definition raw_eval (o : Queue.Op) (vs : list Value) : M (list Value) :=
  match o, vs with
  | Empty, _ => let~ q := emptyA in ret [Q q]
  | Push, Q q :: E x :: _ => let~ q' := pushA q x in ret [Q q']
  | Pop, Q q :: _ =>
    let! pop_q := popA q in
    match pop_q with
    | None => ret []
    | Some (x, q) => ret [E x; Q q]
    end
  | Init x, _ => ret [E (Core.Thunk x)]
  | _, _ => ret []
  end.

Canonical j : Cv.Impl Queue.Op :=
  {| Cv.value := Value ; Cv.raw_eval_op := raw_eval |}.

End Cv.

End Queue.
