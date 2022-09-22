(* Overview

KNOWN
- Pure implementation of lazy queues: [Queue], [empty], [push], [pop]
- Clairvoyant-monadic implementation: [QueueA], [emptyA], [pushA], [popA]

NEW
- Demand functions: [pushD], [popD]
- (Physicist's method) Debt/negative potential: [debt]
- Amortized cost specifications: [pushA_cost], [popA_cost]
- Trees ("API traces" with sharing): [tree], [run_tree]
- Final theorem (statement and proof):
    the cost of executing a tree with [n] operations is [O(n)]
    ([good_queue : GOOD_QUEUE : Prop])

*)

From Equations Require Import Equations.

From Coq Require Import Arith List Lia Setoid Morphisms.
Import ListNotations.
From Clairvoyance Require Import Core Approx ApproxM List Misc.

Import RevCompare.

Set Primitive Projections.
Set Implicit Arguments.
Set Contextual Implicit.
Set Maximal Implicit Insertion.

#[local] Existing Instance Exact_id | 1.
#[local] Existing Instance LessDefined_id | 100.
#[local] Existing Instance PreOrder_LessDefined_id | 100.
#[local] Existing Instance ExactMaximal_id | 100.

(* Lazy persistent queue *)
(* Amortized O(1) push and pop with persistence *)
(* Assume arithmetic on [nat] is O(1) *)

(* Pure implementation *)

(** This is a queue with two lists, but rather than wait for the front to be empty
  (as in the simple non-persistent queue), we maintain the invariant that
  [length back <= length front] and reverse-and-append the back list at the end
  of the front list when [length back = length front + 1] (as soon as the
  invariant breaks).

  Thus, if [length back = length front + 1 = n], we create a thunk for reversing
  the back list, which costs [O(n)], but will only be forced after popping the [n+1]
  elements in front of it. That way, the cost of the thunk is amortized by those
  necessary operations before the thunk is forced. *)

Record Queue (a : Type) : Type := MkQueue
  { nfront : nat
  ; front : list a
  ; nback : nat
  ; back : list a
  }.

Definition mkQueue {a} (fn : nat) (f : list a) (bn : nat) (b : list a) : Queue a :=
  if fn <? bn then {| nfront := fn + bn ; front := append f (rev b) ; nback := 0 ; back := [] |}
  else {| nfront := fn ; front := f ; nback := bn ; back := b |}.

Definition empty {a} : Queue a := MkQueue 0 [] 0 [].

Definition push {a} (q : Queue a) (x : a) : Queue a :=
  mkQueue (nfront q) (front q) (S (nback q)) (x :: back q).

Definition pop {a} (q : Queue a) : option (a * Queue a) :=
  match front q with
  | x :: f => Some (x, mkQueue (pred (nfront q)) f (nback q) (back q))
  | [] => None
  end.

(* Monadic implementation *)
(* We consider the length fields are strict, for simplicity *)

Record QueueA (a : Type) : Type := MkQueueA
  { nfrontA : nat
  ; frontA : T (listA a)
  ; nbackA : nat
  ; backA : T (listA a)
  }.

Definition mkQueueA {a} (fn : nat) (f : T (listA a)) (bn : nat) (b : T (listA a)) : M (QueueA a) :=
  tick >>
  if fn <? bn then
    let~ b' := revA b in
    let~ f' := appendA f b' in
    ret (MkQueueA (fn + bn) f' 0 (Thunk NilA))
  else
    ret (MkQueueA fn f bn b).

Definition emptyA {a} : M (QueueA a) :=
  ret (MkQueueA 0 (Thunk NilA) 0 (Thunk NilA)).

Definition pushA {a} (q : T (QueueA a)) (x : T a) : M (QueueA a) :=
  tick >>
  let! q := force q in
  mkQueueA (nfrontA q) (frontA q) (S (nbackA q)) (Thunk (ConsA x (backA q))).

Definition popA {a} (q : T (QueueA a)) : M (option (T a * T (QueueA a))) :=
  tick >>
  let! q := force q in
  let! f := force (frontA q) in
  match f with
  | NilA => ret None
  | ConsA x f =>
    let~ q := mkQueueA (pred (nfrontA q)) f (nbackA q) (backA q) in
    ret (Some (x, q))
  end.

(** * Approximation structure for [QueueA] *)

(** [less_defined], [exact], [lub] *)

Record less_defined_QueueA {a} (q1 q2 : QueueA a) : Prop :=
  { ld_front : less_defined (frontA q1) (frontA q2)
  ; ld_back : less_defined (backA q1) (backA q2)
  ; ld_nfront : nfrontA q1 = nfrontA q2
  ; ld_nback : nbackA q1 = nbackA q2
  }.

#[global] Hint Constructors less_defined_QueueA : core.
#[global] Hint Resolve ld_front ld_back ld_nfront ld_nback : core.

#[global] Instance LessDefined_QueueA {a} : LessDefined (QueueA a) :=
  less_defined_QueueA.

#[global]
Instance Rep_QueueA {a} : Rep (QueueA a) (nat * T (listA a) * nat * T (listA a)) :=
  {| to_rep := fun q => (nfrontA q, frontA q, nbackA q, backA q)
  ;  from_rep := fun '(nf,f,nb,b) => MkQueueA nf f nb b
  |}.

#[global] Instance RepLaw_QueueA {a} : RepLaw (QueueA a) _.
Proof.
  constructor.
  - intros [ [ [nf f] nb] b]; reflexivity.
  - intros []; reflexivity.
Qed.

#[global] Instance LessDefinedRep_QueueA {a} : LessDefinedRep (QueueA a) _.
Proof.
  intros [] []; cbn; firstorder.
Qed.

#[global] Instance PreOrder_QueueA {a} : PreOrder (less_defined (a := QueueA a)).
Proof. exact PreOrder_Rep. Qed.

#[global] Instance Exact_Queue {a} : Exact (Queue a) (QueueA a) :=
  fun q => MkQueueA (nfront q) (exact (front q)) (nback q) (exact (back q)).

#[global] Instance ExactMaximal_QueueA {a} : ExactMaximal (QueueA a) (Queue a).
Proof.
  red; intros * []; cbn in *.
  apply exact_maximal in ld_front0; apply exact_maximal in ld_back0. destruct xA; cbn in *; subst.
  reflexivity.
Qed.

(* Partial function: we assume that both arguments approximate the same list *)
Fixpoint lub_listA {a} (xs ys : listA a) : listA a :=
  match xs, ys with
  | NilA, NilA => NilA
  | ConsA x xs, ConsA y ys => ConsA (lub_T (fun r _ => r) x y) (lub_T lub_listA xs ys)
  | _, _ => NilA  (* silly case *)
  end.

#[global] Instance Lub_listA {a} : Lub (listA a) := lub_listA.

#[global] Instance LubLaw_listA {a} : LubLaw (listA a).
Proof.
  constructor.
  - intros x y z Hx; revert y; induction Hx; intros ?; inversion 1; subst; cbn; constructor; auto.
    1: inversion H; subst; inversion H4; subst; try constructor; auto.
    1: inversion H; subst; inversion H5; subst; try constructor; auto.
    inversion H6; constructor; auto.
  - intros x y [z [ Hx Hy] ]; revert y Hy; induction Hx; intros ?; inversion 1; subst; cbn;
      constructor; auto.
    1: inversion H; inversion H3; constructor; reflexivity + auto.
    1: inversion H; inversion H4; constructor; reflexivity.
    inversion H5; subst; constructor; [ reflexivity | auto ].
  - intros x y [z [Hx Hy] ]; revert x Hx; induction Hy; intros ?; inversion 1; subst; cbn;
      constructor; auto.
    1: inversion H; inversion H3; subst; invert_approx; constructor; reflexivity + auto; inversion H7; invert_approx; reflexivity.
    1: inversion H; inversion H4; subst; invert_approx; constructor; reflexivity + auto; inversion H8; invert_approx; reflexivity.
    inversion H5; subst; constructor; [ reflexivity | auto ].
Qed.

#[global] Instance Lub_QueueA {a} : Lub (QueueA a) :=
  fun q1 q2 =>
    MkQueueA (nfrontA q1) (lub (frontA q1) (frontA q2)) (nbackA q1) (lub (backA q1) (backA q2)).

#[global] Instance LubRep_QueueA {a} : LubRep (QueueA a) (nat * T (listA a) * nat * T (listA a)).
Proof.
  intros [] []; reflexivity.
Qed.

#[global] Instance LubLaw_QueueA {a} : LubLaw (QueueA a).
Proof.
  exact LubLaw_LubRep.
Qed.

(** * Monotonicity *)

(** Making inputs of approximation functions more defined makes the output more defined.
  These can be used to generalize the demand specifications above to inputs greater than
  the input demand. *)

(** Proofs of monotonicity are largely automated by the [solve_mon] tactic from the
  [ApproxM] module. *)

Lemma appendA__mon {a} (xsA xsA' : listA a) (ysA ysA' : T (listA a))
  : xsA `less_defined` xsA' ->
    ysA `less_defined` ysA' ->
    append_ xsA  ysA `less_defined` append_ xsA' ysA'.
Proof.
  intros Hxs; revert ysA ysA'; induction Hxs; intros * Hys; cbn; solve_mon.
Qed.

#[global] Hint Resolve appendA__mon : mon.

Lemma appendA_mon {a} (xsA xsA' ysA ysA' : T (listA a))
  : xsA `less_defined` xsA' ->
    ysA `less_defined` ysA' ->
    appendA xsA  ysA `less_defined` appendA xsA' ysA'.
Proof.
  intros; unfold appendA; solve_mon.
Qed.

#[global] Hint Resolve appendA_mon : mon.

Lemma revA__mon {a} (xsA xsA' : listA a) (ysA ysA' : T (listA a))
  : xsA `less_defined` xsA' ->
    ysA `less_defined` ysA' ->
    revA_ xsA ysA `less_defined` revA_ xsA' ysA'.
Proof.
  intros Hxs; revert ysA ysA'; induction Hxs; intros * Hys; cbn; solve_mon.
Qed.

#[global] Hint Resolve revA__mon : mon.

Lemma revA_mon {a} (xsA xsA' : T (listA a))
  : xsA `less_defined` xsA' ->
    revA xsA `less_defined` revA xsA'.
Proof.
  intros; unfold revA; solve_mon.
Qed.

#[global] Hint Resolve revA_mon : mon.

Lemma mkQueueA_mon {a} (nf nf' nb nb' : nat) (f f' b b' : T (listA a))
  : nf = nf' ->
    f `less_defined` f' ->
    b `less_defined` b' ->
    nb = nb' ->
    mkQueueA nf f nb b `less_defined` mkQueueA nf' f' nb' b'.
Proof.
  intros; subst; unfold mkQueueA; solve_mon.
Qed.

#[global] Hint Resolve mkQueueA_mon : mon.

Lemma pushA_mon {a} (qA qA' : T (QueueA a)) xA xA'
  : qA `less_defined` qA' ->
    xA `less_defined` xA' ->
    pushA qA xA `less_defined` pushA qA' xA'.
Proof.
  intros; unfold pushA. solve_mon.
  apply mkQueueA_mon; auto.
Qed.

Lemma popA_mon {a} (qA qA' : T (QueueA a))
  : qA `less_defined` qA' ->
    popA qA `less_defined` popA qA'.
Proof.
  intros; unfold popA. solve_mon.
  apply mkQueueA_mon; auto.
Qed.

(**)

(** * Well-formedness *)

(** Invariants on [Queue] *)
Record well_formed {a} (q : Queue a) : Prop :=
  { skew : nback q <= nfront q
  ; frontn : nfront q = length (front q)
  ; backn : nback q = length (back q)
  }.

Lemma well_formed_empty {a} : well_formed (a := a) empty.
Proof.
  constructor; cbn; reflexivity.
Qed.

Lemma length_append {a} (xs ys : list a) : length (append xs ys) = length xs + length ys.
Proof.
  induction xs; cbn; lia.
Qed.

Lemma well_formed_mkQueue {a} nf (f : list a) nb b
  : nf = length f -> nb = length b -> well_formed (mkQueue nf f nb b).
Proof.
  unfold mkQueue; destruct (Nat.ltb_spec nf nb); intros; subst; constructor; cbn; auto.
  - lia.
  - rewrite length_append,rev_length; reflexivity.
Qed.

Lemma well_formed_push {a} (q : Queue a) (x : a) : well_formed q -> well_formed (push q x).
Proof.
  intros wf_q. apply well_formed_mkQueue.
  - apply (frontn wf_q).
  - cbn; f_equal; apply (backn wf_q).
Qed.

Lemma well_formed_pop {a} (q : Queue a) x q'
  : well_formed q -> pop q = Some (x, q') -> well_formed q'.
Proof.
  intros wf_q; unfold pop.
  destruct (front q) eqn:Ef; [ discriminate | ].
  injection 1. intros <- ->.
  apply well_formed_mkQueue.
  - rewrite (frontn wf_q), Ef. reflexivity.
  - apply (backn wf_q).
Qed.

(** * The tick monad *)

Module Tick.

Record Tick (a : Type) : Type := MkTick
  { cost : nat
  ; val : a
  }.

Arguments MkTick {a}.
Arguments cost {a}.
Arguments val {a}.

Definition ret {a} : a -> Tick a := MkTick 0.
Definition bind {a b} (u : Tick a) (k : a -> Tick b) : Tick b :=
  {| cost := cost u + cost (k (val u))
  ;  val := val (k (val u))
  |}.

Definition tick : Tick unit := MkTick 1 tt.

Module Notations.
Declare Scope tick_scope.
Delimit Scope tick_scope with tick.
Bind Scope tick_scope with Tick.

Notation "'let+' x := u 'in' k" := (bind u (fun x => k%tick))
  (at level 200, x as pattern) : tick_scope.
Notation "u >> v" := (bind u (fun _ => v%tick)) : tick_scope.

End Notations.

#[global] Instance LessDefined_Tick {a} `{LessDefined a} : LessDefined (Tick a) :=
  fun x y => cost x <= cost y /\ val x `less_defined` val y.

#[global] Instance Transitive_LessDefined_Tick {a} `{LessDefined a}
  `{!Transitive (less_defined (a := a))} : Transitive (less_defined (a := Tick a)).
Proof.
  unfold Transitive, less_defined, LessDefined_Tick; intros * [] []; split; etransitivity; eauto.
Qed.

#[global] Instance Bottom_Tick {a} `{Bottom a} : Bottom (Tick a) := MkTick 0 bottom.

End Tick.
Notation Tick := Tick.Tick.

Import Tick.Notations.

(** * Demand *)

(* Lazy amortization works by hiding thunks "deep" in the data structure, so
   they cannot be forced immediately, only after performing operations whose
   cost is propoertional to the cost of the thunk.

   However, in the clairvoyance monad, we must decide whether to evaluate thunks
   right when they are constructed, so we have to predict the future to know
   whether it will be used.

   In other words, a user of the cost specification must first decide what the
   demand on the outputs will be. The demand will be modeled by an approximation
   value [T (QueueA a)].  The higher the demand, the higher the cost, which will
   be amortized since the only way to have high demand is to perform many
   operations in the future.  *)

(* Before modeling cost, we must model demand. The caller of a function makes a
   demand on its output, which the function translates to a demand on the
   inputs.

   We can thus define a function from output demands to input demands.

   These can also in principle be derived automatically from the initial
   implementation.  *)

(** ** Demand functions *)

(* A combinator for demand functions. If [f : a -> b] is a demand function
   with input [a], then [thunkD f : T a -> b] is a demand function with input [T
   a]. *)
Definition thunkD {a b} `{Bottom b} (f : a -> b) (x : T a) : b :=
  match x with
  | Undefined => bottom
  | Thunk x => f x
  end.

(* Demand function for [appendA]. Note that the output demand [outD] is at least
   either [NilA] or [ConsA] (i.e., it forces the result at least to WHNF).
   [thunkD] can then be used to lift the output demand type to thunks.  *)
Fixpoint appendD {a} (xs ys : list a) (outD : listA a) : Tick (T (listA a) * T (listA a)) :=
  Tick.tick >>
  match xs, outD with
  | [], _ => Tick.ret (Thunk NilA, Thunk outD)
  | x :: xs, ConsA zD zsD =>
    let+ (xsD, ysD) := thunkD (appendD xs ys) zsD in
    Tick.ret (Thunk (ConsA zD xsD), ysD)
  | _, _ => bottom (* Nonsense: if (xs = _ :: _) then append xs ys = (_ :: _)
                      so the demand cannot be of the form [] *)
  end.

(* Demand function for [revA].
   [revA] has to traverse the list: the input demand is the whole list.
   (Actually, a finer solution is to force only the spine, not the elements,
   since they are protected by [T], but, simplicity.) *)
Definition revD {a} (xs : list a) (outD : listA a) : Tick (T (listA a)) :=
  Tick.MkTick (1 + length xs) (exact xs).

(* [mkQueue] uses [rev] and [append], in this order ([append front (rev back)]),
   so we compute the demand in reverse. *)
Definition mkQueueD {a} (nfront : nat) (front : list a) (nback : nat) (back : list a)
    (outD : QueueA a) : Tick (T (listA a) * T (listA a)) :=
  Tick.tick >>
  if nfront <? nback then
    let+ (frontD, rbackD) := thunkD (appendD front (rev back)) (frontA outD) in
    let+ backD := thunkD (revD back) rbackD in
    Tick.ret (frontD, backD)
  else Tick.ret (frontA outD, backA outD).

Definition emptyX {a} : T (QueueA a) := Thunk (MkQueueA 0 (Thunk NilA) 0 (Thunk NilA)).

Definition tailX {a} (xs : T (listA a)) : T (listA a) :=
  match xs with
  | Thunk (ConsA _ xs) => xs
  | _ => Undefined
  end.

(* In [pushA], [q] is always forced, so the first component of the input demand
   is at least [Thunk]. *)
Definition pushD {a} (q : Queue a) (x : a) (outD : QueueA a) : Tick (T (QueueA a) * T a) :=
  Tick.tick >>
  let+ (frontD, backD) := mkQueueD (nfront q) (front q) (S (nback q)) (x :: back q) outD in
  Tick.ret (Thunk (MkQueueA (nfront q) frontD (nback q) (tailX backD)), Thunk x).

Definition popD {a} (q : Queue a) (outD : option (T a * T (QueueA a))) : Tick (T (QueueA a)) :=
  Tick.tick >>
  match front q, outD with
  | [], _ => Tick.ret (exact q)  (* The queue is empty so the "whole queue" must be a fixed value. *)
  | x :: f, Some (xA, pop_qA) =>
    let+ (fD, bD) := thunkD (mkQueueD (pred (nfront q)) f (nback q) (back q)) pop_qA in
    Tick.ret (Thunk (MkQueueA
      (nfront q)
      (Thunk (ConsA xA fD))
      (nback q)
      bD))
  | _, _ => bottom
  end.

(** ** Soundness of demand functions *)

(** *** Soundess of demand functions with respect to pure functions *)

(** A demand function [fD] must produce an approximation of the input
  of the corresponding pure function [f]. *)

(** These proofs should be automatable, the demand functions can be derived from the
  pure functions. *)

Lemma appendD_approx {a} (xs ys : list a) (outD : _)
  : outD `is_approx` append xs ys -> Tick.val (appendD xs ys outD) `is_approx` (xs, ys).
Proof.
  revert outD; induction xs; cbn.
  - intros; solve_approx.
  - autorewrite with exact; intros. inversion H; subst.
    inversion H4; subst; cbn.
    + constructor; cbn; constructor. autorewrite with exact. constructor; auto; constructor.
    + specialize (IHxs _ H2). inversion IHxs; subst.
      destruct (Tick.val _); cbn in *. solve_approx.
Qed.

Lemma revD_approx {a} (xs : list a) (outD : _)
  : Tick.val (revD xs outD) `is_approx` xs.
Proof.
  unfold revD. reflexivity.
Qed.

Lemma mkQueueD_approx {a} nf (f : list a) nb b (outD : QueueA a)
  : outD `is_approx` mkQueue nf f nb b ->
    Tick.val (mkQueueD nf f nb b outD) `is_approx` (f, b).
Proof.
  unfold mkQueue, mkQueueD.
  destruct (Nat.ltb_spec nf nb).
  - destruct (frontA outD) eqn:Ef; cbn.
    + destruct appendD eqn:Eapp. intros []; cbn in *.
      rewrite Ef in ld_front0; inversion ld_front0; subst.
      apply appendD_approx in H2. rewrite Eapp in H2. destruct H2, val; cbn in *.
      constructor; cbn; auto.
      inversion snd_rel; subst; cbn; [ constructor | reflexivity ].
    + do 2 constructor.
  - intros HH; constructor; apply HH.
Qed.

Lemma tailX_mon {a} (xs xs' : T (listA a))
  : xs `less_defined` xs' -> tailX xs `less_defined` tailX xs'.
Proof.
  destruct 1 as [ | ? ? [ | ] ]; cbn; auto.
Qed.

#[global] Instance Proper_tailX {a} : Proper (less_defined ==> less_defined) (@tailX a).
Proof. exact (@tailX_mon a). Qed.

Lemma pushD_approx {a} (q : Queue a) (x : a) (outD : QueueA a)
  : outD `is_approx` push q x -> Tick.val (pushD q x outD) `is_approx` (q, x).
Proof.
  unfold push, pushD.
  intros Hout. unfold pushD.
  destruct mkQueueD as [ Qcost [] ] eqn:HQ.
  apply mkQueueD_approx in Hout. rewrite HQ in Hout.
  destruct Hout as [Hout1 Hout2]; cbn in Hout1, Hout2.
  apply tailX_mon in Hout2.
  solve_approx.
Qed.

Lemma popD_approx {a} (q : Queue a) (outD : _)
  : outD `is_approx` pop q -> Tick.val (popD q outD) `is_approx` q.
Proof.
  unfold pop, popD. destruct (front _) eqn:Ef; cbn; inversion 1; subst.
  - reflexivity.
  - destruct x; destruct H2; cbn in *.
    inversion snd_rel; subst; cbn [Tick.val thunkD bottom Tick.Bottom_Tick Bottom_prod Tick.ret].
    + solve_approx. rewrite Ef. solve_approx.
    + apply mkQueueD_approx in H2. destruct mkQueueD eqn:Em.
      destruct H2, val; cbn in *. solve_approx. rewrite Ef. solve_approx.
Qed.

Lemma popD_approx_Some {a} (q q' : Queue a) x (outD : _)
  : pop q = Some (x, q') -> outD `is_approx` (x, q') -> Tick.val (popD q (Some outD)) `is_approx` q.
Proof.
  intros Hpop Hout; apply popD_approx. rewrite Hpop. constructor. apply Hout.
Qed.

Lemma appendD_size {a} (xs ys : list a) (outD : _)
  : outD `is_approx` append xs ys ->
    let xy := Tick.val (appendD xs ys outD) in
    sizeX' 0 outD = sizeX (sizeX 0 (snd xy)) (fst xy).
Proof.
  revert outD; induction xs; cbn; intros; [ reflexivity | ].
  destruct outD as [ | ? [] ]; cbn; [ reflexivity | | reflexivity ].
  rewrite IHxs.
  - destruct appendD as [ ? [ [] ? ] ] eqn:E; cbn; reflexivity.
  - inversion H; subst. inversion H5; subst. auto.
Qed.

Lemma appendD_Thunk_r {a} (xs ys : list a) (outD : _)
  : outD `is_approx` append xs ys ->
    forall xsA ysA, (xsA, Thunk ysA) = Tick.val (appendD xs ys outD) ->
    sizeX 0 xsA = length xs.
Proof.
  revert outD; induction xs; cbn; intros outD Hout xsA ysA H.
  - inversion H; reflexivity.
  - inversion Hout; subst.
    inversion H4; subst; cbn in H.
    + inversion H.
    + destruct appendD as [ ? [] ] eqn:ED in H; inversion H; subst; cbn.
      erewrite <- IHxs by (try rewrite ED; cbn; eauto).
      destruct t as [ xs' | ]; reflexivity.
Qed.

(** *** Soundness of demand functions with respect to clairvoyant functions. *)

(** Given the output demand, we compute the input demand, and we expect that
    running the function on those input demands will (optimistically) yield a
    result at least as defined as the output demand. *)

(** These are subsumed by the [_cost] lemmas. *)

(** [revA] has a simple cost specification: it will have to traverse the list in any case,
  so we might as well keep the whole result. *)

Lemma revD_cost {a} (xs : list a) outD : Tick.cost (revD xs outD) = 1 + length xs.
Proof. reflexivity. Qed.

Lemma revA__cost {a} (xs ys : list a)
  : revA_ (exact xs) (exact ys) [[ fun out cost =>
      out = exact (rev_append xs ys) /\ cost = 1 + length xs ]].
Proof.
  revert ys; induction xs; [ rewrite exact_list_unfold_nil | rewrite exact_list_unfold_cons ];
    intros; mgo'.
  apply optimistic_thunk_go; mgo'.
  specialize (IHxs (a0 :: ys)). unfold exact at 2, Exact_T in IHxs.
  rewrite exact_list_unfold_cons in IHxs.
  relax; [ exact IHxs | ]. cbn; intros * [ ? -> ]; split; [auto | lia].
Qed.

Lemma revA_cost {a} (xs : list a)
  : revA (exact xs) [[ fun out cost =>
      out = exact (rev xs) /\ cost = 1 + length xs ]].
Proof.
  unfold revA; mgo'. apply optimistic_thunk_go; mgo'. rewrite rev_alt. apply (revA__cost xs nil).
Qed.

(* This proof for [revD] is backwards (we prove [revA_cost] first, whereas for other
   functions we use the [*D_spec] lemma to prove [*A_cost]), because we took
   a shortcut in the definition of [revD]. *)
Lemma revD_spec {a} (xs : list a) (outD : listA a)
  : outD `is_approx` rev xs ->
    forall xsD dcost, Tick.MkTick dcost xsD = revD xs outD ->
    revA xsD [[ fun out cost => outD `less_defined` out /\ cost <= dcost ]].
Proof.
  intros Hout *; inversion 1; subst. relax; [ apply revA_cost | cbn; intros * []; subst ].
  split; [ assumption | reflexivity ].
Qed.

Lemma appendD_spec {a} (xs ys : list a) (outD : listA a)
  : outD `is_approx` append xs ys ->
    forall xsD ysD dcost, Tick.MkTick dcost (xsD, ysD) = appendD xs ys outD ->
    appendA xsD ysD [[ fun out cost => outD `less_defined` out /\ cost <= dcost ]].
Proof.
  revert outD; induction xs; cbn; intros * Hout *.
  - inversion 1; subst; cbn; mgo_; split; reflexivity.
  - autorewrite with exact in Hout. inv Hout. destruct thunkD as [ ? [] ] eqn:Eth; cbn.
    inversion 1; subst; cbn. mgo_. inv H3; cbn in Eth; inv Eth.
    + apply optimistic_skip. mgo_. split; reflexivity.
    + apply optimistic_thunk_go. relax_apply IHxs; [ try rewrite H1; eauto .. | cbn; intros * [] ].
      mgo_. split; [solve_approx | ]. lia.
Qed.

Lemma appendD_spec' {a} (xs ys : list a) (outD : listA a)
  : outD `is_approx` append xs ys ->
    forall xsD ysD dcost, Tick.MkTick dcost (xsD, ysD) = appendD xs ys outD ->
    forall xsD' ysD', xsD `less_defined` xsD' -> ysD `less_defined` ysD' ->
    appendA xsD' ysD' [[ fun out cost => outD `less_defined` out /\ cost <= dcost ]].
Proof.
  intros; eapply optimistic_corelax.
  - eapply appendA_mon; eassumption.
  - apply uc_cost.
  - eapply appendD_spec; eassumption.
Qed.

Lemma mkQueueD_spec {a} nf f nb b (outD : QueueA a)
  : outD `is_approx` mkQueue nf f nb b ->
    forall fD bD dcost, Tick.MkTick dcost (fD, bD) = mkQueueD nf f nb b outD ->
    mkQueueA nf fD nb bD [[ fun out cost => outD `less_defined` out /\ cost <= dcost ]].
Proof.
  unfold mkQueue, mkQueueD, mkQueueA.
  intros Hout fa bA dcost HQ.
  destruct (Nat.ltb_spec nf nb).
  - mgo_. destruct thunkD as [ cc [f0 b0] ] eqn:ED; cbn in *; inv HQ.
    destruct b0; cbn.
    + apply optimistic_thunk_go. destruct (frontA _) eqn:Ef in ED; cbn in ED; [ | inv ED ].
      inv Hout; cbn in *. rewrite Ef in ld_front0. inv ld_front0.
      assert (Happ := appendD_approx H2). rewrite ED in Happ. destruct Happ; cbn in *. inv snd_rel.
      relax; [ eapply revA_cost | cbn; intros * []; subst; mgo_ ].
      apply optimistic_thunk_go. relax.
      { eapply appendD_spec'; try eassumption.
        - rewrite ED. reflexivity.  - reflexivity.  - constructor; assumption. }
      cbn; intros * []. mgo_.
      split.
      * constructor; cbn; try assumption. rewrite Ef; auto.
      * lia.
    + apply optimistic_skip. mgo_. inv Hout; cbn in *. destruct (frontA _) eqn:Ef; inv ld_front0; cbn in ED.
      * apply optimistic_thunk_go.
        relax; [ eapply appendD_spec'; eassumption + (try rewrite ED; reflexivity) | ].
        cbn; intros * []; mgo_.
        split; [ constructor; cbn; try assumption | lia].
        rewrite Ef; auto.
      * apply optimistic_skip. mgo_. split; [constructor; cbn; try assumption | lia ].
        rewrite Ef; reflexivity.
  - mgo_. inv HQ. split; [ constructor; cbn; apply Hout + reflexivity | reflexivity ].
Qed.

Lemma mkQueueD_spec' {a} nf f nb b (outD : QueueA a)
  : outD `is_approx` mkQueue nf f nb b ->
    forall fD bD dcost, Tick.MkTick dcost (fD, bD) = mkQueueD nf f nb b outD ->
    forall fD' bD', fD `less_defined` fD' -> bD `less_defined` bD' ->
    mkQueueA nf fD' nb bD' [[ fun out cost => outD `less_defined` out /\ cost <= dcost ]].
Proof.
  intros. eapply optimistic_corelax.
  - eapply mkQueueA_mon; eassumption + reflexivity.
  - apply uc_cost.
  - eapply mkQueueD_spec; try eassumption.
Qed.

Arguments mkQueueD : simpl never.

Lemma less_defined_tail_cons {a} (l : T (listA a)) x xs
  : l `less_defined` Thunk (ConsA x xs) ->
    l `less_defined` Thunk (ConsA x (tailX l)).
Proof.
  inversion 1; subst; constructor. inversion H2; constructor; cbn; [ auto | reflexivity ].
Qed.

Lemma pushD_spec {a} (q : Queue a) (x : a) (outD : QueueA a)
  : outD `is_approx` push q x ->
    forall qD xD, (qD, xD) = Tick.val (pushD q x outD) ->
    let dcost := Tick.cost (pushD q x outD) in
    pushA qD xD [[ fun out cost => outD `less_defined` out /\ cost <= dcost ]].
Proof.
  unfold push, pushD, pushA; cbn beta iota.
  intros Hout * Hval. destruct mkQueueD as [? [] ] eqn:EQ in Hval; cbn in Hval. inv Hval. mgo_.
  relax.
  { eapply mkQueueD_spec'.
    - eassumption.
    - rewrite EQ; reflexivity.
    - reflexivity.
    - eapply less_defined_tail_cons. eapply mkQueueD_approx in Hout. rewrite EQ in Hout.
      cbn in Hout. destruct Hout as [_ Hout]. cbn in Hout. autorewrite with exact in Hout.
      exact Hout. }
  cbn; intros * []. split; [auto |].
  rewrite EQ in *; cbn in *; lia.
Qed.

Lemma popD_spec {a} (q : Queue a) (outD : option (T a * T (QueueA a)))
  : outD `is_approx` pop q ->
    forall qD, qD = Tick.val (popD q outD) ->
    let dcost := Tick.cost (popD q outD) in
    popA qD [[ fun out cost => outD `less_defined` out /\ cost <= dcost ]].
Proof.
  unfold pop, popD, popA.
  intros Hout * ->. destruct (front q) eqn:Ef.
  - cbn. mgo_. rewrite Ef. autorewrite with exact. mgo_.
  - mgo_. inversion Hout; subst. destruct H1 as [Hfst Hsnd]; destruct x as [x' q']; cbn in *.
    destruct thunkD as [? [] ] eqn:ED. cbn. mgo_.
    inversion Hsnd; subst; cbn in *.
    + apply optimistic_skip. mgo_; cbn [thunkD bottom Bottom_T].
      split; [ reflexivity | ]. inversion ED; subst. reflexivity.
    + apply optimistic_thunk_go; cbn.
      relax.
      { eapply mkQueueD_spec.
        - eassumption.
        - rewrite ED; reflexivity. }
      cbn; intros * []. mgo_.
      split; [ solve_approx | lia ].
Qed.

(** * Lazy Physicist's method *)

(** Unlike a regular physicist, the lazy physicist defines potential only over
  the fragment of the data structure that will be needed, which we have
  represented as the "demand". *)

(** The potential should be thought of as "negative potential", or "debt".  When
  an expensive operation occurs, this consumes potential energy/creates debt,
  which must be recovered in the future. *)

(** This works in reverse from the classical physicist's method.

    ** Classical physicist

    Potential is accumulated before it is spent.

    ** Lazy physicist

    Negative potential can be spent whenever (there is no lower bound), but it
    must eventually be recovered. We do not spend potential/debt we do not plan
    to pay back, which we can "predict" in our clairvoyant framework. *)

Class Debitable a : Type :=
  debt : a -> nat.

#[global] Instance Debitable_T {a} `{Debitable a} : Debitable (T a) :=
  fun x =>
    match x with
    | Undefined => 0
    | Thunk x => debt x
    end.

#[global] Instance Debitable_QueueA {a} : Debitable (QueueA a) :=
  fun qA => 2 * sizeX 0 (frontA qA) - 2 * nbackA qA.

Arguments Debitable_QueueA {a} qA /.

(* Ad hoc overloading of [debt] on the output of [pop]. *)
#[local] Instance Debitable_popo {a} : Debitable (option (T a * T (QueueA a))) :=
  fun x =>
    match x with
    | None => 0
    | Some (_, qA) => debt qA
    end.

(* Here, the debt must decrease constantly when we pop elements from the front
   or when we push elements to the back. When the two queues are of equal
   length, the debt is zero, and we are free to increase it again.  A
   reverse-and-append costs (length (front q) + length (back q) = 2 * length
   (front q)), because the two lists have the same length.  But because the
   [reverse], unlike [append], cannot be done incrementally, we must frontload
   those debits on the first half of the list, hence the factor [2] in [debt].

   But we might not need the whole output, in which case we can drop the debits
   for thunks that won't be reached. This is why the debt is a function of the
   demand, rather than the complete output, and we look at the partial length
   ([sizeX]) of [frontA] instead of reading the exact length in [nfrontA].  *)

(* TODO: can you increase the debt if it is not yet zero? In Okasaki, no, and
   that's why the Banker's method is more general. But this seems different. As
   long as your final demand (at the end of all operations) has debt 0, you can
   do anything. *)

(** * Amortized cost specifications (and proofs) *)

(* The two main theorems to prove are [pushA_cost] and [popA_cost].
   We then generalize them by monotonicity into [pushA_cost'] and [popA_cost'],
   where the input doesn't have to be exactly equal to the input demand. *)

Opaque Nat.mul Nat.add Nat.sub.

(** ** Cost specs for auxiliary functions *)

(** [appendA] is our first example where the notion of demand is relevant
  (so this differs from the spec from our initial paper).

  1. The caller (user of this theorem) must specify a demand [outD] on the
     output (first condition: [outD] must be an approximation of the pure
     output [append xs ys]).
  2. This corresponds to an input demand [(xsA, ysA)], via the demand
     function [appendD].
  3. When that input demand is met (i.e., we use [xsA] and [ysA] as the inputs
     of [appendA]), we can satisfy the output demand: we can (optimistically)
     produce an output [out] at least as defined as [outD] in time bounded
     by some function of the output demand (here it is a function of the input
     demand, which is itself a function of the output demand). *)

Lemma appendD_cost {a} (xs ys : list a) outD
  : outD `is_approx` append xs ys ->
    forall xsA, xsA = fst (Tick.val (appendD xs ys outD)) ->
    Tick.cost (appendD xs ys outD) = sizeX 1 xsA.
Proof.
  revert outD; induction xs; cbn; intros * Hout * ->; [ reflexivity | ].
  autorewrite with exact in Hout. inv Hout. inv H3; cbn; [ lia | ].
  erewrite IHxs by eauto. destruct (Tick.val _) as [ [] ? ]; cbn; lia.
Qed.

Lemma appendA_cost {a} (xs ys : list a) outD
  : outD `is_approx` append xs ys ->
    forall xsA ysA, (xsA, ysA) = Tick.val (appendD xs ys outD) ->
    appendA xsA ysA [[ fun out cost =>
      outD `less_defined` out /\ cost <= sizeX 1 xsA ]].
Proof.
  intros. destruct appendD as [ ? [] ] eqn:ED; inv H0.
  relax; [ eapply appendD_spec; eassumption + rewrite ED; reflexivity | cbn; intros * [] ].
  split; [ auto | ]. rewrite H1.
  replace cost with (Tick.cost (appendD xs ys outD)) by (rewrite ED; reflexivity).
  apply Nat.eq_le_incl, appendD_cost; [ assumption | rewrite ED; reflexivity ].
Qed.

(** We can then generalize that theorem: the postcondition can be satisfied
  as long as the input [(xsA',ysA')] is at least as defined as the input demand
  [(xsA,ysA)]. This is a straightforward consequence of [appendA]'s monotonicity
  proved earlier. *)

(** Relaxed cost specification *)
Lemma appendA_cost' {a} (xs ys : list a) outD
  : outD `is_approx` append xs ys ->
    forall xsA ysA, (xsA, ysA) = Tick.val (appendD xs ys outD) ->
    forall xsA' ysA', xsA `less_defined` xsA' -> ysA `less_defined` ysA' ->
    appendA xsA' ysA' [[ fun out cost =>
      outD `less_defined` out /\ cost <= sizeX 1 xsA ]].
Proof.
  intros. eapply optimistic_corelax.
  - eapply appendA_mon; eassumption.
  - apply uc_cost.
  - eauto using appendA_cost.
Qed.

(** Below are similar cost specifications for the queue methods [pushA] and
    [popA], both relying on a cost specification for [mkQueueA]. These are
    _amortized cost specifications_: the potential function on the input and
    output demands adds extra terms in the cost inequality.

[[ debt inD + cost <= C + debt outD ]]

  for some constant [C]. This is of course equivalent to [cost <= c + debt outD -
  debt inD], but only doing arithmetic in [nat].

  Starting from the empty queue (with debt 0), we can add the costs of a
  sequence of operations

[[ TOTALCOST = debt emptyX + cost1 + cost2 + ... + costn ]]

  if we call [q1] the queue after the first operation, its amortized cost
  specification provides the following inequality:

[[ debt emptyX + cost1 <= C + debt q1 ]]

  We can bound the above sum by:

[[ TOTALCOST <= C + debt q1 + cost2 + cost3 + ... + costn ]]

  And so on.

[[ TOTALCOST <= C + C + debt q2 + cost3 + ... + costn ]]
[[ TOTALCOST <= C + C + C + debt q3 + ... + costn ]]
[[ ... ]]
[[ TOTALCOST <= C + C + C + ... + C + debt qn ]]

  If we make the final demand empty (bottom/undefined), the last term becomes
  [debt qn = debt _|_ = 0]. Therefore, the final cost is [n * C], for a constant
  [C]. This is [O(n)]. So the average cost of each operation is [C].  *)

(* Auxiliary *)
Lemma size_approx {a} (xs : list a) (xsA : T (listA a))
  : xsA `is_approx` xs -> sizeX 0 xsA <= length xs.
Proof.
  revert xsA; induction xs; intros *; inversion 1; subst; cbn; try lia.
  - inversion H2; cbn; lia.
  - inversion H2; subst; cbn. inversion H5; subst; cbn. lia.
    apply le_n_S. eapply (IHxs (Thunk x)); auto.
Qed.

(* Auxiliary *)
Lemma sizeX_up {a} (xs : T (listA a)) n : sizeX n xs <= sizeX 0 xs + n.
Proof.
  destruct xs as [ xs | ]; cbn; [ | lia ].
  induction xs; cbn; lia.
Qed.

(* Auxiliary *)
Lemma sizeX_down {a} (xs : T (listA a)) n : sizeX 0 xs <= sizeX n xs.
Proof.
  destruct xs as [ xs | ]; cbn; [ | lia ].
  induction xs; cbn; lia.
Qed.

(** Cost specification for [mkQueueD] *)
Lemma mkQueueD_cost {a} (nf : nat) (f : list a) (nb : nat) (b : list a) (outD : QueueA a)
  : nf = length f /\ nb = length b /\ nb <= nf + 1 -> outD `is_approx` mkQueue nf f nb b ->
    forall fA bA cost, Tick.MkTick cost (fA, bA) = mkQueueD nf f nb b outD ->
    2 * sizeX 0 fA - 2 * nb + cost <= 4 + debt outD.
Proof.
  unfold mkQueue, mkQueueD.
  intros (Hf & Hb & Hbf) Hout fa bA c HQ.
  destruct (Nat.ltb_spec nf nb).
  - destruct thunkD as [ cc [f0 b0] ] eqn:ED; cbn in *; inv HQ.
    destruct b0; cbn.
    + destruct (frontA _) eqn:Ef in ED; cbn in ED; [ | inv ED ].
      inversion Hout; cbn in *. rewrite Ef in ld_front0. inv ld_front0.
      assert (APX := appendD_approx H2).
      rewrite ED in APX; cbn in APX. destruct APX as [APX1 APX2]; cbn in *; inv APX2.
      replace cc with (sizeX 1 f0).
      2:{ eapply appendD_cost in H2; [ | rewrite ED; reflexivity ].
        rewrite ED in H2; cbn in H2. auto. }
      unfold debt, Debitable_QueueA.
      rewrite (size_approx (xs := f)) by assumption.
      rewrite Ef. cbn. erewrite appendD_size by eauto.
      rewrite ED; cbn.
      rewrite <- (sizeX_down _ (sizeX' _ _)).
      rewrite sizeX_up.
      rewrite ld_nback0.
      assert (sizeX 0 f0 = length f).
      { eapply appendD_Thunk_r; [ eauto | rewrite ED; reflexivity]. }
      lia.
    + inv Hout; cbn in *.
      destruct (frontA _) eqn:Ef in *; cbn in ED.
      * inv ld_front0.
        replace cc with (sizeX 1 f0).
      2:{ eapply appendD_cost in H2; [ | rewrite ED; reflexivity ].
        rewrite ED in H2; cbn in H2. auto. }
        unfold debt, Debitable_QueueA.
        rewrite ld_nback0. rewrite Ef; cbn; erewrite appendD_size by eauto.
        rewrite ED; cbn. rewrite (sizeX_up _ 1).
        assert (sizeX 0 f0 <= length f).
        { apply size_approx. apply appendD_approx in H2.
          rewrite ED in H2. apply H2. }
        lia.
      * inversion ED; subst; cbn. lia.
  - unfold debt, Debitable_QueueA.
    inversion HQ; subst.
    inversion Hout; cbn in *. lia.
Qed.

Lemma pushD_cost {a} (q : Queue a) (x : a) (outD : QueueA a)
  : well_formed q ->
    outD `is_approx` push q x ->
    forall qA xA, (qA, xA) = Tick.val (pushD q x outD) ->
    let cost := Tick.cost (pushD q x outD) in
    debt qA + cost <= 7 + debt outD.
Proof.
  intros Wq Hout; unfold pushA, pushD. intros. repeat (mforward idtac).
  destruct mkQueueD as [ ? [] ] eqn:Em; inv H; cbn.
  symmetry in Em; apply mkQueueD_cost in Em; cbn; auto.
  2:{ split; [ apply Wq | ].
      split; [ f_equal; apply Wq | ].
      rewrite Nat.add_1_r; rewrite <- Nat.succ_le_mono. apply Wq. }
  unfold debt at 1; cbn. lia.
Qed.

(** Cost specification for [pushA] *)
Lemma pushA_cost {a} (q : Queue a) (x : a) (outD : QueueA a)
  : well_formed q ->
    outD `is_approx` push q x ->
    forall qA xA, (qA, xA) = Tick.val (pushD q x outD) ->
    pushA qA xA [[ fun out cost =>
      outD `less_defined` out /\ debt qA + cost <= 7 + debt outD ]].
Proof.
  intros; relax; [ eapply pushD_spec; eauto | cbn beta ].
  intros * []; split; [ auto | ]. apply pushD_cost in H1; auto.
  lia.
Qed.

(** Relaxed cost specification *)
(* Note that there are two ways from [pushD_spec] (above) to [pushA_cost'] (below),
   by commuting the two steps (here done in order "1 then 2"):
   (1) transform [pushD]'s specification ([pushD_spec]) into [pushA]'s cost
   specification ([pushA_cost]) (left-right arrows);
   (2) relax the specification by monotonicity (up-down arrows).

   [[
   pushD_spec   --(pushD_cost)-->  pushA_cost
       |                               |
       | pushA_mon                     | pushA_mon
       v                               v
   pushD_spec'  --(pushD_cost)-->  pushA_cost'
   ]] *)
Lemma pushA_cost' {a} (q : Queue a) (x : a) (outD : QueueA a)
  : well_formed q ->
    outD `is_approx` push q x ->
    forall qA xA, (qA, xA) = Tick.val (pushD q x outD) ->
    forall qA', qA `less_defined` qA' ->
    pushA qA' xA [[ fun out cost =>
      outD `less_defined` out /\ debt qA + cost <= 7 + debt outD ]].
Proof.
  intros. eapply optimistic_corelax.
  - eapply pushA_mon. eassumption. reflexivity.
  - apply uc_acost.
  - eapply pushA_cost; eassumption.
Qed.

Lemma popD_cost {a} (q : Queue a) (outD : option (T a * T (QueueA a)))
  : well_formed q ->
    outD `is_approx` pop q ->
    let qA := Tick.val (popD q outD) in
    let cost := Tick.cost (popD q outD) in
    debt qA + cost <= 7 + debt outD.
Proof.
  unfold pop, popD. intros Wq Hout. cbn.
  destruct (front q) eqn:Ef; cbn.
  - let q' := eval unfold exact, Exact_Queue in (exact q) in change (exact q) with q'.
    rewrite Ef. autorewrite with exact.
    unfold debt, Debitable_QueueA; cbn. lia.
  - inv Hout. destruct H1 as [Hfst Hsnd]; destruct x as [x' q']; cbn in *.
    destruct thunkD as [ ? [] ] eqn:EmkQ. cbn.
    inv Hsnd; subst; cbn in *.
    + inv EmkQ; subst; cbn. unfold debt, Debitable_QueueA. cbn. lia.
    + assert (HQ := @mkQueueD_cost _ (pred (nfront q)) l (nback q) (back q) x).
      eassert (HQH : _); [ | specialize (HQ HQH H1 _ _ _ (eq_sym EmkQ)) ].
      { destruct Wq. rewrite Ef in *; cbn in *. lia. }
      unfold debt at 1, Debitable_QueueA at 1; cbn.
      destruct t; cbn in *; try lia.
Qed.

(** Cost specification for [popA] *)
Lemma popA_cost {a} (q : Queue a) (outD : option (T a * T (QueueA a)))
  : well_formed q ->
    outD `is_approx` pop q ->
    let qA := Tick.val (popD q outD) in
    popA qA [[ fun out cost =>
      outD `less_defined` out /\ debt qA + cost <= 7 + debt outD ]].
Proof.
  intros; relax; [ eapply popD_spec; eauto | cbn beta ].
  intros * []; split; [ auto | ]. apply popD_cost in H0; auto.
  fold qA in H0. lia.
Qed.

(** Relaxed cost specification *)
Lemma popA_cost' {a} (q : Queue a) (outD : option (T a * T (QueueA a)))
  : well_formed q ->
    outD `is_approx` pop q ->
    let qA := Tick.val (popD q outD) in
    forall qA', qA `less_defined` qA' ->
    popA qA' [[ fun out cost =>
      outD `less_defined` out /\ debt qA + cost <= 7 + debt outD ]].
Proof.
  intros.
  eapply optimistic_corelax.
  - eapply popA_mon. eassumption.
  - apply uc_acost.
  - apply popA_cost; assumption.
Qed.

(** * Validation for persistence *)

(* We want to be able to prove that in any usage of this queue, operations have
   amortized constant cost. We represent "usage" as a tree of operations, where
   branching is sharing. *)

Inductive tree a : Type :=
| Push : a -> tree a -> tree a
| Pop : tree a -> tree a
| Share : tree a -> tree a -> tree a
| Done : tree a
.

Fixpoint run_tree {a} (t : tree a) (q : T (QueueA a)) : M (list (T a)) :=
  match t with
  | Push x t =>
    let~ q := pushA q (Thunk x) in
    run_tree t q
  | Pop t =>
    let! o := popA q in
    match o with
    | None => ret []
    | Some (x, q) =>
      let! xs := run_tree t q in
      ret (x :: xs)
    end
  | Share t1 t2 =>
    let! r1 := run_tree t1 q in
    let! r2 := run_tree t2 q in
    ret (r1 ++ r2)
  | Done => ret []
  end.

(* Then the cost of that computation must be bounded by the size of the tree
   (the number of operations it contains) within some multiplicative factor. *)

Fixpoint size_tree {a} (t : tree a) : nat :=
  match t with
  | Push _ t => 1 + size_tree t
  | Pop t => 1 + size_tree t
  | Share t1 t2 => size_tree t1 + size_tree t2
  | Done => 0
  end.

(* This queue's operations have amortized constant cost. *)
Definition GOOD_QUEUE : Prop :=
  forall a (t : tree a),
    (let~ _empty := emptyA in
     run_tree t _empty) [[ fun _ n => n <= 7 * size_tree t ]].

(* The proof: we first compute the demand. *)


Class LubDebt a `{LessDefined a, Lub a, Debitable a} : Prop :=
  lub_debt : forall x y : a, cobounded x y -> debt (lub x y) <= debt x + debt y.

Arguments LubDebt : clear implicits.
Arguments LubDebt a {_ _ _}.

#[global] Instance LubDebt_T {a} `{LubDebt a} : LubDebt (T a).
Proof.
  intros [x |] [y |] [z [Hx Hy] ]; cbn; [ | lia .. ].
  apply H2. inversion Hx; subst; inversion Hy; subst. eexists; split; eassumption.
Qed.

Lemma sizeX'_lub {a} (x y : listA a) : sizeX' 0 (lub x y) <= max (sizeX' 0 x) (sizeX' 0 y).
Proof.
  revert y; induction x as [ | | ]; intros [ | y [ ys | ] ]; cbn; auto; try lia.
  specialize (IHx ys). lia.
Qed.

Lemma sizeX_lub {a} (x y : T (listA a)) : sizeX 0 (lub x y) <= max (sizeX 0 x) (sizeX 0 y).
Proof.
  destruct x, y; cbn; try lia; apply sizeX'_lub.
Qed.

#[global] Instance LubDebt_QueueA {a} : LubDebt (QueueA a).
Proof.
  intros q1 q2 [q3 [ [] [] ] ]; cbn.
  unfold debt, Debitable_QueueA; cbn.
  repeat match goal with
  | H : _ = _ |- _ => rewrite H
  end. rewrite !sizeX_lub. lia.
Qed.

Arguments popD : simpl never.
Arguments pushD : simpl never.

Fixpoint demand_tree {a} (t : tree a) (q : Queue a) : T (QueueA a) :=
   match t with
   | Push x t =>
     let d := demand_tree t (push q x) in
     fst (Tick.val (thunkD (pushD q x) d))
   | Pop t =>
     match pop q with
     | None => exact q
     | Some (x, q') =>
       let d := demand_tree t q' in
       Tick.val (popD q (Some (Thunk x, d)))
     end
   | Share t1 t2 => lub (demand_tree t1 q) (demand_tree t2 q)
   | Done => bottom
   end.

#[global]
Instance Proper_fst_less_defined {a b} `{LessDefined a,LessDefined b}
  : Proper (less_defined ==> less_defined) (@fst a b).
Proof.
  intros ? ? [H1 ?]; exact H1.
Qed.

Lemma demand_tree_approx {a} (t : tree a) q
  : demand_tree t q `is_approx` q.
Proof.
  revert q; induction t; cbn; intros.
  - specialize (IHt (push q a0)).
    inversion IHt; cbn.
    + apply bottom_least.
    + apply pushD_approx in H1. apply Proper_fst_less_defined in H1. apply H1.
  - destruct (pop q) as [ [] | ] eqn:Hpop; [ | reflexivity ].
    + apply (popD_approx_Some Hpop). constructor; cbn; [ constructor; reflexivity | apply IHt ].
  - apply lub_least_upper_bound; auto.
  - apply bottom_least.
Qed.

Lemma cobounded_demand_tree {a} (t1 t2 : tree a) q
  : cobounded (demand_tree t1 q) (demand_tree t2 q).
Proof.
  exists (exact q); split; apply demand_tree_approx.
Qed.

Lemma pop_popD {a} (q : Queue a)
  : pop q = None -> Tick.val (popD q None) = exact q.
Proof.
  unfold pop, popD. destruct (front q); [reflexivity | discriminate].
Qed.

(* The core lemma where the action happens *)
Lemma run_tree_cost {a} (t : tree a) (q : Queue a) (qA : T (QueueA a))
  : well_formed q ->
    demand_tree t q `less_defined` qA ->
    run_tree t qA [[ fun _ n => debt (demand_tree t q) + n <= 7 * size_tree t ]].
Proof.
  revert q qA; induction t; cbn; intros q qA wf_q ld_q.
  - mgo'. assert (WF := well_formed_push a0 wf_q).
    destruct (demand_tree t (push q a0)) as [ q' | ] eqn:Eq'; cbn in *.
    { apply optimistic_thunk_go.
      destruct (pushD q a0 q') as [ccp [xD qD] ] eqn:Epush; cbn in *.
      assert (Hq' : q' `is_approx` push q a0).
      { apply less_defined_Thunk_inv. rewrite <- Eq'. apply demand_tree_approx. }
      assert (PUSH := pushA_cost' a0 wf_q Hq' (f_equal Tick.val (eq_sym Epush)) ld_q).
      assert (qD = Thunk a0).
      { unfold pushD in Epush. destruct mkQueueD as [ ? [] ] in Epush. inv Epush. reflexivity. }
      subst. relax. { exact PUSH. }
      cbn; intros * []. relax. { apply (IHt _ _ WF). rewrite Eq'. constructor. assumption. }
      cbn; intros. rewrite Eq' in H1. cbn in H1. lia. }
    { apply optimistic_skip. relax. { apply (IHt _ _ WF). rewrite Eq'. constructor. }
      cbn; intros. lia. }
  - mgo'. assert (WF := fun x q' => well_formed_pop (x := x) (q' := q') wf_q). relax.
    { eapply @popA_cost' with (outD :=
        match pop q with Some (x, q') => Some (Thunk x, demand_tree t q') | None => None end).
      { eassumption. }
      { destruct (pop q) as [ [? ?] | ] eqn:Ep.
        - constructor. constructor; cbn.
          + constructor. hnf. reflexivity.
          + apply demand_tree_approx.
        - constructor. }
      destruct (pop q) as [ [? ?] | ] eqn:Ep; [ specialize (WF _ _ eq_refl) | ].
      - assumption.
      - rewrite (pop_popD Ep). assumption.
    }
    cbn; intros ? ? [ld_ COST].
    destruct (pop q) as [ [? ?] | ] eqn:Ep.
    { inversion ld_; subst. destruct y; destruct H0; cbn in *. apply optimistic_bind.
      relax.
      { eapply IHt. { apply (well_formed_pop wf_q Ep). }
        assumption. }
      cbn; intros. apply optimistic_ret. lia. }
    { inversion ld_. mforward idtac. rewrite (pop_popD Ep) in COST.
      change (Exact_Queue q) with (exact q). cbn in COST |- *. lia. }
  - apply lub_inv in ld_q; [ | apply cobounded_demand_tree ].
    mgo'. relax. { apply IHt1; [apply wf_q | apply ld_q]. }
    cbn; intros; mgo'. relax. { apply IHt2; [apply wf_q | apply ld_q]. }
    cbn; intros; mgo'. rewrite lub_debt by apply cobounded_demand_tree. lia.
  - mgo'.
Qed.

Theorem good_queue : GOOD_QUEUE.
Proof.
  intros a t.
  mgo'.
  apply optimistic_thunk_go.
  unfold emptyA.
  mgo'.
  relax.
  - apply run_tree_cost; [ apply well_formed_empty | apply (demand_tree_approx t (q := empty)) ].
  - intros. cbn in H. lia.
Qed.

(* Print Assumptions good_queue. *)
