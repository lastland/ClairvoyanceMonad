(* Overview

KNOWN
- Pure implementation of lazy queues: [Queue], [empty], [push], [pop]
- Clairvoyant-monadic implementation: [QueueA], [emptyA], [pushA], [popA]

NEW
- Demand functions: [emptyA'], [pushD], [popD]
- (Physicist's method) Debt/negative potential: [debt]
- Amortized cost specifications: [pushA_cost], [popA_cost]
- Trees ("API traces" with sharing): [tree], [run_tree]
- Final theorem (statement and proof):
    the cost of executing a tree with [n] operations is [O(n)]
    ([good_queue : GOOD_QUEUE : Prop])

*)

From Coq Require Import Arith List Lia Setoid Morphisms.
Import ListNotations.
From Clairvoyance Require Import Core Approx List Misc.

Import RevCompare.

Set Implicit Arguments.
Set Contextual Implicit.
Set Maximal Implicit Insertion.

#[local] Existing Instance Exact_id | 1.
#[local] Existing Instance LessDefined_id | 100.
#[local] Existing Instance LessDefinedOrder_id | 100.
#[local] Existing Instance LessDefinedExact_id | 100.

(* Lazy persistent queue *)
(* Amortized O(1) push and pop with persistence *)
(* Consider arithmetic on [nat] is O(1) *)

(* Pure implementation *)

Record Queue (a : Type) : Type := MkQueue
  { nfront : nat
  ; front : list a
  ; nback : nat
  ; back : list a
  }.

Definition mkQueue {a} (fn : nat) (f : list a) (bn : nat) (b : list a) : Queue a :=
  if fn <? bn then {| nfront := fn + bn ; front := f ++ rev b ; nback := 0 ; back := [] |}
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
(* We consider the numbers are strict, for simplicity *)

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

(**)

#[global] Instance Exact_Queue {a} : Exact (Queue a) (QueueA a) :=
  fun q => MkQueueA (nfront q) (exact (front q)) (nback q) (exact (back q)).

Record less_defined_QueueA {a} (q1 q2 : QueueA a) : Prop :=
  { ld_front : less_defined (frontA q1) (frontA q2)
  ; ld_back : less_defined (backA q1) (backA q2)
  }.

#[global] Instance LessDefined_QueueA {a} : LessDefined (QueueA a) :=
  less_defined_QueueA.

#[global] Instance LessDefinedOrder_QueueA {a} : @LessDefinedOrder (QueueA a) _.
Proof.
Admitted.

#[global] Instance LessDefinedExact_QueueA {a} : @LessDefinedExact (QueueA a) _ _ _ _.
Proof.
Admitted.

(* Well-formedness *)

Record well_formed {a} (q : Queue a) : Prop :=
  { skew : nback q <= nfront q
  ; frontn : nfront q = length (front q)
  ; backn : nback q = length (back q)
  }.

Lemma well_formed_empty {a} : well_formed (a := a) empty.
Proof.
  constructor; cbn; reflexivity.
Qed.

Lemma well_formed_mkQueue {a} nf (f : list a) nb b
  : nf = length f -> nb = length b -> well_formed (mkQueue nf f nb b).
Proof.
Admitted.

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

(* Lazy amortization works by hiding thunks "deep" in the data structure,
   so they cannot be forced immediately, only after performing operations whose
   cost is propoertional to the cost of the thunk.

   However, in the clairvoyance monad, we must decide whether to evaluate thunks
   right when they are constructed, so we have to predict the future to know whether
   it will be used.

   In other words, a user of the cost specification must first decide what the demand
   on the outputs will be. The demand will be modeled by an approximation value (T (QueueA a)).
   The higher the demand, the higher the cost, which will be amortized since the only
   way to have high demand is to perform many operations in the future.
*)

(* Before modeling cost, we must model demand. The caller of a function makes a demand
   on its output, which the function translates to a demand on the inputs.

   We can thus define a function from output demands to input demands.

   These can also in principled be derived automatically from the initial implementation.
 *)

(* A combinator for demand functions. If [f : a -> b] is a demand function with input [a],
   then [thunkD f : T a -> b] is a demand function with input [T a]. *)
Definition thunkD {a b} `{Bottom b} (f : a -> b) (x : T a) : b :=
  match x with
  | Undefined => bottom
  | Thunk x => f x
  end.

(* Demand function for [appendA]. Note that the output demand [outD] is at least
   either [NilA] or [ConsA] (i.e., it forces the result at least to WHNF).
   [thunkD] can then be used to lift the output demand type to thunks.  *)
Fixpoint appendD {a} (xs ys : list a) (outD : listA a) : T (listA a) * T (listA a) :=
  match xs, outD with
  | [], _ => (Thunk NilA, Thunk outD)
  | x :: xs, ConsA zD zsD =>
    let '(xsD, ysD) := thunkD (appendD xs ys) zsD in
    (Thunk (ConsA zD xsD), ysD)
  | _, _ => bottom (* Nonsense: if (xs = _ :: _) then append xs ys = (_ :: _)
                      so the demand cannot be of the form [] *)
  end.

(* Demand function for [revA].
   [revA] has to traverse the list: the input demand is the whole list.
   (Actually, a finer solution is to force only the spine, not the elements,
   since they are protected by [T], but, simplicity.) *)
Definition revD {a} (xs : list a) (outD : listA a) : T (listA a) :=
  exact xs.

(* [mkQueue] uses [rev] and [append], in this order ([append front (rev back)]),
   so we compute the demand in reverse. *)
Definition mkQueueD {a} (nfront : nat) (front : list a) (nback : nat) (back : list a)
    (outD : QueueA a) : T (listA a) * T (listA a) :=
  if nfront <? nback then
    let '(frontD, rbackD) := thunkD (appendD front (rev back)) (frontA outD) in
    let backD := thunkD (revD back) rbackD in
    (frontD, backD)
  else (frontA outD, backA outD).

Definition emptyA' {a} : T (QueueA a) := Thunk (MkQueueA 0 (Thunk NilA) 0 (Thunk NilA)).

(* In [pushA], [q] is always forced, so the first component of the input demand is at least
   [Thunk]. *)
Definition pushD {a} (q : Queue a) (x : a) (outD : QueueA a) : T (QueueA a) * T a :=
  let '(frontD, backD) := mkQueueD (nfront q) (front q) (S (nback q)) (x :: back q) outD in
  (Thunk (MkQueueA (nfront q) frontD (nback q) backD), Thunk x).

Definition popD {a} (q : Queue a) (outD : option (T a * T (QueueA a))) : T (QueueA a) :=
  match front q, outD with
  | [], _ => exact q  (* The queue is empty so the "whole queue" must be a fixed value. *)
  | x :: f, Some (xA, pop_qA) => Thunk (MkQueueA
      (nfront q)
      (Thunk (ConsA xA (thunkD frontA pop_qA)))
      (nback q)
      (thunkD backA pop_qA))
  | _, _ => bottom
  end.

(* The following theorems relate the demand functions to the approximation functions.
   Given the output demand, we compute the input demand, and we expect that
   running the function on those input demands will (optimistically) yield a
   result at least as defined as the output demand. *)

Lemma appendD_spec {a} (xs ys : list a) (outD : listA a)
  : forall xsD ysD, (xsD, ysD) = appendD xs ys outD ->
    appendA xsD ysD [[ fun out _ => outD `less_defined` out ]].
Proof.
Admitted.

Lemma pushD_spec {a} (q : Queue a) (x : a) (outD : QueueA a)
  : well_formed q ->
    forall qD xD, (qD, xD) = pushD q x outD ->
    pushA qD xD [[ fun out _ => outD `less_defined` out ]].
Proof.
Admitted.

Lemma popD_spec {a} (q : Queue a) (outD : option (T a * T (QueueA a)))
  : well_formed q ->
    let qD := popD q outD in
    popA qD [[ fun out _ => outD `less_defined` out ]].
Proof.
Admitted.

(* Monotonicity: There should also be properties that making inputs of approximation functions
   more defined makes the output more defined. These can be used to generalize the
   demand specifications above to inputs greater than the input demand. *)

Lemma appendA_mon {a} (xsA xsA' ysA ysA' : T (listA a))
  : xsA `less_defined` xsA' ->
    ysA `less_defined` ysA' ->
    appendA xsA  ysA  `less_defined` appendA xsA' ysA'.
Proof.
Admitted.

Lemma pushA_mon {a} (qA qA' : T (QueueA a)) xA xA'
  : qA `less_defined` qA' ->
    xA `less_defined` xA' ->
    pushA qA xA `less_defined` pushA qA' xA'.
Proof.
Admitted.

Lemma popA_mon {a} (qA qA' : T (QueueA a))
  : qA `less_defined` qA' ->
    popA qA `less_defined` popA qA'.
Proof.
Admitted.

(**)

(* Physicist's method *)

(* With an explicit representation of demand, we can attach a notion of "debt",
   or "negative potential" to it.
   "Higher" demands cost more to satisfy. Here, the debt must decrease constantly when
   we pop elements from the front or when we push elements to the back. When the two
   queues are of equal length, the debt is zero, and we are free to increase it again.
   A reverse-append costs (length (front q) + length (back q) = 2 * length (front q)),
   because the two lists have the same length.
   But because the [reverse], unlike [append], cannot be done incrementally,
   we must frontload those debits on the first half of the list, hence the factor [2] in
   [debt].

   But we might not need the whole output, in which case we can drop the debits for
   thunks that won't be reached. This is why the debt is a function of the demand,
   rather than the complete output, and we look at the partial length ([sizeX])
   of [frontA] instead of reading the exact length in [nfrontA].
   *)

(* TODO: can you increase the debt if it is not yet zero? In Okasaki, no, and that's why
   the Banker's method is more general. But this seems different. As long as your final
   demand (at the end of all operations) has debt 0, you can do anything. *)

(* This is an algorithm-specific class; another data structure should define its own... *)
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

(* Ad hoc overloading of [debt] on the output of [pop]. *)
#[local] Instance Debitable_popo {a} : Debitable (option (T a * T (QueueA a))) :=
  fun x =>
    match x with
    | None => 0
    | Some (_, qA) => debt qA
    end.

(* The two main theorems to prove are [pushA_cost] and [popA_cost].
   We then generalize them by monotonicity into [pushA_cost'] and [popA_cost'],
   where the input doesn't have to be exactly equal to the input demand. *)

Lemma pushA_cost {a} (q : Queue a) (x : a) (outD : QueueA a)
  : well_formed q ->
    forall qA xA, (qA, xA) = pushD q x outD ->
    pushA qA xA [[ fun out cost =>
      outD `less_defined` out /\ debt qA + cost <= 4 + debt outD ]].
Proof.
Admitted.

Lemma pushA_cost' {a} (q : Queue a) (x : a) (outD : QueueA a)
  : well_formed q ->
    forall qA xA, (qA, xA) = pushD q x outD ->
    forall qA', qA `less_defined` qA' ->
    pushA qA' xA [[ fun out cost =>
      outD `less_defined` out /\ debt qA + cost <= 4 + debt outD ]].
Proof.
  intros. eapply optimistic_corelax.
  - eapply pushA_mon. eassumption. reflexivity.
  - red. intros * ? ? []. split; etransitivity; try eassumption. lia.
  - eapply pushA_cost; eassumption.
Qed.

Lemma popA_cost {a} (q : Queue a) (outD : option (T a * T (QueueA a)))
  : well_formed q ->
    let qA := popD q outD in
    popA qA [[ fun out cost =>
      outD `less_defined` out /\ debt qA + cost <= 4 + debt outD ]].
Proof.
Admitted.

Lemma popA_cost' {a} (q : Queue a) (outD : option (T a * T (QueueA a)))
  : well_formed q ->
    let qA := popD q outD in
    forall qA', qA `less_defined` qA' ->
    popA qA' [[ fun out cost =>
      outD `less_defined` out /\ debt qA + cost <= 4 + debt outD ]].
Proof.
  intros.
  eapply optimistic_corelax.
  - eapply popA_mon. eassumption.
  - red. intros * ? ? []; split; etransitivity; try eassumption. lia.
  - apply popA_cost. assumption.
Qed.

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
     run_tree t _empty) [[ fun _ n => n <= 4 * size_tree t ]].

(* The proof: we first compute the demand. *)

(* Partial function: we assume that both arguments approximate the same list *)
Fixpoint lub_list {a} (xs ys : listA a) : listA a :=
  match xs, ys with
  | NilA, NilA => NilA
  | ConsA x xs, ConsA _ ys => ConsA x (lub_T lub_list xs ys)
  | _, _ => NilA  (* silly case *)
  end.

#[global] Instance Lub_list {a} : Lub (listA a) := lub_list.

#[global] Instance Lub_QueueA {a} : Lub (QueueA a) :=
  fun q1 q2 =>
    MkQueueA (nfrontA q1) (lub (frontA q1) (frontA q2)) (nbackA q1) (lub (backA q1) (backA q2)).

#[global] Instance LubLaw_QueueA {a} : LubLaw (QueueA a).
Proof.
Admitted.

Class LubDebt a `{Lub a, Debitable a} : Prop :=
  lub_debt : forall x y : a, debt (lub x y) <= debt x + debt y.

Arguments LubDebt : clear implicits.
Arguments LubDebt a {_ _}.

#[global] Instance LubDebt_T {a} `{LubDebt a} : LubDebt (T a).
Proof.
Admitted.

#[global] Instance LubDebt_QueueA {a} : LubDebt (QueueA a).
Proof.
Admitted.

Fixpoint demand_tree {a} (t : tree a) (q : Queue a) : T (QueueA a) :=
   match t with
   | Push x t =>
     let d := demand_tree t (push q x) in
     fst (thunkD (pushD q x) d)
   | Pop t =>
     match pop q with
     | None => exact q
     | Some (x, q') =>
       let d := demand_tree t q' in
       popD q (Some (Thunk x, d))
     end
   | Share t1 t2 => lub (demand_tree t1 q) (demand_tree t2 q)
   | Done => bottom
   end.

Lemma demand_tree_approx {a} (t : tree a) q
  : demand_tree t q `less_defined` exact q.
Proof.
Admitted.

Lemma pop_popD {a} (q : Queue a)
  : pop q = None -> popD q None = exact q.
Proof.
  unfold pop, popD. destruct (front q); [reflexivity | discriminate].
Qed.

(* The core lemma where the action happens *)
Lemma run_tree_cost {a} (t : tree a) (q : Queue a) (qA : T (QueueA a))
  : well_formed q ->
    demand_tree t q `less_defined` qA ->
    run_tree t qA [[ fun _ n => debt (demand_tree t q) + n <= 4 * size_tree t ]].
Proof.
Opaque Nat.mul Nat.add.
  revert q qA; induction t; cbn; intros q qA wf_q ld_q.
  - mgo'. assert (WF := well_formed_push a0 wf_q).
    destruct (demand_tree t (push q a0)) as [ q' | ] eqn:Eq'; cbn in *.
    { apply optimistic_thunk_go.
      destruct (pushD q a0 q') as [xD qD] eqn:Epush; cbn in *.
      assert (PUSH := pushA_cost' a0 wf_q (eq_sym Epush) ld_q).
      assert (qD = Thunk a0). { unfold pushD in Epush. destruct mkQueueD in Epush. congruence. }
      subst. relax. { exact PUSH. }
      cbn; intros * []. relax. { apply (IHt _ _ WF). rewrite Eq'. constructor. assumption. }
      cbn; intros. rewrite Eq' in H1. cbn in H1. lia. }
    { apply optimistic_skip. relax. { apply (IHt _ _ WF). rewrite Eq'. constructor. }
      cbn; intros. lia. }
  - mgo'. assert (WF := fun x q' => well_formed_pop (x := x) (q' := q') wf_q). relax.
    { eapply @popA_cost' with (outD :=
        match pop q with Some (x, q') => Some (Thunk x, demand_tree t q') | None => None end).
      { eassumption. }
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
  - apply upper in ld_q. mgo'. relax. { apply IHt1; [apply wf_q | apply ld_q]. }
    cbn; intros; mgo'. relax. { apply IHt2; [apply wf_q | apply ld_q]. }
    cbn; intros; mgo'. rewrite lub_debt. lia.
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
