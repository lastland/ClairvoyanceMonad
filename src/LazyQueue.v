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

From Coq Require Import Arith List Lia Setoid Morphisms.
Import ListNotations.
From Clairvoyance Require Import Core Approx Monotonic List Misc.

Import RevCompare.

Set Implicit Arguments.
Set Contextual Implicit.
Set Maximal Implicit Insertion.

#[local] Existing Instance Exact_id | 1.
#[local] Existing Instance LessDefined_id | 100.
#[local] Existing Instance ApproximationAlgebra_id | 100.

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
  ; ld_nfront : nfrontA q1 = nfrontA q2
  ; ld_nback : nbackA q1 = nbackA q2
  }.

#[global] Hint Constructors less_defined_QueueA : core.
#[global] Hint Resolve ld_front ld_back ld_nfront ld_nback : core.

#[global] Instance LessDefined_QueueA {a} : LessDefined (QueueA a) :=
  less_defined_QueueA.

#[global] Instance ApproximationAlgebra_QueueA {a} : ApproximationAlgebra (QueueA a) (Queue a).
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

Definition emptyX {a} : T (QueueA a) := Thunk (MkQueueA 0 (Thunk NilA) 0 (Thunk NilA)).

Definition tailX {a} (xs : T (listA a)) : T (listA a) :=
  match xs with
  | Thunk (ConsA _ xs) => xs
  | _ => Undefined
  end.

(* In [pushA], [q] is always forced, so the first component of the input demand is at least
   [Thunk]. *)
Definition pushD {a} (q : Queue a) (x : a) (outD : QueueA a) : T (QueueA a) * T a :=
  let '(frontD, backD) := mkQueueD (nfront q) (front q) (S (nback q)) (x :: back q) outD in
  (Thunk (MkQueueA (nfront q) frontD (nback q) (tailX backD)), Thunk x).

Definition popD {a} (q : Queue a) (outD : option (T a * T (QueueA a))) : T (QueueA a) :=
  match front q, outD with
  | [], _ => exact q  (* The queue is empty so the "whole queue" must be a fixed value. *)
  | x :: f, Some (xA, pop_qA) =>
    let '(fD, bD) := thunkD (mkQueueD (pred (nfront q)) f (nback q) (back q)) pop_qA in
    Thunk (MkQueueA
      (nfront q)
      (Thunk (ConsA xA fD))
      (nback q)
      bD)
  | _, _ => bottom
  end.

(* The demand is an approximation of the input. *)

Lemma mkQueueD_approx {a} nf (f : list a) nb b (outD : QueueA a)
  : outD `is_approx` mkQueue nf f nb b ->
    mkQueueD nf f nb b outD `is_approx` (f, b).
Proof.
Admitted.

Lemma tailX_mon {a} (xs xs' : T (listA a))
  : xs `less_defined` xs' -> tailX xs `less_defined` tailX xs'.
Proof.
  destruct 1 as [ | ? ? [ | ] ]; cbn; auto.
Qed.

#[global] Instance Proper_tailX {a} : Proper (less_defined ==> less_defined) (@tailX a).
Proof. exact (@tailX_mon a). Qed.

From Equations Require Import Equations.

Lemma pushD_approx {a} (q : Queue a) (x : a) (outD : QueueA a)
  : outD `is_approx` push q x -> pushD q x outD `is_approx` (q, x).
Proof.
  unfold push, pushD.
  intros Hout. unfold pushD.
  destruct mkQueueD eqn:HQ.
  constructor.
  - apply mkQueueD_approx in Hout. rewrite HQ in Hout.
    destruct Hout as [Hout1 Hout2]; cbn in Hout1, Hout2.
    constructor; constructor; cbn; auto.
    rewrite Hout2. cbn.
    change (exact (a := list ?a) (b := listA ?b)) with (exact_listA (a := a) (b := b)).
    simp exact_listA. constructor; reflexivity.
  - constructor; reflexivity.
Qed.

Lemma appendD_approx {a} (xs ys : list a) (outD : _)
  : outD `is_approx` append xs ys -> appendD xs ys outD `is_approx` (xs, ys).
Proof.
  revert outD; induction xs; cbn.
  - intros; solve_approx idtac.
  - unfold is_approx; autorewrite with exact; intros. inversion H; subst.
    inversion H4; subst; cbn.
    + constructor; cbn; constructor. autorewrite with exact. constructor; auto; constructor.
    + specialize (IHxs _ H2); inversion IHxs; subst.
      destruct appendD; cbn in *. solve_approx idtac. cbn. autorewrite with exact.
      constructor; auto.
Qed.

Lemma popD_approx {a} (q : Queue a) (outD : _)
  : outD `is_approx` pop q -> popD q outD `is_approx` q.
Proof.
  unfold pop, popD. destruct front eqn:Ef; cbn; inversion 1; subst.
  - red; reflexivity.
  - destruct x; destruct H2; cbn in *.
    inversion snd_rel; subst; cbn.
    + constructor. constructor; cbn; auto; constructor. rewrite Ef; autorewrite with exact.
      constructor; auto. constructor.
    + apply mkQueueD_approx in H2. destruct mkQueueD eqn:Em.
      destruct H2; cbn in *. constructor; constructor; cbn; auto.
      rewrite Ef; autorewrite with exact. constructor; constructor; auto.
Qed.

Lemma popD_approx_Some {a} (q q' : Queue a) x (outD : _)
  : pop q = Some (x, q') -> outD `is_approx` (x, q') -> popD q (Some outD) `is_approx` q.
Proof.
  intros Hpop Hout; apply popD_approx. rewrite Hpop. constructor. apply Hout.
Qed.

Lemma appendD_size {a} (xs ys : list a) (outD : _)
  : outD `is_approx` append xs ys ->
    let xy := appendD xs ys outD in
    sizeX' 0 outD = sizeX (sizeX 0 (snd xy)) (fst xy).
Proof.
  revert outD; induction xs; cbn; intros; [ reflexivity | ].
  destruct outD as [ | ? [] ]; cbn; [ reflexivity | | reflexivity ].
  rewrite IHxs.
  - destruct appendD as [ [] ? ] eqn:E; cbn; reflexivity.
  - inversion H; subst. inversion H5; subst. auto.
Qed.

Lemma appendD_Thunk_r {a} (xs ys : list a) (outD : _)
  : outD `is_approx` append xs ys ->
    forall xsA ysA, (xsA, Thunk ysA) = appendD xs ys outD ->
    sizeX 0 xsA = length xs.
Proof.
  revert outD; induction xs; cbn; intros outD Hout xsA ysA H.
  - inversion H; reflexivity.
  - inversion Hout; subst.
    inversion H4; subst; cbn in H.
    + inversion H.
    + destruct appendD eqn:ED in H; inversion H; subst; cbn.
      erewrite <- IHxs by eauto.
      destruct t as [ xs' | ]; reflexivity.
Qed.

(* The following theorems relate the demand functions to the approximation functions.
   Given the output demand, we compute the input demand, and we expect that
   running the function on those input demands will (optimistically) yield a
   result at least as defined as the output demand.

   These are subsumed by the [_cost] lemmas. *)

Lemma appendD_spec {a} (xs ys : list a) (outD : listA a)
  : forall xsD ysD, (xsD, ysD) = appendD xs ys outD ->
    appendA xsD ysD [[ fun out _ => outD `less_defined` out ]].
Proof.
Abort.

Lemma pushD_spec {a} (q : Queue a) (x : a) (outD : QueueA a)
  : well_formed q ->
    forall qD xD, (qD, xD) = pushD q x outD ->
    pushA qD xD [[ fun out _ => outD `less_defined` out ]].
Proof.
Abort.

Lemma popD_spec {a} (q : Queue a) (outD : option (T a * T (QueueA a)))
  : well_formed q ->
    let qD := popD q outD in
    popA qD [[ fun out _ => outD `less_defined` out ]].
Proof.
Abort.

(* Monotonicity: There should also be properties that making inputs of approximation functions
   more defined makes the output more defined. These can be used to generalize the
   demand specifications above to inputs greater than the input demand. *)

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

Opaque Nat.mul Nat.add Nat.sub.

Lemma revA__cost {a} (xs ys : list a)
  : revA_ (exact xs) (exact ys) [[ fun out cost =>
      out = exact (rev_append xs ys) /\ cost = length xs + 1 ]].
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
      out = exact (rev_append xs []) /\ cost = length xs + 1 ]].
Proof.
  unfold revA; mgo'. apply optimistic_thunk_go; mgo'. apply (revA__cost xs nil).
Qed.

Lemma appendA_cost {a} (xs ys : list a) outD
  : outD `is_approx` append xs ys ->
    forall xsA ysA, (xsA, ysA) = appendD xs ys outD ->
    appendA xsA ysA [[ fun out cost =>
      outD `less_defined` out /\ cost <= sizeX 1 xsA ]].
Proof.
  revert outD; induction xs; cbn; intros outD Hout * H.
  - inversion H; subst. cbn. mgo'. split; [ reflexivity | lia ].
  - inversion Hout; subst.
    destruct thunkD eqn:ED in H. inversion H; subst.
    cbn; repeat mforward idtac.
    inversion H4; subst.
    + apply optimistic_skip. mgo'. split; [reflexivity | lia].
    + apply optimistic_thunk_go. relax; [apply IHxs; eauto| cbn; intros ].
      mforward idtac. split; [ constructor; [reflexivity | constructor; apply H0] | ].
      destruct t; cbn in H0; lia.
Qed.

Lemma appendA_cost' {a} (xs ys : list a) outD
  : outD `is_approx` append xs ys ->
    forall xsA ysA, (xsA, ysA) = appendD xs ys outD ->
    forall xsA' ysA', xsA `less_defined` xsA' -> ysA `less_defined` ysA' ->
    appendA xsA' ysA' [[ fun out cost =>
      outD `less_defined` out /\ cost <= sizeX 1 xsA ]].
Proof.
  intros. eapply optimistic_corelax.
  - eapply appendA_mon; eassumption.
  - apply uc_cost.
  - eauto using appendA_cost.
Qed.

Lemma size_approx {a} (xs : list a) (xsA : T (listA a))
  : xsA `is_approx` xs -> sizeX 0 xsA <= length xs.
Proof.
  revert xsA; induction xs; intros *; inversion 1; subst; cbn; try lia.
  - inversion H2; cbn; lia.
  - inversion H2; subst; cbn. inversion H5; subst; cbn. lia.
    apply le_n_S. eapply (IHxs (Thunk x)); auto.
Qed.

Lemma sizeX_up {a} (xs : T (listA a)) n : sizeX n xs <= sizeX 0 xs + n.
Proof.
  destruct xs as [ xs | ]; cbn; [ | lia ].
  induction xs; cbn; lia.
Qed.

Lemma sizeX_down {a} (xs : T (listA a)) n : sizeX 0 xs <= sizeX n xs.
Proof.
  destruct xs as [ xs | ]; cbn; [ | lia ].
  induction xs; cbn; lia.
Qed.

Lemma mkQueueA_cost {a} (nf : nat) (f : list a) (nb : nat) (b : list a) (outD : QueueA a)
  : nf = length f /\ nb = length b /\ nb <= nf + 1 -> outD `is_approx` mkQueue nf f nb b ->
    forall fA bA, (fA, bA) = mkQueueD nf f nb b outD ->
    mkQueueA nf fA nb bA [[ fun out cost =>
      outD `less_defined` out /\ 2 * sizeX 0 fA - 2 * nb + cost <= 4 + debt outD  ]].
Proof.
  unfold mkQueue, mkQueueA, mkQueueD.
  intros (Hf & Hb & Hbf) Hout * HmkQ.
  destruct (Nat.ltb_spec nf nb); repeat mforward idtac.
  - destruct thunkD eqn:ED in HmkQ. inversion HmkQ; subst; clear HmkQ.
    destruct t0; cbn.
    + apply optimistic_thunk_go.
      relax; [ apply revA_cost | cbn; intros * [] ].
      mforward idtac.
      apply optimistic_thunk_go.
      destruct frontA eqn:Ef in ED; cbn in ED; [ | inversion ED ].
      inversion Hout; cbn in *. rewrite Ef in ld_front0.
      inversion ld_front0; subst; clear ld_front0.
      assert (APX := appendD_approx H4).
      rewrite ED in APX. destruct APX as [APX1 APX2]; cbn in *; inversion APX2; subst.
      relax.
      { eapply appendA_cost'; eauto. { reflexivity. }
        { constructor; auto. rewrite <- rev_alt; auto. } }
      cbn; intros * []. mforward idtac. split.
      * constructor; auto. cbn. rewrite Ef; constructor; auto.
      * unfold debt, Debitable_QueueA.
        rewrite Ef. cbn. erewrite appendD_size by eauto.
        rewrite ED; cbn.
        rewrite (size_approx (xs := f)) by assumption.
        rewrite sizeX_up in H1.
        rewrite <- sizeX_down.
        rewrite ld_nback0.
        assert (sizeX 0 t = length f). { eapply appendD_Thunk_r; eauto. }
        lia.
    + apply optimistic_skip; mforward idtac.
      inversion Hout; cbn in *.
      destruct frontA eqn:Ef in *; cbn in ED.
      * apply optimistic_thunk_go.
        inversion ld_front0; subst; clear ld_front0.
        relax.
        { eapply appendA_cost'; eauto; reflexivity. }
        cbn; intros * []. mforward idtac. split.
        ** constructor; cbn; auto. rewrite Ef; constructor; auto.
        ** unfold debt, Debitable_QueueA.
           rewrite ld_nback0. rewrite Ef; cbn; erewrite appendD_size by eauto.
           rewrite ED; cbn. rewrite sizeX_up in H1.
            assert (sizeX 0 t <= length f).
            { apply size_approx. apply appendD_approx in H2.
              rewrite ED in H2. apply H2. }
            lia.
      * apply optimistic_skip. mforward idtac. cbn.
        split; [ constructor; cbn; eauto; rewrite Ef; auto | ].
        inversion ED; subst; cbn. lia.
  - unfold debt, Debitable_QueueA.
    inversion HmkQ; subst. split; [ constructor; cbn; reflexivity + apply Hout | ].
    inversion Hout; cbn in *. lia.
Qed.

Lemma mkQueueA_cost' {a} (nf : nat) (f : list a) (nb : nat) (b : list a) (outD : QueueA a)
  : forall fA bA, (fA, bA) = mkQueueD nf f nb b outD ->
    forall fA' bA', fA `less_defined` fA' -> bA `less_defined` bA' ->
    mkQueueA nf fA' nb bA' [[ fun out cost =>
      outD `less_defined` out /\ 2 * sizeX 0 fA - 2 * nb + cost <= 4 + debt outD ]].
Proof.
Admitted.

Lemma pushA_cost {a} (q : Queue a) (x : a) (outD : QueueA a)
  : well_formed q ->
    forall qA xA, (qA, xA) = pushD q x outD ->
    pushA qA xA [[ fun out cost =>
      outD `less_defined` out /\ debt qA + cost <= 7 + debt outD ]].
Proof.
Admitted.

Lemma pushA_cost' {a} (q : Queue a) (x : a) (outD : QueueA a)
  : well_formed q ->
    forall qA xA, (qA, xA) = pushD q x outD ->
    forall qA', qA `less_defined` qA' ->
    pushA qA' xA [[ fun out cost =>
      outD `less_defined` out /\ debt qA + cost <= 7 + debt outD ]].
Proof.
  intros. eapply optimistic_corelax.
  - eapply pushA_mon. eassumption. reflexivity.
  - apply uc_acost.
  - eapply pushA_cost; eassumption.
Qed.

Lemma popA_cost {a} (q : Queue a) (outD : option (T a * T (QueueA a)))
  : well_formed q ->
    outD `is_approx` pop q ->
    let qA := popD q outD in
    popA qA [[ fun out cost =>
      outD `less_defined` out /\ debt qA + cost <= 7 + debt outD ]].
Proof.
  intros Wq Hout; unfold popA. mgo'.
  unfold popD; unfold pop in Hout. destruct (front q) eqn:Ef.
  - cbn. repeat (mforward idtac; cbn).
    let q' := eval unfold exact, Exact_Queue in (exact q) in change (exact q) with q'.
    rewrite Ef. simp exact_listA. mforward idtac.
    rewrite exact_list_unfold_nil. mforward idtac.
    split; cbn; auto. unfold debt, Debitable_QueueA; cbn. rewrite exact_list_unfold_nil. cbn. lia.
  - inversion Hout; subst. destruct H1 as [Hfst Hsnd]; destruct x as [x' q']; cbn in *.
    destruct thunkD eqn:EmkQ. cbn.
    repeat (mforward idtac; cbn). inversion Hsnd; subst; cbn in *.
    + apply optimistic_skip. mforward idtac; cbn [thunkD bottom Bottom_T].
      split; [ reflexivity | ]. inversion EmkQ; subst. unfold debt, Debitable_QueueA. cbn.
      lia.
    + apply optimistic_thunk_go; cbn.
      assert (HQ := @mkQueueA_cost _ (pred (nfront q)) l (nback q) (back q) x).
      eassert (HQH : _); [ | specialize (HQ HQH) ].
      { destruct Wq. inversion Hout; cbn in *; subst. rewrite Ef in *; cbn in *.
        lia. }
      relax; [ eapply mkQueueA_cost; eauto | ].
      cbn; intros * [HH HH']. mforward idtac.
      split; [ constructor; constructor; cbn; [ reflexivity | constructor; apply HH ] | ].
      revert HH'.
      unfold debt, Debitable_QueueA; cbn.
      destruct t; cbn; try lia.
Qed.

Lemma popA_cost' {a} (q : Queue a) (outD : option (T a * T (QueueA a)))
  : well_formed q ->
    outD `is_approx` pop q ->
    let qA := popD q outD in
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

(* Partial function: we assume that both arguments approximate the same list *)
Fixpoint lub_list {a} (xs ys : listA a) : listA a :=
  match xs, ys with
  | NilA, NilA => NilA
  | ConsA x xs, ConsA y ys => ConsA (lub_T (fun r _ => r) x y) (lub_T lub_list xs ys)
  | _, _ => NilA  (* silly case *)
  end.

#[global] Instance Lub_list {a} : Lub (listA a) := lub_list.

#[global] Instance Lub_QueueA {a} : Lub (QueueA a) :=
  fun q1 q2 =>
    MkQueueA (nfrontA q1) (lub (frontA q1) (frontA q2)) (nbackA q1) (lub (backA q1) (backA q2)).

Class Rep (a b : Type) : Type :=
  { to_rep : a -> b
  ; from_rep : b -> a
  ; to_from : forall x, to_rep (from_rep x) = x
  ; from_to : forall x, from_rep (to_rep x) = x
  }.

#[global,refine]
Instance Rep_QueueA {a} : Rep (QueueA a) (nat * T (listA a) * nat * T (listA a)) :=
  {| to_rep := fun q => (nfrontA q, frontA q, nbackA q, backA q)
  ;  from_rep := fun '(nf,f,nb,b) => MkQueueA nf f nb b
  |}.
Proof.
  - intros [ [ [nf f] nb] b]; reflexivity.
  - intros []; reflexivity.
Defined.

Class LubRep a b `{Rep a b,Lub a,Lub b} : Prop :=
  to_rep_lub : forall x y : a, to_rep (lub x y) = lub (to_rep x) (to_rep y).

Arguments LubRep : clear implicits.
Arguments LubRep a b {_ _ _}.

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

#[global] Instance LubRep_QueueA {a} : LubRep (QueueA a) (nat * T (listA a) * nat * T (listA a)).
Proof.
  intros [] []; reflexivity.
Qed.

Class LessDefinedRep a b `{REP : Rep a b, LDa : LessDefined a, LDb : LessDefined b} : Prop :=
  to_rep_less_defined : forall x y : a, less_defined x y <-> less_defined (a := b) (to_rep x) (to_rep y).

Arguments LessDefinedRep : clear implicits.
Arguments LessDefinedRep a b {REP LDa LDb}.

#[global] Instance LessDefinedRep_QueueA {a} : LessDefinedRep (QueueA a) _.
Proof.
  intros [] []; cbn; firstorder.
Qed.

Lemma to_rep_cobounded {a b} `{LessDefinedRep a b}
  : forall x y : a, Basics.impl (cobounded x y) (cobounded (a := b) (to_rep x) (to_rep y)).
Proof.
  intros x y [z [Hx Hy] ]; exists (to_rep z); rewrite <- 2 to_rep_less_defined; auto.
Qed.

Lemma LubLaw_LubRep a b `{LubRep a b,LessDefinedRep a b (REP := _),LL: !LubLaw b} : LubLaw a.
Proof.
  constructor; intros *; rewrite ?to_rep_cobounded, 3? to_rep_less_defined, to_rep_lub; apply LL.
Qed.

#[global] Instance LubLaw_QueueA {a} : LubLaw (QueueA a).
Proof.
  exact LubLaw_LubRep.
Qed.

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
  - destruct (pop q) as [ [] | ] eqn:Hpop; [ | red; reflexivity ].
    + apply (popD_approx_Some Hpop). constructor; cbn; [ constructor; reflexivity | apply IHt ].
  - unfold is_approx in *; apply lub_least_upper_bound; auto.
  - apply bottom_least.
Qed.

Lemma cobounded_demand_tree {a} (t1 t2 : tree a) q
  : cobounded (demand_tree t1 q) (demand_tree t2 q).
Proof.
  exists (exact q); split; apply demand_tree_approx.
Qed.

Lemma pop_popD {a} (q : Queue a)
  : pop q = None -> popD q None = exact q.
Proof.
  unfold pop, popD. destruct (front q); [reflexivity | discriminate].
Qed.

(* The core lemma where the action happens *)
Lemma run_tree_cost {a} (t : tree a) (q : Queue a) (qA : T (QueueA a))
  : well_formed q ->
    demand_tree t q `less_defined` qA ->
    run_tree t qA [[ fun _ n => debt (demand_tree t q) + n <= 7 * size_tree t ]].
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
