(* This is the two-list version of the Queue *)

From Equations Require Import Equations.

From Coq Require Import Arith List Lia Setoid Morphisms.
Import ListNotations.
From Clairvoyance Require Import Core Approx ApproxM ListA List Misc Tick.

Import Tick.Notations.

Set Primitive Projections.
Set Implicit Arguments.
Set Contextual Implicit.
Set Maximal Implicit Insertion.

#[local] Existing Instance Exact_id | 1.
#[local] Existing Instance LessDefined_id | 100.
#[local] Existing Instance PreOrder_LessDefined_id | 100.
#[local] Existing Instance ExactMaximal_id | 100.

(* Pure implementation *)

Record Queue (a : Type) : Type := MkQueue
  { 
    front : list a
  ; back : list a
  }.

Definition empty {a} : Queue a := MkQueue [] [].

Definition push {a} (q : Queue a) (x : a) : Queue a :=
  MkQueue  (front q) (x :: back q).

Definition pop {a} (q : Queue a) : option (a * Queue a) :=
  match front q with
  | x :: f => Some (x, MkQueue f (back q))
  | [] => match (rev (back q)) with 
      | x :: f => Some (x, MkQueue f [])
      | [] => None
         end
  end.

(* Monadic implementation *)

Record QueueA (a : Type) : Type := MkQueueA
  { 
    frontA : T (listA a)
  ; backA : T (listA a)
  }.

Definition emptyA {a} : M (QueueA a) :=
  ret (MkQueueA (Thunk NilA) (Thunk NilA)).

Definition pushA {a} (q : T (QueueA a)) (x : T a) : M (QueueA a) :=
  tick >>
  let! q := force q in
  ret (MkQueueA (frontA q) (Thunk (ConsA x (backA q)))).

Definition popA {a} (q : T (QueueA a)) : M (option (T a * T (QueueA a))) :=
  tick >>
  let! q := force q in
  let! f := force (frontA q) in
  match f with
  | ConsA x f =>
    let q := MkQueueA f (backA q) in
    ret (Some (x, Thunk q))
  | NilA => 
      let! rb := revA (backA q) in
      match rb with 
      | ConsA x f =>
       let q := MkQueueA f (backA q) in
       ret (Some (x, Thunk q))
      | NilA =>
      ret None
      end
  end.

(** * Approximation structure for [QueueA] *)

(** [less_defined], [exact], [lub] *)

Record less_defined_QueueA {a} (q1 q2 : QueueA a) : Prop :=
  { ld_front : less_defined (frontA q1) (frontA q2)
  ; ld_back : less_defined (backA q1) (backA q2)
  }.

#[global] Hint Constructors less_defined_QueueA : core.
#[global] Hint Resolve ld_front ld_back : core.

#[global] Instance LessDefined_QueueA {a} : LessDefined (QueueA a) :=
  less_defined_QueueA.

#[global]
Instance Rep_QueueA {a} : Rep (QueueA a) (T (listA a) * T (listA a)) :=
  {| to_rep := fun q => (frontA q, backA q)
  ;  from_rep := fun '(f,b) => MkQueueA f b
  |}.

#[global] Instance RepLaw_QueueA {a} : RepLaw (QueueA a) _.
Proof.
  constructor.
  - intros [ f b] ; reflexivity.
  - intros []; reflexivity.
Qed.

#[global] Instance LessDefinedRep_QueueA {a} : LessDefinedRep (QueueA a) _.
Proof.
  intros [] []; cbn; firstorder.
Qed.

#[global] Instance PreOrder_QueueA {a} : PreOrder (less_defined (a := QueueA a)).
Proof. exact PreOrder_Rep. Qed.

#[global] Instance Exact_Queue {a} : Exact (Queue a) (QueueA a) :=
  fun q => MkQueueA (exact (front q)) (exact (back q)).

#[global] Instance ExactMaximal_QueueA {a} : ExactMaximal (QueueA a) (Queue a).
Proof.
  red; intros * []; cbn in *.
  apply exact_maximal in ld_front0; apply exact_maximal in ld_back0. destruct xA; cbn in *; subst.
  reflexivity.
Qed.

#[global] Instance Lub_QueueA {a} : Lub (QueueA a) :=
  fun q1 q2 =>
    MkQueueA (lub (frontA q1) (frontA q2)) (lub (backA q1) (backA q2)).

#[global] Instance LubRep_QueueA {a} : LubRep (QueueA a) (T (listA a) * T (listA a)).
Proof.
  intros [] []; reflexivity.
Qed.

#[global] Instance LubLaw_QueueA {a} : LubLaw (QueueA a).
Proof.
  exact LubLaw_LubRep.
Qed.


Lemma MkQueueA_mon {a} (f f' b b' : T (listA a))
  : 
    f `less_defined` f' ->
    b `less_defined` b' ->
    MkQueueA f b `less_defined` MkQueueA f' b'.
Proof.
  intros; subst; solve_mon.
Qed.

#[global] Hint Resolve MkQueueA_mon : mon.

Lemma pushA_mon {a} (qA qA' : T (QueueA a)) xA xA'
  : qA `less_defined` qA' ->
    xA `less_defined` xA' ->
    pushA qA xA `less_defined` pushA qA' xA'.
Proof.
  intros; unfold pushA. solve_mon.
  apply MkQueueA_mon; auto.
Qed.

Lemma popA_mon {a} (qA qA' : T (QueueA a))
  : qA `less_defined` qA' ->
    popA qA `less_defined` popA qA'.
Proof.
  intros; unfold popA. solve_mon.
Qed.

(**)



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

Definition emptyX {a} : T (QueueA a) := Thunk (MkQueueA (Thunk NilA) (Thunk NilA)).

(* In [pushA], [q] is always forced, so the first component of the input demand
   is at least [Thunk]. *)
Definition pushD {a} (q : Queue a) (x : a) (outD : QueueA a) : Tick (T (QueueA a) * T a) :=
  Tick.tick >>
  let backD := backA outD in
  Tick.ret (Thunk (MkQueueA (frontA outD) (tailX backD)), Thunk x).


Definition popD {a} (q : Queue a) (outD : option (T a * T (QueueA a))) : Tick (T (QueueA a)) := bottom.
(*
  Tick.tick >>
  match front q, outD with
  | [], Some (_, pop_qA) => bottom
      let+ bq := pop_qA in
      let+ b := thunkD (revD (back q)) (backA bq) in
      match rev (back q), b with 
        | x :: f, Some (xA, pop_qA) => 
            let (fD, bD) := (frontA pop_qA, backA pop_qA) in
            Tick.ret (Thunk (MkQueueA (Thunk (ConsA xA fD)) bD))
        | [] , _ =>
            Tick.ret (exact q)  (* The queue is empty so the "whole queue" must be a fixed value. *) 
      end 
  | x :: f, Some (xA, pop_qA) =>
    let+ qa := pop_qA in
    let (fD, bD) := (frontA pop_qA, backA pop_qA) in
    Tick.ret (Thunk (MkQueueA
      (Thunk (ConsA xA fD)) bD))
  | _, _ => bottom
  end. *)


(** ** Soundness of demand functions *)

(** *** Soundess of demand functions with respect to pure functions *)

(** A demand function [fD] must produce an approximation of the input
  of the corresponding pure function [f]. *)

(** These proofs should be automatable, the demand functions can be derived from the
  pure functions. *)

Lemma pushD_approx {a} (q : Queue a) (x : a) (outD : QueueA a)
  : outD `is_approx` push q x -> Tick.val (pushD q x outD) `is_approx` (q, x).
Proof.
  unfold push, pushD.
  intros Hout. unfold pushD.
  destruct Hout as [Hout1 Hout2]; cbn in Hout1, Hout2.
  apply tailX_mon in Hout2.
  solve_approx.
Qed.

Lemma popD_approx {a} (q : Queue a) (outD : _)
  : outD `is_approx` pop q -> Tick.val (popD q outD) `is_approx` q.
Proof.
Admitted.
(*
  unfold pop, popD. destruct (front _) eqn:Ef; cbn; inversion 1; subst.
  - reflexivity.
  - destruct x; destruct H2; cbn in *.
    inversion snd_rel; subst; cbn [Tick.val thunkD bottom Tick.Bottom_Tick Bottom_prod Tick.ret].
    + solve_approx. rewrite Ef. solve_approx.
    + apply mkQueueD_approx in H2. destruct mkQueueD eqn:Em.
      destruct H2, val; cbn in *. solve_approx. rewrite Ef. solve_approx.
Qed.
*)

Lemma popD_approx_Some {a} (q q' : Queue a) x (outD : _)
  : pop q = Some (x, q') -> outD `is_approx` (x, q') -> Tick.val (popD q (Some outD)) `is_approx` q.
Proof.
  intros Hpop Hout; apply popD_approx. rewrite Hpop. constructor. apply Hout.
Qed.

(** *** Soundness of demand functions with respect to clairvoyant functions. *)

(** Given the output demand, we compute the input demand, and we expect that
    running the function on those input demands will (optimistically) yield a
    result at least as defined as the output demand. *)

(** These are subsumed by the [_cost] lemmas. *)

Lemma pushD_spec {a} (q : Queue a) (x : a) (outD : QueueA a)
  : outD `is_approx` push q x ->
    forall qD xD, (qD, xD) = Tick.val (pushD q x outD) ->
    let dcost := Tick.cost (pushD q x outD) in
    pushA qD xD [[ fun out cost => outD `less_defined` out /\ cost <= dcost ]].
Proof.
  unfold push, pushD, pushA; cbn beta iota.
  intros Hout * Hval. cbn in Hval. inv Hval. mgo_.
  split; [|auto]. inversion Hout. mgo_.
  eapply less_defined_tail_cons. 
  inversion ld_back0; subst; mgo_.
  inversion H1. subst. mgo_.
Qed.

Lemma popD_spec {a} (q : Queue a) (outD : option (T a * T (QueueA a)))
  : outD `is_approx` pop q ->
    forall qD, qD = Tick.val (popD q outD) ->
    let dcost := Tick.cost (popD q outD) in
    popA qD [[ fun out cost => outD `less_defined` out /\ cost <= dcost ]].
Proof.
Admitted.

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
  fun qA => 2 * sizeX 0 (frontA qA) - 2 * sizeX 0 (backA qA).

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

(** ** Cost specs for auxiliary functions *)

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


Lemma pushD_cost {a} (q : Queue a) (x : a) (outD : QueueA a)
  :  outD `is_approx` push q x ->
    forall qA xA, (qA, xA) = Tick.val (pushD q x outD) ->
    let cost := Tick.cost (pushD q x outD) in
    debt qA + cost <= 7 + debt outD.
Proof.
  intros Wq Hout; unfold pushA, pushD. simpl. inversion 1; subst.
  unfold debt, Debitable_T, debt, Debitable_QueueA. simpl.
  destruct (backA outD) as [outD' | ].
  - simpl. induction outD'; simpl; lia.
  - simpl. lia.
Qed.

(** Cost specification for [pushA] *)
Lemma pushA_cost {a} (q : Queue a) (x : a) (outD : QueueA a)
  : outD `is_approx` push q x ->
    forall qA xA, (qA, xA) = Tick.val (pushD q x outD) ->
    pushA qA xA [[ fun out cost =>
      outD `less_defined` out /\ debt qA + cost <= 7 + debt outD ]].
Proof.
  intros; relax; [ eapply pushD_spec; eauto | cbn beta ].
  intros * []; split; [ auto | ]. apply pushD_cost in H0; auto.
  lia.
Qed.

Print Assumptions pushA_cost.

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
  :  outD `is_approx` push q x ->
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
  : outD `is_approx` pop q ->
    let qA := Tick.val (popD q outD) in
    let cost := Tick.cost (popD q outD) in
    debt qA + cost <= 7 + debt outD.
Proof.
Admitted.

(** Cost specification for [popA] *)
Lemma popA_cost {a} (q : Queue a) (outD : option (T a * T (QueueA a)))
  : outD `is_approx` pop q ->
    let qA := Tick.val (popD q outD) in
    popA qA [[ fun out cost =>
      outD `less_defined` out /\ debt qA + cost <= 7 + debt outD ]].
Proof.
  intros; relax; [ eapply popD_spec; eauto | cbn beta ].
  intros * []; split; [ auto | ]. apply popD_cost in H; auto.
  fold qA in H0. 
Admitted.

(** Relaxed cost specification *)
Lemma popA_cost' {a} (q : Queue a) (outD : option (T a * T (QueueA a)))
  : outD `is_approx` pop q ->
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

(*
(** TODO: This is subsumed by QueueInterface.v *)

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
*)

(* Print Assumptions good_queue. *)
