(** Real-time Banker's Queue *)

(** Operations take non-amortized constant time. *)

From Coq Require Import List.
From Clairvoyance Require Import Core Approx ApproxM List Misc LazyQueue.

Import ListNotations.
Import RevCompare.

Set Primitive Projections.
Set Implicit Arguments.
Set Contextual Implicit.
Set Maximal Implicit Insertion.

Record QueueA (a : Type) : Type := MkQueueA
  { front : T (listA a)
  ; back : T (listA a)
  ; schedule : T (listA a) }.

Definition emptyA {a : Type} : QueueA a := let n := Thunk NilA in MkQueueA n n n.

(* rotate x y z = x ++ rev y ++ z *)
Fixpoint rotateA_ {a} (f b : listA a) (d : T (listA a)) : M (listA a) :=
  match f, b with
  | NilA, ConsA y _ => ret (ConsA y d)
  | ConsA x f, ConsA y b =>
    forcing f (fun f =>
    let! b := force b in
    let~ r := rotateA_ f b (Thunk (ConsA y d)) in
    ret (ConsA x r))
  | _, NilA => ret NilA  (* Should not happen *)
  end.

Definition rotateA {a} (f b d : T (listA a)) : M (listA a) :=
  let! f := force f in
  let! b := force b in
  rotateA_ f b d.

Definition mkQueueA {a} (f b s : T (listA a)) : M (QueueA a) :=
  tick >>
  let! s := force s in
  match s with
  | NilA =>
    let~ f' := rotateA f b (Thunk NilA) in
    ret (MkQueueA f' (Thunk NilA) f')
  | ConsA _ s' =>
    ret (MkQueueA f b s')
  end.

Definition pushA {a} (q : T (QueueA a)) (x : T a) : M (QueueA a) :=
  tick >>
  let! q := force q in
  mkQueueA (front q) (Thunk (ConsA x (back q))) (schedule q).

Definition popA {a} (q : T (QueueA a)) : M (option (T a * T (QueueA a))) :=
  tick >>
  let! q := force q in
  let! front_q := force (front q) in
  match front_q with
  | NilA => ret None
  | ConsA x f => let~ q := mkQueueA f (back q) (schedule q) in ret (Some (x, q))
  end.

(* TODO: following BankersQueue we can formalize the asymptotic complexity bounds.
   But how can we formalize the stronger non-asumptotic bounds? *)
