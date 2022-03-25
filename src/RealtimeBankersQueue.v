(** Real-time Banker's Queue *)

(** Operations take non-amortized constant time. *)

(* TODO: following BankersQueue we can formalize the amortized complexity bounds.
   But how can we formalize the stronger non-amortized bounds? *)

From Coq Require Import List.
From Clairvoyance Require Import Core Approx ApproxM List Misc BankersQueue.

Import ListNotations.
Import RevCompare.

Set Primitive Projections.
Set Implicit Arguments.
Set Contextual Implicit.
Set Maximal Implicit Insertion.

Record Queue (a : Type) : Type := MkQueue
  { front : list a
  ; back : list a
  ; schedule : list a
  }.

(* rotate x y z = x ++ rev y ++ z *)
(* Assumes 1 + length f = length b *)
Fixpoint rotate {a} (f b d : list a) : list a :=
  match f, b with
  | [], y :: _ => y :: d
  | x :: f, y :: b => x :: rotate f b (y :: d)
  | _, [] => []  (* Should never happen *)
  end.

Definition mkQueue {a} (f b s : list a) : Queue a :=
  match s with
  | [] => let f := rotate f b [] in MkQueue f [] f
  | _ :: s => MkQueue f b s
  end.

Definition push {a} (q : Queue a) (x : a) : Queue a :=
  mkQueue (front q) (x :: back q) (schedule q).

Definition pop {a} (q : Queue a) : option (a * Queue a) :=
  match front q with
  | [] => None
  | x :: f => Some (x, mkQueue f (back q) (schedule q))
  end.

Record QueueA (a : Type) : Type := MkQueueA
  { frontA : T (listA a)
  ; backA : T (listA a)
  ; scheduleA : T (listA a) }.

Definition emptyA {a : Type} : QueueA a := let n := Thunk NilA in MkQueueA n n n.

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
  mkQueueA (frontA q) (Thunk (ConsA x (backA q))) (scheduleA q).

Definition popA {a} (q : T (QueueA a)) : M (option (T a * T (QueueA a))) :=
  tick >>
  let! q := force q in
  let! front_q := force (frontA q) in
  match front_q with
  | NilA => ret None
  | ConsA x f => let~ q := mkQueueA f (backA q) (scheduleA q) in ret (Some (x, q))
  end.

Import Tick.Notations.

Definition headX {a} (xs : T (listA a)) : T a :=
  match xs with
  | Thunk (ConsA x _) => x
  | _ => Undefined
  end.

Fixpoint rotateD {a} (f b d : list a) (out : listA a)
  : Tick (T (listA a) * T (listA a) * T (listA a)) :=
  Tick.tick >>
  match f, b, out with
  | [], _ :: _, ConsA y' d' => Tick.ret (Thunk NilA, Thunk (ConsA y' Undefined), d')
  | x :: f, y :: b, ConsA x' r' =>
    let+ (f', b', d') := thunkD (rotateD f b (y :: d)) r' in
    Tick.ret (Thunk (ConsA x' f'), Thunk (ConsA (headX d') b'), tailX d')
  | _, [], _ | _, _, NilA => bottom (* Should not happen *)
  end.

Definition mkQueueD {a} (f b s : list a) (out : QueueA a)
  : Tick (T (listA a) * T (listA a) * T (listA a)) :=
  Tick.tick >>
  match s with
  | [] =>
    let f' := lub (frontA out) (scheduleA out) in
    let+ (f', b', _) := thunkD (rotateD f b []) f' in
    Tick.ret (f', b', Thunk NilA)
  | _ :: _ => Tick.ret (frontA out, backA out, Thunk (ConsA Undefined (scheduleA out)))
  end.

Definition pushD {a} (q : Queue a) (x : a) (out : QueueA a) : Tick (T (QueueA a) * T a) :=
  Tick.tick >>
  let+ (f, b, d) := mkQueueD (front q) (x :: back q) (schedule q) out in
  Tick.ret (Thunk (MkQueueA f (tailX b) d), headX b).

Definition popD {a} (q : Queue a) (out : option (T (QueueA a) * T a)) : Tick (T (QueueA a)) :=
  Tick.tick >>
  match front q with
  | [] => Tick.ret (Thunk (MkQueueA (Thunk NilA) Undefined Undefined))
  | x :: f =>
    match out with
    | Some (qout, xout) =>
      let+ (f', b', s') := thunkD (mkQueueD f (back q) (schedule q)) qout in
      Tick.ret (Thunk (MkQueueA (Thunk (ConsA xout f')) b' s'))
    | None => bottom
    end
  end.
