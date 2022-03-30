(** Real-time Banker's Queue *)

(** Operations take non-amortized constant time. *)

(* TODO: following BankersQueue we can formalize the amortized complexity bounds.
   But how can we formalize the stronger non-amortized bounds? *)

From Coq Require Import List.
From Clairvoyance Require Import Core Approx ApproxM List Misc BankersQueue.
From Clairvoyance Require Launchbury.

Import ListNotations.
Import RevCompare.

Set Primitive Projections.
Set Implicit Arguments.
Set Contextual Implicit.
Set Maximal Implicit Insertion.

#[local] Existing Instance Exact_id | 1.
#[local] Existing Instance LessDefined_id | 100.
#[local] Existing Instance PreOrder_LessDefined_id | 100.
#[local] Existing Instance ExactMaximal_id | 100.

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

#[global] Instance Exact_Queue {a aA} `{Exact a aA} : Exact (Queue a) (QueueA aA) :=
  fun q => MkQueueA (exact (front q)) (exact (back q)) (exact (schedule q)).

Record less_defined_QueueA {a} `{LessDefined a} (q1 q2 : QueueA a) : Prop :=
  { ld_frontA : frontA q1 `less_defined` frontA q2
  ; ld_backA : backA q1 `less_defined` backA q2
  ; ld_scheduleA : scheduleA q1 `less_defined` scheduleA q2
  }.

#[global] Instance LessDefined_QueueA {a} `{LessDefined a} : LessDefined (QueueA a) :=
  less_defined_QueueA.

Lemma pushD_spec {a} (q : Queue a) (x : a) (outD : QueueA a)
  : outD `is_approx` push q x ->
    forall qD xD dcost, Tick.MkTick dcost (qD, xD) = pushD q x outD ->
    pushA qD xD {{ fun out cost => outD `less_defined` out /\ cost <= dcost }}.
Proof.
Admitted.

Lemma pushD_lowspec {a} (q : Queue a) (x : a) (outD : QueueA a)
  : outD `is_approx` push q x ->
    forall qD xD dcost, Tick.MkTick dcost (qD, xD) = pushD q x outD ->
    pushA qD xD [[ fun out cost => outD `less_defined` out -> dcost <= cost ]].
Proof.
Admitted.

Import Clairvoyance.Launchbury.
Import L.Notations.

Record QueueF (t : Type -> Type) (_list : Type) (_Q : Type) : Type := MkQueueF
  { frontF : t _list
  ; backF : t _list
  ; scheduleF : t _list
  }.

#[global] Instance Data_QueueA {a} : Data (QueueF T (listA a)) :=
  {| d_ := QueueA a
  ;  des := fun q => {| frontF := frontA q ; backF := backA q ; scheduleF := scheduleA q |}
  ;  con := fun q => {| frontA := frontF q ; backA := backF q ; scheduleA := scheduleF q |}
  |}.

Section F.
Context {t a} {list_ : Data (listF t a)} {Queue_ : Data (QueueF t list_)}.

Definition emptyF : L t Queue_ :=
  let^~ f := L.ret (con NilF) in
  L.ret (con {| frontF := f ; backF := f ; scheduleF := f |}).

CoFixpoint rotateF (f b d : t list_) : L t list_ :=
  let^ f := L.force f in
  let^ b := L.force b in
  match des f, des b with
  | NilF, ConsF y _ => L.ret (con (ConsF y d))
  | ConsF x f, ConsF y b =>
    let^~ d := L.ret (con (ConsF y d)) in
    let^~ r := rotateF f b d in
    L.ret (con (ConsF x r))
  | _, _ => L.ret (con NilF) (* should not happen *)
  end.

Definition mkQueueF (f b s : t list_) : L t Queue_ :=
  let^ _ := L.tick in
  let^ s := L.force s in
  match des s with
  | NilF =>
    let^~ z := L.ret (con NilF) in
    let^~ f := rotateF f b z in
    L.ret (con (MkQueueF f z f))
  | ConsF _ s' => L.ret (con (MkQueueF f b s'))
  end.

Definition pushF (q : t Queue_) (x : t a) : L t Queue_ :=
  let^ _ := L.tick in
  let^ q := L.force q in
  let q := des q in
  let^~ b := L.ret (con (ConsF x (backF q))) in
  mkQueueF (frontF q) b (scheduleF q).

Definition popF (q : t Queue_) : L t (option (t a * t Queue_)) :=
  let^ _ := L.tick in
  let^ q := L.force q in
  let q := des q in
  let^ f := L.force (frontF q) in
  match des f with
  | NilF => L.ret None
  | ConsF x f =>
    let^~ q := mkQueueF f (backF q) (scheduleF q) in
    L.ret (Some (x, q))
  end.

End F.
