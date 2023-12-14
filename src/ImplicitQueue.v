From Clairvoyance Require Import Core Approx Tick.

Import Tick.Notations.

Set Implicit Arguments.
Set Contextual Implicit.
Set Maximal Implicit Insertion.

Definition factorPairD (A B : Type) (p : T (A * B)) : T A * T B :=
  match p with
  | Undefined => (Undefined, Undefined)
  | Thunk (x, y) => (Thunk x, Thunk y)
  end.

Definition unfactorPairD (A B : Type) (p : T A) (q : T B) : T (A * B) :=
  match p, q with
  | Thunk x, Thunk y => Thunk (x, y)
  | _, _ => Undefined
  end.

Inductive Front (A : Type) : Type :=
| FOne : A -> Front A
| FTwo : A -> A -> Front A.

Inductive FrontA (A : Type) : Type :=
| FOneA : T A -> FrontA A
| FTwoA : T A -> T A -> FrontA A.

#[global]
Instance Exact_Front (A : Type) : Exact (Front A) (FrontA A) :=
  fun u => match u with
           | FOne x => FOneA (Thunk x)
           | FTwo x y => FTwoA (Thunk x) (Thunk y)
           end.

Inductive Rear (A : Type) : Type :=
| RZero : Rear A
| ROne : A -> Rear A.

Inductive RearA (A : Type) : Type :=
| RZeroA : RearA A
| ROneA : T A -> RearA A.

#[global]
Instance Exact_Rear (A : Type) : Exact (Rear A) (RearA A) :=
  fun u => match u with
           | RZero => RZeroA
           | ROne x => ROneA (Thunk x)
           end.

Inductive Queue (A : Type) : Type :=
| Nil : Queue A
| Deep : Front A -> Queue (A * A) -> Rear A -> Queue A.

Inductive QueueA (A : Type) : Type :=
| NilA : QueueA A
| DeepA : T (FrontA A) -> T (QueueA (A * A)) -> T (RearA A) -> QueueA A.

Fixpoint push (A : Type) (q : Queue A) (x : A) : Queue A :=
  match q with
  | Nil => Deep (FOne x) Nil RZero
  | Deep f q RZero => Deep f q (ROne x)
  | Deep f q (ROne y) => Deep f (push q (y, x)) RZero
  end.

Fixpoint pushD (A : Type) (q : Queue A) (x : A) (outD : QueueA A) : Tick (T (QueueA A) * T A) :=
  Tick.tick >>
    match q with
    | Nil => match outD with
             | DeepA (Thunk (FOneA xD)) (Thunk NilA) (Thunk RZeroA) => Tick.ret (Thunk NilA, xD)
             | _ => bottom
             end
    | Deep f q RZero => match outD with
                        | DeepA fD qD (Thunk (ROneA xD)) => Tick.ret (Thunk (DeepA fD qD (Thunk RZeroA)), xD)
                        | _ => bottom
                        end
    | Deep f q (ROne y) => match outD with
                           | DeepA fD qD (Thunk RZeroA) =>
                               let+ (qD, pD) := thunkD (pushD q (y, x)) qD in
                               let (yD, xD) := factorPairD pD
                               in Tick.ret (Thunk (DeepA fD qD (Thunk (ROneA yD))), xD)
                           | _ => bottom
                           end
    end.

Fixpoint pop (A : Type) (q : Queue A) : option (A * Queue A) :=
  match q with
  | Nil => None
  | Deep (FTwo x y) q r => Some (x, Deep (FOne y) q r)
  | Deep (FOne x) q r => let q' := match r with
                                   | RZero => Nil
                                   | ROne y => Deep (FOne y) Nil RZero
                                   end
                         in let q'' := match pop q with
                                       | Some ((y, z), q) => Deep (FTwo y z) q r
                                       | None => q'
                                       end
                            in Some (x, q'')
  end.

Fixpoint popD (A : Type) (q : Queue A) (outD : option (T A * T (QueueA A))) : Tick (T (QueueA A)) :=
  Tick.tick >>
    match q with
    | Nil => match outD with
             | None => Tick.ret (Thunk NilA)
             | _ => bottom
             end
    | Deep (FTwo _ _) _ _ => match outD with
                             | Some (xA, Thunk (DeepA (Thunk (FOneA yA)) qA rA)) =>
                                 Tick.ret (Thunk (DeepA (Thunk (FTwoA xA yA)) qA rA))
                             | _ => Tick.ret bottom
                             end
    | Deep (FOne _) q _ => match outD with
                           | Some (xD, Thunk NilA) =>
                               (* `pop q` is `None`, `r` is `RZero` *)
                               Tick.ret (Thunk (DeepA (Thunk (FOneA xD)) (Thunk NilA) (Thunk RZeroA)))
                           | Some (xD, Thunk (DeepA (Thunk (FOneA yD)) (Thunk NilA) (Thunk RZeroA))) =>
                               (* `pop q` is `None`, `r` is `ROne y` *)
                               Tick.ret (Thunk (DeepA (Thunk (FOneA xD)) (Thunk NilA) (Thunk (ROneA yD))))
                           | Some (xD, Thunk (DeepA (Thunk (FTwoA yD zD)) qD rD)) =>
                               (* `pop q` is `Some ((y, z), q)` *)
                               let+ qD := popD q (Some (unfactorPairD yD zD, qD)) in
                               Tick.ret (Thunk (DeepA (Thunk (FOneA xD)) qD rD))
                           | _ => bottom
                           end
    end.
