From Clairvoyance Require Import Core Approx Tick.

Import Tick.Notations.

Set Implicit Arguments.
Set Contextual Implicit.
Set Maximal Implicit Insertion.

Inductive Front (A : Type) : Type :=
| FOne : A -> Front A
| FTwo : A -> A -> Front A.

Inductive Rear (A : Type) : Type :=
| RZero : Rear A
| ROne : A -> Rear A.

Inductive Queue (A : Type) : Type :=
| Nil  : Queue A
| Deep : Front A -> Queue (A * A) -> Rear A -> Queue A.

Fixpoint push (A : Type) (q : Queue A) (x : A) : Queue A :=
  match q with
  | Nil => Deep (FOne x) Nil RZero
  | Deep f q RZero => Deep f q (ROne x)
  | Deep f q (ROne y) => Deep f (push q (x, y)) RZero
  end.

Fixpoint pop (A : Type) (q : Queue A) : option (A * Queue A) :=
  match q with
  | Nil => None
  | Deep (FTwo x y) q r => Some (x, Deep (FOne y) q r)
  | Deep (FOne x) q r => Some (x, match pop q with
                                  | Some ((y, z), q) => Deep (FTwo y z) q r
                                  | None => match r with
                                            | RZero => Nil
                                            | ROne y => Deep (FOne y) Nil RZero
                                            end
                                  end)
  end.

Inductive QueueA (A : Type) : Type :=
| NilA : QueueA A
| DeepA : Front A -> T (QueueA (A * A)) -> Rear A -> QueueA A.

#[global]
Instance Exact_Queue : forall (A : Type), Exact (Queue A) (QueueA A) :=
  fix Exact_Queue _ q := match q with
                         | Nil => NilA
                         | Deep f q r => DeepA f (Thunk (Exact_Queue _ q)) r
                         end.

Fixpoint pushD (A : Type) (q : Queue A) (x : A) (outD : QueueA A) : Tick (T (QueueA A)) :=
  match q with
  | Nil => Tick.ret (Thunk (DeepA (FOne x) (Thunk NilA) RZero))
  | Deep f q RZero => match outD with
                      | DeepA _ qA _ => Tick.ret (Thunk (DeepA f qA (ROne x)))
                      | _ => bottom
                      end
  | Deep f q (ROne y) => match outD with
                         | DeepA _ qA _ => let+ qD := thunkD (pushD q (x, y)) qA in
                                           Tick.ret (Thunk (DeepA f qD RZero))
                         | _ => bottom
                         end
  end.
