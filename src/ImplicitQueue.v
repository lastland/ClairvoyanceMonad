From Clairvoyance Require Import Core Approx Tick.

Import Tick.Notations.

Set Implicit Arguments.
Set Contextual Implicit.
Set Maximal Implicit Insertion.

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

Definition pairD (A B : Type) (p : T (A * B)) : T A * T B :=
  match p with
  | Undefined => (Undefined, Undefined)
  | Thunk (x, y) => (Thunk x, Thunk y)
  end.

Fixpoint pushD (A : Type) (q : Queue A) (x : A) (outD : QueueA A) : Tick (T (QueueA A) * T A) :=
  Tick.tick >>
    match q with
    | Nil => Tick.ret (Thunk NilA, Thunk x)
    | Deep f q RZero => match outD with
                        | DeepA fA qA (Thunk (ROneA xA)) => Tick.ret (Thunk (DeepA fA qA (Thunk RZeroA)), xA)
                        | _ => bottom
                        end
    | Deep f q (ROne y) => match outD with
                           | DeepA fA qA (Thunk RZeroA) => let+ (qD, pD) := thunkD (pushD q (y, x)) qA in
                                                           let (yD, xD) := pairD pD
                                                           in Tick.ret (Thunk (DeepA fA qD (Thunk (ROneA yD))), xD)
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


(* Fixpoint popD (A : Type) (q : Queue A) (outD : option (T A * T (QueueA A))) : Tick (T (QueueA A)) := *)
(*   Tick.tick >> *)
(*     match q with *)
(*     | Nil => Tick.ret (Thunk NilA) *)
(*     | Deep (FTwo _ _) _ _ => match outD with *)
(*                              | Some (xA, Thunk (DeepA (Thunk (FOneA yA)) qA rA)) => *)
(*                                  Tick.ret (Thunk (DeepA (Thunk (FTwoA xA yA)) qA rA)) *)
(*                              | _ => Tick.ret bottom *)
(*                              end *)
(*     | Deep (FOne _) q _ => match outD with *)
(*                            | Some (xA, Thunk (DeepA (Thunk (FTwoA yA zA)) qA rA)) => *)
(*                                      let+ rD := thunkD (popD q) qA in *)
(*                                      let q' := thunkD (fun r => match r with *)
(*                                                                 | RZeroA => Nil *)
(*                                                                 | ROneA _ => Nil *)
(*                                                                 end) rD *)
(*                                        (* match rD with *) *)
(*                                        (*         | Undefined => Tick.ret bottom *) *)
(*                                        (*         | _ => Tick.ret bottom *) *)
(*                                        (*         end *) *)
(*                                      in Tick.ret bottom *)
(*                            | _ => Tick.ret bottom *)
(*                            end *)
(*     end. *)


        (* let+ qD := thunkD (popD q) *)
    (* end. *)

                         (*               let q' := match pop q with *)
                         (*           | Some ((y, z), q) => Deep (FTwo y z) q r *)
                         (*           | None => match r with *)
                         (*                     | RZero => Nil *)
                         (*                     | ROne y => Deep (FOne y) Nil RZero *)
                         (*                     end *)
                         (*           end *)
                         (* in Some (x, q') *)
