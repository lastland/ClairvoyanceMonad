From Coq Require Import List Arith Lia RelationClasses.
From Clairvoyance Require Import Core Approx ApproxM List Misc BankersQueue Tick.

Import ListNotations.

From Clairvoyance Require Import FingerTree FingerTreeM.

Set Primitive Projections.
Set Implicit Arguments.
Set Contextual Implicit.
Set Maximal Implicit Insertion.

Import Tick.Notations.

Module FT := FingerTree.

Definition emptyD {a} : Tick (SeqA a) := Tick.tick >> Tick.ret Nil.

Fixpoint consD_ {a b} (x : a) (s : Seq a) (sA : SeqA b) : Tick (T b * T (SeqA b)) :=
  Tick.tick >> 
  match s with 
  | FT.Nil => match sA with Unit xA => Tick.ret (xA, Thunk Nil) | _ => bottom end
  | FT.Unit y => match sA with
    | More x' _ y' =>
      Tick.ret (match x' with Thunk (One xA) => xA | _ => Undefined end,
                Thunk (Unit (match y' with Thunk (One yA) => yA | _ => Undefined end)))
    | _ => bottom
    end
  | FT.More c q u =>
    match c with
    | FT.One y => match sA with
      | More xy' qA uA =>
          let (xA, yA) := match xy' with Thunk (Two xA yA) => (xA, yA) | _ => bottom end in
          Tick.ret (xA, Thunk (More (Thunk (One yA)) qA uA))
      | _ => bottom
      end
    | FT.Two y z => match sA with
      | More xyz' qA uA =>
          let '(xA, yA, zA) := match xyz' with Thunk (Three xA yA zA) => (xA, yA, zA) | _ => bottom end in
          Tick.ret (xA, Thunk (More (Thunk (Two yA zA)) qA uA))
      | _ => bottom
      end
    | FT.Three y z w => match sA with
      | More xy' rA uA =>
        let+ zwq' := thunkD (consD_ (FT.Pair z w) q) rA in
        let (xA, yA) := match xy' with Thunk (Two xA yA) => (xA, yA) | _ => bottom end in
        let qA := snd zwq' in
        let (zA, wA) := match fst zwq' with Thunk (Pair zA wA) => (zA, wA) | _ => bottom end in
        Tick.ret (xA, Thunk (More (Thunk (Three yA zA wA)) qA uA))
      | _ => bottom
      end
    end
  end.
