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

Section FTD.

Notation U := Undefined.

Definition emptyD {a} : Tick (SeqA a) := Tick.tick >> Tick.ret Nil.

Fixpoint consD {a b} (x : a) (s : Seq a) (sA : SeqA b) : Tick (T b * T (SeqA b)) :=
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
        let+ zwq' := thunkD (consD (FT.Pair z w) q) rA in
        let (xA, yA) := match xy' with Thunk (Two xA yA) => (xA, yA) | _ => bottom end in
        let qA := snd zwq' in
        let (zA, wA) := match fst zwq' with Thunk (Pair zA wA) => (zA, wA) | _ => bottom end in
        Tick.ret (xA, Thunk (More (Thunk (Three yA zA wA)) qA uA))
      | _ => bottom
      end
    end
  end.

Definition tailD_ {a b} (more0D : _) (s : Seq a) (rA : SeqA b) : Tick (T (SeqA b)) :=
  Tick.tick >>
  match s with
  | FT.Nil => Tick.ret (Thunk Nil)
  | FT.Unit x => Tick.ret (Thunk (Unit bottom))
  | FT.More (FT.One x) q u =>
    let+ (qA, uA) := more0D q u rA in
    Tick.ret (Thunk (More (Thunk (One bottom)) qA uA))
  | FT.More (FT.Two x y) q u =>
    match rA with
    | More T_One_y  qA uA =>
      let yA := match T_One_y with Thunk (One yA) => yA | _ => bottom end in
      Tick.ret (Thunk (More (Thunk (Two bottom yA)) qA uA))
    | _ => bottom
    end
  | FT.More (FT.Three x y z) q u =>
    match rA with
    | More T_Two_yz qA uA =>
      let '(yA, zA) :=
        match T_Two_yz with
        | Thunk (Two yA zA) => (yA, zA)
        | _ => bottom
        end
      in Tick.ret (Thunk (More (Thunk (Three bottom yA zA)) qA uA))
    | _ => bottom
    end
  end.

Definition map1D {a b} (fD : a -> b -> Tick (T b)) (s : Seq a) (rA : SeqA b) : Tick (T (SeqA b)) :=
  match s with
  | FT.Nil => Tick.ret (Thunk Nil)
  | FT.Unit x =>
    match rA with
    | Unit (Thunk fxA) =>
      let+ xA := fD x fxA in
      Tick.ret (Thunk (Unit xA))
    | _ => bottom
    end
  | FT.More (FT.One x) q u =>
    match rA with
    | More One_fx qA uA =>
      let+ xA := match One_fx with Thunk (One (Thunk fxA)) => fD x fxA | _ => bottom end in
      Tick.ret (Thunk (More (Thunk (One xA)) qA uA))
    | _ => bottom
    end
  | FT.More (FT.Two x y) q u =>
    match rA with
    | More Two_fx_y qA uA =>
      let+ (xA, yA) :=
        match Two_fx_y with
        | Thunk (Two fxA yA) =>
          let+ xA := match fxA with Thunk fxA => fD x fxA | _ => bottom end in
          Tick.ret (xA, yA)
        | _ => bottom
        end in
      Tick.ret (Thunk (More (Thunk (Two xA yA)) qA uA))
    | _ => bottom
    end
  | FT.More (FT.Three x y z) q u =>
    match rA with
    | More Three_fx_y_z qA uA =>
      let+ (xA, yA, zA) :=
        match Three_fx_y_z with
        | Thunk (Three fxA yA zA) =>
          let+ xA := match fxA with Thunk fxA => fD x fxA | _ => bottom end in
          Tick.ret (xA, yA, zA)
        | _ => bottom
        end in
      Tick.ret (Thunk (More (Thunk (Three xA yA zA)) qA uA))
    | _ => bottom
    end
  end%tick.

Definition chopD {a b} (x : Tuple a) (yA : TupleA b) : Tick (T (TupleA b)) :=
  match x with
  | FT.Triple _ y z =>
    match yA with
    | Pair yA zA => Tick.ret (Thunk (Triple U yA zA))
    | _ => bottom
    end
  | _ => Tick.ret (Thunk yA)
  end.

Fixpoint more0D {a b} (q : Seq (Tuple a)) (u : Crowd a) (rA : SeqA b) : Tick (T (SeqA (TupleA b)) * T (CrowdA b)) :=
  Tick.tick >>
  match q,u with
  | FT.Nil, FT.One y =>
    match rA with
    | Unit yA => Tick.ret (Thunk Nil, Thunk (One yA))
    | _ => bottom
    end
  | FT.Nil, FT.Two y z =>
    match rA with
    | More One_y _ One_z =>
      let yA := match One_y with Thunk (One yA) => yA | _ => U end in
      let zA := match One_z with Thunk (One zA) => zA | _ => U end in
      Tick.ret (Thunk Nil, Thunk (Two yA zA))
    | _ => bottom
    end
  | FT.Nil, FT.Three y z w =>
    match rA with
    | More One_y _ Two_zw =>
      let yA := match One_y with Thunk (One yA) => yA | _ => U end in
      let (zA, wA) := match Two_zw with Thunk (Two zA wA) => (zA, wA) | _ => bottom end in
      Tick.ret (Thunk Nil, Thunk (Three yA zA wA))
    | _ => bottom
    end
  | FT.Unit (FT.Pair x y), _ =>
    match rA with
    | More Two_xy tail_qA uA =>
      let '(xA, yA) := match Two_xy with Thunk (Two xA yA) => (xA, yA) | _ => bottom end in
      let qA := match tail_qA with Thunk t => tailD_ more0D q t | _ => bottom end in
      Tick.ret (Thunk (Unit (Thunk (Pair xA yA))), uA)
    | _ => bottom
    end
  | FT.More (FT.One (FT.Pair x y)) q1 u1, _ =>
    match rA with
    | More Two_xy tail_qA uA =>
      let '(xA, yA) := match Two_xy with Thunk (Two xA yA) => (xA, yA) | _ => bottom end in
      let qA := match tail_qA with Thunk t => tailD_ more0D q t | _ => bottom end in
      Tick.ret (Thunk (More (Thunk (One (Thunk (Pair xA yA)))) U U), uA)
    | _ => bottom
    end
  | FT.More (FT.Two (FT.Pair x y) _) _ _, _ =>
    match rA with
    | More Two_xy tail_qA uA =>
      let '(xA, yA) := match Two_xy with Thunk (Two xA yA) => (xA, yA) | _ => bottom end in
      let qA := match tail_qA with Thunk t => tailD_ more0D q t | _ => bottom end in
      Tick.ret (Thunk (More (Thunk (Two (Thunk (Pair xA yA)) U)) U U), uA)
    | _ => bottom
    end
  | FT.More (FT.Three (FT.Pair x y) _ _) _ _, _ =>
    match rA with
    | More Two_xy tail_qA uA =>
      let '(xA, yA) := match Two_xy with Thunk (Two xA yA) => (xA, yA) | _ => bottom end in
      let qA := match tail_qA with Thunk t => tailD_ more0D q t | _ => bottom end in
      Tick.ret (Thunk (More (Thunk (Three (Thunk (Pair xA yA)) U U)) U U), uA)
    | _ => bottom
    end
  | FT.Unit (FT.Triple x _ _), _ =>
    match rA with
    | More One_x map1_chop_q uA =>
      let xA := match One_x with Thunk (One xA) => xA | _ => bottom end in
      let qA := match map1_chop_q with Thunk t => map1D chopD q t | _ => bottom end in
      Tick.ret (Thunk (Unit (Thunk (Triple xA U U))), uA)
    | _ => bottom
    end
  | FT.More (FT.One (FT.Triple x _ _)) _ _, _ =>
    match rA with
    | More One_x map1_chop_q uA =>
      let xA := match One_x with Thunk (One xA) => xA | _ => bottom end in
      let qA := match map1_chop_q with Thunk t => map1D chopD q t | _ => bottom end in
      Tick.ret (Thunk (More (Thunk (One (Thunk (Triple xA U U)))) U U), uA)
    | _ => bottom
    end
  | FT.More (FT.Two (FT.Triple x _ _) _) _ _, _ =>
    match rA with
    | More One_x map1_chop_q uA =>
      let xA := match One_x with Thunk (One xA) => xA | _ => bottom end in
      let qA := match map1_chop_q with Thunk t => map1D chopD q t | _ => bottom end in
      Tick.ret (Thunk (More (Thunk (Two (Thunk (Triple xA U U)) U)) U U), uA)
    | _ => bottom
    end
  | FT.More (FT.Three (FT.Triple x _ _) _ _) _ _, _ =>
    match rA with
    | More One_x map1_chop_q uA =>
      let xA := match One_x with Thunk (One xA) => xA | _ => bottom end in
      let qA := match map1_chop_q with Thunk t => map1D chopD q t | _ => bottom end in
      Tick.ret (Thunk (More (Thunk (Three (Thunk (Triple xA U U)) U U)) U U), uA)
    | _ => bottom
    end
  end.

Definition tailD {a b} (s : Seq a) (rA : SeqA b) : Tick (T (SeqA b)) :=
  tailD_ more0D s rA.

Inductive LessDefined_TupleA {a} `{LessDefined a} : LessDefined (TupleA a) :=
| less_defined_Pair {x x' y y'} : x `less_defined` x' -> y `less_defined` y' -> Pair x y `less_defined` Pair x' y'
| less_defined_Triple {x x' y y' z z'} : x `less_defined` x' -> y `less_defined` y' -> z `less_defined` z' -> Triple x y z `less_defined` Triple x' y' z'
.
Existing Instance LessDefined_TupleA.

Inductive LessDefined_CrowdA {a} `{LessDefined a} : LessDefined (CrowdA a) :=
.
Existing Instance LessDefined_CrowdA.

Inductive LessDefined_SeqA {a} `{LessDefined a} : LessDefined (SeqA a) :=
| less_defined_Nil : Nil `less_defined` Nil
| less_defined_Unit {x x'} : x `less_defined` x' -> Unit x `less_defined` Unit x'
| less_defined_More {x x' y y' z z'} : x `less_defined` x' -> y `less_defined` y' -> z `less_defined` z' -> More x y z `less_defined` More x' y' z'
.
Existing Instance LessDefined_SeqA.

Definition exact_CrowdA {a b} `{Exact a b} : Exact (Crowd a) (CrowdA b).
Admitted.
Existing Instance exact_CrowdA.

Definition exact_TupleA {a b} `{Exact a b} : Exact (Tuple a) (TupleA b).
Admitted.
Existing Instance exact_TupleA.

Definition exact_SeqA {a b} `{Exact a b} : Exact (Seq a) (SeqA b) :=
  (fix exact_ {a b} `{Exact a b} (s : Seq a) : SeqA b :=
    let _ : Exact (Seq (Tuple a)) (SeqA (TupleA b)) := exact_ in
    match s with
    | FT.Nil => Nil
    | FT.Unit x => Unit (exact x)
    | FT.More x y z => More (exact x) (exact y) (exact z)
    end) _ _ _.
Existing Instance exact_SeqA.

(** Functional correctness *)
Lemma consD_fun : forall {a b} `{Exact a b, LessDefined b},
  forall (x : a) s (sA : SeqA b),
  sA `less_defined` exact (FT.cons x s) ->
  Tick.val (consD x s sA) `less_defined` exact (x, s).
Admitted.

End FTD.
