From Coq Require Import List Arith Psatz.

From Clairvoyance Require Import Core Approx List ListA Tick.

Import ListNotations.
Import Tick.Notations.

(* Now, what if we did the same but with mergesort *)

(* MergeSort and its attendent functions as given by Software Foundations *) 

Fixpoint split {X:Type} (l:list X) : (list X * list X) :=
  match l with
  | [] => ([],[])
  | [x] => ([x],[])
  | x1 :: x2 :: l' =>
    let (l1,l2) := split l' in
    (x1 :: l1, x2 :: l2)
  end.

Fixpoint merge l1 l2 n :=
  match l1, l2, n with
  | _, _, 0 => []
  | [], _, _ => l2
  | _, [], _ => l1
  | a1::l1', a2::l2', S n =>
      if a1 <=? a2 then a1 :: merge l1' l2 n else a2 :: merge l1 l2' n
  end.

(* We swapped this to use fuel instead of well-founded induction *)
Fixpoint mergesort' (l: list nat) (n : nat) : list nat :=
  match n, l with
  | 0, _ => [] (* Ran out of fuel *)
  | _, [] => []
  | _, [x] => [x]
  | S n, _ => let (l1,l2) := split l in 
              merge (mergesort' l1 n) (mergesort' l2 n) (length l)
  end.

Definition mergesort (l : list nat) : list nat :=
  mergesort' l (length l).

(* Demand functions for split/merge/mergesort *)

Definition thunkTupleD {a b} `{Bottom b} (f : a * a -> b) (x : T a * T a) (p : a) : b :=
  match x with
  | (Thunk x1, Thunk x2) => f (x1, x2)
  | (Thunk x1, Undefined) => f (x1, p)
  | (Undefined, Thunk x2) => f (p, x2)
  | (Undefined, Undefined) => bottom
  end.

Fixpoint splitD {a : Type} (xs : list a) (outD : listA a * listA a) : Tick (T (listA a)) :=
  Tick.tick >>
  match xs, outD with
  | [], _ => Tick.ret (Thunk NilA)
  | [x], _ => Tick.ret (Thunk (ConsA (Thunk x) (Thunk NilA)))
  | x :: x' :: xs, (ConsA zD zsD, ConsA zD' zsD') =>
    Tick.tick >>
    let+ xsD := thunkTupleD (splitD xs) (zsD, zsD') (ConsA Undefined Undefined) in
    Tick.ret (Thunk (ConsA zD (Thunk (ConsA zD' xsD))))
  | _, _ => bottom
  end.

(* Compute splitD [1;2;3;4;5;6;7;8] (exact [1;3;5;7], exact [2;4;6;8]). *)

Fixpoint mergeD (xs ys : list nat) (outD : listA nat) : Tick (T (listA nat) * T (listA nat)) :=
  Tick.tick >>
  match xs, ys, outD with
  | [], _, _ => Tick.ret (Thunk NilA, Undefined)
  | _, [], _ => Tick.ret (Undefined, Thunk NilA)
  | x :: xs, y :: ys, ConsA zD (Thunk (ConsA zD' zsD)) =>
    Tick.tick >>
    let+ (xsD, ysD) := thunkD (mergeD xs ys) zsD in
    Tick.ret (Thunk (ConsA zD xsD), Thunk (ConsA zD' ysD))
  | _, _, _ => bottom
  end.

Fixpoint mergesortD' (l : list nat) (n : nat) (outD : listA nat) : Tick (T (listA nat)) :=
  Tick.tick >>
  match l, outD, n with
  | _, _, 0 => Tick.ret Undefined
  | [], _, _ => Tick.ret (Thunk NilA)
  | [x], _, _ => Tick.ret (Thunk (ConsA (Thunk x) (Thunk NilA)))
  | _ :: _, ConsA _ _, S n =>
    let (xs, ys) := split l in
    let+ (mxsD, mysD) := mergeD (mergesort xs) (mergesort ys) outD in
    let+ xsD := thunkD (mergesortD' xs n) mxsD in
    let+ ysD := thunkD (mergesortD' ys n) mysD in
    let+ lD := thunkTupleD (splitD l) (xsD, ysD) (ConsA Undefined Undefined) in
    Tick.ret lD
  | _, _, _ => bottom
  end.

Definition merge_sortD (l : list nat) (outD : listA nat) : Tick (T (listA nat)) :=
  mergesortD' l (length l) outD.

(* Long-term goal:
   show that   head (selection_sort xs)   in O(n)
   (also could be merge_sort) *)

