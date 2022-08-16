From Coq Require Import List Arith Lia RelationClasses.
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

Variant Crowd (a: Type) : Type :=
  | One : a -> Crowd a 
  | Two : a -> a -> Crowd a 
  | Three : a -> a -> a -> Crowd a 
.

Variant Tuple (a: Type) : Type :=
  | Pair : a -> a -> Tuple a 
  | Triple : a -> a -> a -> Tuple a.

Inductive Seq (a : Type) : Type := 
  | Nil : Seq a
  | Unit : a -> Seq a 
  | More : Crowd a -> Seq (Tuple a) -> Crowd a -> Seq a.

Definition Crowd_toList {a:Type} (c : Crowd a) : list a :=
match c with
 | (One x) => [x]
 | (Two x y) => [x; y]
 | (Three x y z) => [x;y;z]
end.

Fixpoint cons {a : Type} (x : a) (s : Seq a) : Seq a :=
  match s with 
  | Nil => Unit x
  | Unit y => More (One x) Nil (One y)
  | (More (One y) q u) => More (Two x y) q u
  | (More (Two y z) q u) => More (Three x y z) q u
  | (More (Three y z w) q u) =>
    More (Two x y) (cons (Pair z w) q) u
end.

Fixpoint snoc {a: Type} (s: Seq a) (x:a) : Seq a := 
 match s with 
   | Nil => Unit x
   | (Unit y) => More (One y) Nil (One x)
   | (More u q (One y)) => More u q (Two y x) 
   | (More u q (Two y z)) => More u q (Three y z x)
   | (More u q (Three y z w)) =>
   More u (snoc q (Pair z w)) (Two y x)
end.

Definition chop {a:Type} ( x: Tuple a) : Tuple a :=
  match x with 
  | Triple _ y z => Pair y z
  | _ => x
  end.

Definition head {a:Type} (t: Seq a) : option a :=
  match t with
  | Nil => None
  | (Unit x) => Some x
  | (More (One x) _ _ ) => Some x
  | (More (Two x _) _ _) => Some x
  | (More (Three x _ _) _ _) => Some x
  end.

Fixpoint map1 {a:Type} (f : a -> a) (s : Seq a) : Seq a :=
  match s with
  | Nil => Nil
  | (Unit x) => Unit (f x)
  | (More (One x) q u) => More (One (f x)) q u
  | (More (Two x y) q u) => More (Two (f x) y) q u
  | (More (Three x y z) q u) => More (Three (f x) y z) q u 
  end.

Fixpoint more0 {a:Type} (q: Seq (Tuple a)) (u: Crowd a) : Seq a := 
  match (q,u) with 
   | (Nil, (One y)) => Unit y
   | (Nil, (Two y z)) => More (One y) Nil (One z)
   | (Nil, (Three y z w)) => More (One y) Nil (Two z w)
   | (Unit (Pair x y), _) => More (Two x y) Nil u
   | (More (One (Pair x y)) _ _, _) => More (Two x y) Nil u
   | (More (Two (Pair x y) _) _ _, _) => More (Two x y) Nil u
   | (More (Three (Pair x y) _ _) _ _, _) => More (Two x y) Nil u
   | (Unit (Triple x _ _), _) => More (One x) (map1 chop q) u
   | (More (One (Triple x _ _)) _ _, _) => More (One x) (map1 chop q) u
   | (More (Two (Triple x _ _) _) _ _, _) => More (One x) (map1 chop q) u
   | (More (Three (Triple x _ _) _ _) _ _, _) => More (One x) (map1 chop q)u 
   end.

Fixpoint toTuples {a:Type} (la : list a) : list (Tuple a) := 
  match la with
    | [] => []
    | [x] => [] (* extra *)
    | [x ; y] => [Pair x y ]
    | [x ; y; z; w] => [Pair x y; Pair z w]
    | (x :: y :: z :: xs) => Triple x y z :: toTuples xs
  end.


Fixpoint glue {a:Type} (q1 : Seq a) (la: list a) (q2: Seq a) : Seq a :=
  match (q1,q2) with 
  | (Nil,_) => List.fold_right cons q2 la
  | (_,Nil) => List.fold_left snoc la q1
  | (Unit x, _) => List.fold_right cons q2 (x :: la)
  | (_, Unit y) => List.fold_left snoc (la ++ [y]) q1
  | (More u1 q1 v1, More u2 q2 v2) =>
      More u1 (glue q1 (toTuples (Crowd_toList v1 ++ la ++ Crowd_toList u2)) q2) v2
  end.

Definition append {a:Type} (q1 : Seq a) (q2 : Seq a) : Seq a :=
    glue q1 nil q2.

Fixpoint fromTuples {a:Type} (lta : list (Tuple a)) : list a :=
  match lta with 
  | [] => []
  | [Pair x y] => [x;y]
  | [Pair x y; Pair z w] => [x; y; z; w]
  | (Pair x y :: xs) => [x; y] ++ fromTuples xs  (* extra *)
  | (Triple x y z :: xs) => [x; y; z] ++ fromTuples xs
  end.

