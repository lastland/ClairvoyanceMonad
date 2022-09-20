From Coq Require Import List Arith Lia RelationClasses.
From Clairvoyance Require Import Core Approx ApproxM List Misc BankersQueue.

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

(* Copied from list case study *)
Fixpoint foldrA_ {a b} (f : T a -> T b -> M b) (v : T b) (xs : listA a) : M b :=
  tick >>
  match xs with
  | NilA => force v
  | ConsA x xs => let~ t := foldrA_ f v $! xs in
                 f x t
  end.

Definition foldrA {a b} (f : T a -> T b -> M b) (v : T b) (xs : T (listA a)) : M b :=
  foldrA_ f v $! xs.


Fixpoint foldlA_ {a b} (f : T b -> T a -> M b) (v : T b) (xs : listA a) : M b :=
  tick >>
  match xs with
  | NilA => force v
  | ConsA x xs => let~ t := f v x in
                  foldlA_ f t $! xs
  end.

Definition foldlA {a b} (f : T b -> T a -> M b) (v : T b) (xs : T (listA a)) : M b :=
  foldlA_ f v $! xs.
(* ---- *)


Variant CrowdA (a: Type) : Type :=
  | One : T a -> CrowdA a 
  | Two : T a -> T a -> CrowdA a 
  | Three : T a -> T a -> T a -> CrowdA a 
.

Variant TupleA (a: Type) : Type :=
  | Pair : T a -> T a -> TupleA a 
  | Triple : T a -> T a -> T a -> TupleA a.

Inductive SeqA (a : Type) : Type := 
  | Nil : SeqA a
  | Unit : T a -> SeqA a 
  | More : T (CrowdA a) -> T (SeqA (TupleA a)) -> T (CrowdA a) -> SeqA a.


Fixpoint consA_ {a : Type} (x : T a) (s : SeqA a) : M (SeqA a) :=
  tick >> 
  match s with 
  | Nil => ret (Unit x)
  | Unit y => ret (More (Thunk (One x)) (Thunk Nil) (Thunk (One y)))
  | More c q u => 
    forcing c (fun c => 
    match c with 
    | One y => ret (More (Thunk (Two x y)) q u)
    | Two y z => ret (More (Thunk (Three x y z)) q u)
    | Three y z w => 
      forcing q (fun q =>
      let~ r := consA_ (Thunk (Pair z w)) q in
      ret (More (Thunk (Two x y)) r u))
    end)
  end.

Definition consA {a} (x : T a) (s : T (SeqA a)) : M (SeqA a) :=
  let! s := force s in
  consA_ x s.

Fixpoint snocA_ {a: Type} (s: SeqA a) (x:T a) : M (SeqA a) :=
 tick >>
 match s with 
   | Nil => ret (Unit x)
   | (Unit y) => ret (More (Thunk (One y)) (Thunk Nil) (Thunk (One x)))
   | (More u q c) => 
     forcing c (fun c => 
     match c with
   | (One y) => ret (More u q (Thunk (Two y x)))
   | (Two y z) => ret (More u q (Thunk (Three y z x)))
   | (Three y z w) => 
       forcing q (fun q => 
       let~ r := snocA_ q (Thunk (Pair z w)) in
       ret (More u r (Thunk (Two y x))))
     end)
end.

Definition snocA {a} (s : T (SeqA a)) (x : T a)  : M (SeqA a) :=
  let! s := force s in
  snocA_ s x.


Definition chopA {a:Type} ( x: T (TupleA a)) : M (TupleA a) :=
  tick >>
  forcing x (fun x => 
  match x with 
  | Triple _ y z => ret (Pair y z)
  | _ => ret x
  end).

Variant optionA (a:Type) : Type :=
  | NoneA : optionA a
  | SomeA : T a -> optionA a 
.

Definition headA {a:Type} (t: T (SeqA a)) : M (optionA a) :=
  tick >>
  forcing t (fun t => 
  match t with
  | Nil => ret NoneA
  | (Unit x) => ret (SomeA x)
  | (More c _ _) => 
      forcing c (fun c => 
      match c with
  | (One x) => ret (SomeA x)
  | (Two x _)  => ret (SomeA x)
  | (Three x _ _) => ret (SomeA x)
      end)
  end).

Definition map1 {a:Type} (f : T a -> M a) (s : SeqA a) : M (SeqA a) :=
  tick >>
  match s with
  | Nil => ret Nil
  | (Unit x) => 
      let~ g := f x in
      ret (Unit g)
  | (More c q u) => 
      forcing c (fun c => 
      match c with 
      | (One x) => 
          let~ g := f x in 
          ret (More (Thunk (One g)) q u)
      | (Two x y) => 
          let~ g := f x in
          ret (More (Thunk (Two g y)) q u)
      | (Three x y z) => 
          let~ g := f x in
          ret (More (Thunk (Three g y z)) q u)
      end)
  end.

Definition more0 {a:Type} (q: SeqA (TupleA a)) (u: CrowdA a) : M (SeqA a) :=
  tick >>
  match (q,u) with 
   | (Nil, (One y)) => ret (Unit y)
   | (Nil, (Two y z)) => ret (More (Thunk (One y)) (Thunk Nil) (Thunk (One z)))
   | (Nil, (Three y z w)) => ret (More (Thunk (One y)) (Thunk Nil) (Thunk (Two z w)))
   | (Unit t, _) => 
       forcing t (fun t => 
       match t with 
       | (Pair x y) => 
           ret (More (Thunk (Two x y)) (Thunk Nil) (Thunk u))
       | (Triple x _ _) => 
           let~ r := map1 chopA q in
           ret (More (Thunk (One x)) r (Thunk u))
       end )
   | (More c _ _, _) => 
       forcing c (fun c => 
       match c with 
       | One t => 
         forcing t (fun t => 
         match t with
         | (Pair x y) => ret (More (Thunk (Two x y)) (Thunk Nil) (Thunk u))
         | (Triple x _ _) => 
             let~ r := map1 chopA q in
             ret (More (Thunk (One x)) r (Thunk u))
         end)
      | Two t _ =>
        forcing t (fun t => 
        match t with 
        | (Pair x y) => ret (More (Thunk (Two x y)) (Thunk Nil) (Thunk u))
        | (Triple x _ _) => 
            let~ r := map1 chopA q in
            ret (More (Thunk (One x)) r (Thunk u))
        end)
      | Three t _ _ => 
          forcing t (fun t => 
          match t with 
          | (Pair x y) => ret (More (Thunk (Two x y)) (Thunk Nil) (Thunk u))
          | (Triple x _ _) => 
            let~ r := map1 chopA q in       
            ret (More (Thunk (One x)) r (Thunk u))
          end)
       end)
  end.

Definition tailA {a:Type} (t: T (SeqA a)) : M (SeqA a) :=
  tick >>
  forcing t (fun t =>
  match t with
  | Nil => ret Nil
  | Unit x => ret Nil
  | More v q u =>
    forcing v (fun v =>
    match v with
    | One _ => forcing q (fun q => forcing u (fun u => more0 q u))
    | Two x y => let~ v := ret (One y) in ret (More v q u)
    | Three x y z => let~ v := ret (Two y z) in ret (More v q u)
    end)
  end).

Fixpoint toTuples {a:Type} (la : listA a) : M (listA (TupleA a)) := 
  tick >>
  match la with
    | NilA => ret NilA
    | ConsA x t => 
        forcing t (fun t => 
        match t with 
        | NilA => ret NilA
        | ConsA y t => 
          forcing t (fun t => 
          match t with 
          | NilA => ret (ConsA (Thunk (Pair x y)) (Thunk NilA))
          | ConsA z t => 
              forcing t (fun t => 
              match t with 
              | NilA => ret (ConsA (Thunk (Triple x y z)) (Thunk NilA))
              | ConsA w t => 
                  forcing t (fun t => 
                  match t with 
                  | NilA => 
                      ret (ConsA (Thunk (Pair x y)) 
                            (Thunk (ConsA (Thunk (Pair z w)) (Thunk NilA))))
                  | _ =>
                      let~ r := toTuples t in
                      ret (ConsA (Thunk (Triple x y z)) r)
                  end)
              end)
          end)
        end)
  end.

Definition CrowdA_toListA {a:Type} (c : CrowdA a) : listA a :=
match c with
 | (One x) => ConsA x (Thunk NilA)
 | (Two x y) => ConsA x (Thunk (ConsA y (Thunk NilA)))
 | (Three x y z) => ConsA x (Thunk (ConsA y (Thunk (ConsA z (Thunk NilA)))))
end.



Fixpoint glue {a:Type} (q1 : SeqA a) (la: listA a) (q2: SeqA a) : M (SeqA a) :=
  tick >> 
  match (q1,q2) with 
  | (Nil,_) => foldrA_ consA (Thunk q2) la
  | (_,Nil) => foldlA_ snocA (Thunk q1) la
  | (Unit x, _) => foldrA_ consA (Thunk q2) (ConsA x (Thunk la))
  | (_, Unit y) => 
      let~ r := append_ la (Thunk (ConsA y (Thunk NilA))) in
      foldlA snocA (Thunk q1) r
  | (More u1 q1 v1, More u2 q2 v2) =>
      forcing q1 (fun q1 =>
      let! v1 := force v1 in
      let! q2 := force q2 in 
      let! v2 := force v2 in
      let r1 := CrowdA_toListA v1 in
      let r2 := CrowdA_toListA v2 in
      let~ r3 := append_ la (Thunk r2) in
      let! l  := appendA (Thunk r1) r3 in
      let! l := toTuples l in
      let~ r  := glue q1 l q2 in
      ret (More u1 r (Thunk v2)))
  end.

Definition appendA {a:Type} (q1 : T (SeqA a)) (q2 : T (SeqA a)) : M (SeqA a) :=
  let! q1 := force q1 in
  let! q2 := force q2 in
  glue q1 NilA q2.

(** *)

Fixpoint _depthX {a} (t: SeqA a) : nat :=
  match t with
  | More _ t _ => 1 + match t with Undefined => 0 | Thunk t => _depthX t end
  | _ => 0
  end.

Definition depthX {a} (t: T (SeqA a)) : nat :=
  match t with
  | Undefined => 0
  | Thunk t => _depthX t
  end.
