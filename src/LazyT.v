Set Implicit Arguments.
Set Maximal Implicit Insertion.
Set Contextual Implicit.

From Clairvoyance Require Import Core List Fuel BankersQueue.

From Coq Require Import Nat List.

Import ListNotations.

(** Koen's code in Haskell makes use of [undefined] in Haskell. We need an
    explicit bottom value in Coq---represented by [T] here. *)
Definition Lazy (A : Type) : Type := Fuel -> T A.

(** * Combinators for [Lazy]. *)

Section LazyCombinators.

  Variables A B : Type.

  Definition ret (x : A) : Lazy A :=
    fun _ => Thunk x.

  Definition bind (m : Lazy A) (k : A -> Lazy B) : Lazy B :=
    fun f => match f with
          | F (x :: xs) =>
              match m x with
              | Thunk m' => k m' (F xs)
              | _ => Undefined
              end
          | _ => Undefined
          end.

  Definition bindT (m : Lazy A) (k : T A -> Lazy B) : Lazy B :=
    fun f => match f with
          | F (x :: xs) => k (m x) (F xs)
          | _ => Undefined
          end.

  Definition force (x : T A) : Lazy A :=
    fun _ => x.

  Definition forcing (x : T A) (f : A -> Lazy B) : Lazy B :=
    bind (force x) f.

End LazyCombinators.

(** * List. *)

Section List.

Variable A : Type.

Fail Fixpoint appendL (xs ys : list A) : Lazy (list A) :=
  match xs with
  | [] => fun f => Thunk ys
  | x :: xs' =>
    fun f => match f with
          | F (r :: _) => x :: appendL xs ys r
          | _ => Undefined
          end
  end.

Fixpoint append_ (xs' : listA A) (ys : T (listA A)) : Lazy (listA A) :=
  match xs' with
  | NilA => force ys
  | ConsA x xs'' =>
      bindT (forcing xs'' (fun xs''' => append_ xs''' ys))
        (fun r => ret (ConsA x r))
  end.

Definition appendL (xs ys : T (listA A)) : Lazy (listA A) :=
  forcing xs (fun xs' => append_ xs' ys).

Fixpoint rev_ (xs' : listA A) (ys : T (listA A)) : Lazy (listA A) :=
  match xs' with
  | NilA => force ys
  | ConsA x xs'' =>
      forcing xs'' (fun xs''' => rev_ xs''' ys)
  end.

Definition revL (xs : T (listA A)) : Lazy (listA A) :=
  forcing xs (fun xs' => rev_ xs' (Thunk NilA)).

End List.

(** * Queue. *)

Section Queue.

Variable A : Type.

Definition mkQueueL
           (n : nat) (xs : T (listA A))
           (m : nat) (ys : T (listA A)) : Lazy (QueueA A) :=
  if leb m n then
    ret {| nfrontA := n; frontA := xs; nbackA := m; backA := ys |}
  else
    bindT (bindT (revL ys) (fun ys' => appendL xs ys'))
    (fun fA => ret {| nfrontA := n + m;
                   frontA  := fA;
                   nbackA  := 0;
                   backA   := Thunk (NilA) |}).

Definition enqueueL
           (q : T (QueueA A)) (a : T A) : Lazy (QueueA A) :=
  forcing q (fun q => mkQueueL q.(nfrontA)
                            q.(frontA)
                            (q.(nbackA) + 1)
                            (Thunk (ConsA a q.(backA)))).

Definition dequeueL
           (q0 : T (QueueA A)) : Lazy (QueueA A) :=
  forcing q0 (fun q =>
               forcing q.(frontA) (fun xs =>
                 match xs with
                   | ConsA _ xs' =>
                     mkQueueL (q.(nfrontA) - 1)
                              xs'
                              q.(nbackA)
                              q.(backA)
                   | _ => fun f => q0
                   end)).

End Queue.
