Set Implicit Arguments.
Set Maximal Implicit Insertion.
Set Contextual Implicit.

From Clairvoyance Require Import Core List BankersQueue.

From Coq Require Import Nat List Psatz.

Import ListNotations.

Section FuelAndLaziness.

(** * The [Fuel] tree and the alternative [Lazy] representation. *)

Unset Elimination Schemes.

(** The same as [Fuel] used by Koen. *)
Inductive Fuel :=
| F (children: list Fuel).

(** Custom induction principles due to nested inductive types. *)
Lemma Fuel_ind : forall (P : Fuel -> Prop),
    (forall l, Forall P l -> P (F l)) ->
    forall f, P f.
Proof.
  intros P Hyp. fix SELF 1.
  intros [f]. apply Hyp.
  induction f; constructor.
  - apply SELF.
  - apply IHf.
Defined.

Set Elimination Schemes.

(** Koen's code in Haskell makes use of [undefined] in Haskell. We need an
    explicit bottom value in Coq---represented by [T] here. *)
Definition Lazy (A : Type) : Type := Fuel -> T A.

(** * A few functions regarding [Fuel]. *)

Fixpoint fuel1 (n : nat) : Fuel :=
  match n with
  | O => F []
  | S n' => F [fuel1 n']
  end.

Fixpoint cost (f : Fuel) : nat :=
  match f with
  | F l => S (list_sum (map cost l))
  end.

(** Beware of the [+ 1] on the right hand side! *)
Theorem fuel1_cost :
  forall n, cost (fuel1 n) = n + 1.
Proof.
  induction n; [reflexivity|cbn;lia].
Qed.

(** The other direction: taking a [Fuel], transforming it to a natural number
    using [cost] and back using [fuel1] is not true. *)

Section LazyCombinators.

  Variables A B : Type.

  Definition forcing (x : T A) (f : A -> Lazy B) : Lazy B :=
    match x with
    | Thunk a => f a
    | Undefined => fun f => Undefined
    end.

End LazyCombinators.

End FuelAndLaziness.

(** TODO: this should belong to [Core.v]. *)
Definition bindT {A B} (x : T A) (k : A -> T B) : T B :=
  match x with
  | Thunk a => k a
  | Undefined => Undefined
  end.

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
  | NilA => fun f => ys
  | ConsA x xs'' =>
    fun f =>
      match f with
      | F (r :: _) =>
        Thunk (ConsA x (bindT xs'' (fun xs''' => append_ xs''' ys r)))
      | _ => Undefined
      end
  end.

Fixpoint appendL (xs ys : T (listA A)) : Lazy (listA A) :=
  forcing xs (fun xs' => append_ xs' ys).

Fixpoint rev_ (xs' : listA A) (ys : T (listA A)) : Lazy (listA A) :=
  match xs' with
  | NilA => fun f => ys
  | ConsA x xs'' =>
    fun f =>
      match f with
      | F (r :: _) =>
        bindT xs'' (fun xs''' => rev_ xs''' ys r)
      | _ => Undefined
      end
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
    fun f => Thunk {| nfrontA := n; frontA := xs; nbackA := m; backA := ys |}
  else
    fun f => match f with
          | F (p :: q :: _) => Thunk
            {| nfrontA := n + m;
               frontA  := appendL xs (revL ys q) p;
               nbackA  := 0;
               backA   := Thunk (NilA) |}
          | _ => Undefined
          end.

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
