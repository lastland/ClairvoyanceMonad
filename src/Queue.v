
From Coq Require Import Arith List Psatz Morphisms Relations.
From Equations Require Import Equations.

From Clairvoyance Require Import Core Approx ApproxM Tick Misc List ListA QueueInterface QueueTrace BankersQueue.

#[local] Existing Instance Exact_id | 1.
#[local] Existing Instance LessDefined_id | 100.
#[local] Existing Instance PreOrder_LessDefined_id | 100.
#[local] Existing Instance ExactMaximal_id | 100.

Set Primitive Projections.
Set Implicit Arguments.
Set Maximal Implicit Insertion.
Set Contextual Implicit.

Import ListNotations.
Import Tick.Notations.

Global Instance Proper_S_le : Proper (le ==> le) S.
Proof.
  unfold Proper, respectful. lia.
Qed.

(** Queue implementation! **)

Record two_list_queue (a : Type) : Type := TwoListQueue
{
  QueueFront : list a;
  QueueBack : list a
}.

Record two_list_queueA (a : Type) : Type := TwoListQueueA
{
  QueueFrontA : T (listA a);
  QueueBackA : T (listA a)
}.

Global Instance Exact_two_list_queue {a b} {e : Exact a b} : Exact (two_list_queue a) (two_list_queueA b) :=
  fun queue => match queue with
    | TwoListQueue front back => TwoListQueueA (exact front) (exact back)
    end.

Definition Push_TwoListQueue (a : Type) (queue : two_list_queue a) (appending : a) : two_list_queue a :=
  let old_back := QueueBack queue in
  let new_back := appending :: old_back in
  let front := QueueFront queue in
  TwoListQueue front new_back.

Definition Push_TwoListQueueD (a : Type) (queue : two_list_queue a) (appending : a) (outD : two_list_queueA a) :
  Tick (T (two_list_queueA a) * T a) :=
  Tick.tick >>
  Tick.ret ((Thunk (TwoListQueueA (QueueFrontA outD) (tailX (QueueBackA outD)))), Thunk appending).

Definition SwapBack (a : Type) (queue : two_list_queue a) : (two_list_queue a) :=
  match QueueFront queue with
  | nil => TwoListQueue (rev (QueueBack queue)) nil
  | _ => queue
end.

Definition Pop_TwoListQueue (a : Type) (queue : two_list_queue a) : ((option a) * (two_list_queue a)) :=
  let new_queue := (SwapBack queue) in
  match QueueFront new_queue with
  | nil => (None, TwoListQueue nil nil)
  | x :: xs => (Some x, TwoListQueue xs (QueueBack new_queue))
  end.

(*Borrowed from Banker's Queue in large part.*)

(*Quoted from there...*)

(* "[mkQueue] uses [rev] and [append], in this order ([append front (rev back)]),
   so we compute the demand in reverse." *)

Definition SwapBackD {a} (queue : two_list_queue a) (outD : (option (T a) * T (two_list_queueA a))) :
  Tick (T (two_list_queueA a)) :=
  Tick.tick >>
  match QueueFront queue with
  | nil => match QueueBack queue with
    | nil => Tick.ret (exact queue)
    (*Non-empty case - undo the swap*)
    | h :: t => match outD with
      | (Some (xA, queueA)) =>
        let+ (frontD, rbackD) := thunkD (appendD (QueueFront queue) (rev (QueueBack queue))) (QueueFrontA queueA) in
        let+ backD := thunkD (revD (QueueBack queue)) rbackD in
        Tick.ret (Thunk (TwoListQueueA frontD backD))
      | _ => bottom
      end
    end
  | _ => Tick.ret (exact queue)
  end.

Definition Pop_TwoListQueueD (a : Type) (queue : two_list_queue a) (outD : ((option (T a)) * (T (two_list_queueA a)))) :
  Tick (T (two_list_queueA a)) :=
  Tick.tick >>
  let+ new_queueA := (SwapBackD queue outD) in
  match QueueFrontA new_queueA, outD with
  (*Queue was empty - return the empty queue*)
  | [], _ => Tick.ret new_queueA
  (*Queue was non-empty - push the value back on the queue*)
  | _, Some (xA, queueA) => Tick.ret (Thunk (appendD xA (QueueBackA new_queueA)))
  (*Can't happen - will never have a non-empty list and an empty demand*)
  | h1 :: t1, _ => bottom
  end.

(** Tests! **)

Compute Pop_TwoListQueue (TwoListQueue [1;2;3] []).

Compute Pop_TwoListQueue (TwoListQueue [1;2;3] [4;5;6]).

Compute Pop_TwoListQueue (TwoListQueue [] [1;2;3]).

Compute Pop_TwoListQueue (TwoListQueue [] []).

Compute Push_TwoListQueue (TwoListQueue [1;2;3] []) 1.

Compute Push_TwoListQueue (TwoListQueue [1;2;3] [4;5;6]) 2.

Compute Push_TwoListQueue (TwoListQueue [] [1;2;3]) 3.

Compute Push_TwoListQueue (TwoListQueue [] []) 4.

Compute Push_TwoListQueueD (TwoListQueue [1;2;3] []) 1 (TwoListQueueA ((exact [1;2;3])) (exact [1])).

Compute Push_TwoListQueueD (TwoListQueue [1;2;3] [4;5;6]) 2 (TwoListQueueA ((exact [1;2;3])) (exact [2;4;5;6])).

Compute Push_TwoListQueueD (TwoListQueue [] [1;2;3]) 3 (TwoListQueueA ((exact [])) (exact [3;1;2;3])).

Compute Push_TwoListQueueD (TwoListQueue [] []) 4 (TwoListQueueA ((exact [])) (exact [4])).

(** Proofs! **)

Lemma push_cost {a} (queue : two_list_queue a) (appending : a) (outD : two_list_queueA a)
  : outD `is_approx` (Push_TwoListQueue queue appending) ->
  Tick.cost (Push_TwoListQueueD queue appending outD) = 1.
Proof.
  auto.
Qed.

(*

To prove:
Done! Push is constant time; state and prove it.
- Pop first, then computation costs about it.
- If I finish it, think about best way to prove functional correctness.
  - Equivalence to pure version?
    - Prove that the pure version is also correct by showing that it's equal to a *lesser* queue using just one list
  - Input demand leq the input of the pure version + (fun xs = zs, fun xs zsD = xsD, zs `is_approx` zsD) -> (xsD `is_approx` xs)
  - At some point, define the approx function PushTLQA and prove equivalence with PushTLQD.

*)