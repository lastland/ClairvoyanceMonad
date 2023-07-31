
From Coq Require Import Arith List Psatz Morphisms Relations.
From Equations Require Import Equations.

From Clairvoyance Require Import Core Approx ApproxM Tick Misc ListA QueueInterface QueueTrace.

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

(* ---------------------- Queue operations ---------------------- *)

Record two_list_queue (a : Type) : Type := TwoListQueue
{
  QueueFront : list a;
  QueueBack : list a
}.

Definition Push_TwoListQueue (a : Type) (queue : two_list_queue a) (appending : a) : two_list_queue a :=
  let back := appending :: QueueBack queue in
  let front := QueueFront queue in
  TwoListQueue front back.

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

Record two_list_queueA (a : Type) : Type := TwoListQueueA
{
  QueueFrontA : T (listA a);
  QueueBackA : T (listA a)
}.

Definition Push_TwoListQueueD (a : Type) (queue : two_list_queue a) (appending : a)
  (outD : two_list_queueA a) : Tick (T (two_list_queueA a)) :=
  Tick.tick >>
  match (QueueBackA outD) with
  | Undefined => bottom
  | Thunk xsD => match xsD with
    | NilA => bottom
    | ConsA yD ysD => Tick.ret (Thunk (TwoListQueueA (QueueFrontA outD) (exact (ConsA yD ysD))))
  end
end.

(** Unfinished Pop_TwoListQueueD implementation **)

(* Definition Pop_TwoListQueueD (a : Type) (queue : two_list_queue a)
  (outD : (two_list_queueA a) * a) : Tick (T (two_list_queueA a)) :=
  Tick.tick >>
  match outD (*Need to access queuefront of outD's first element*) with
  | (Undefined, _, _) => bottom
  | (_, Undefined, _) => bottom
  | (Thunk xsD, Thunk ysD, popped) => match xsD with
    | NilA => bottom
    | ConsA yD ysD => Tick.ret (Thunk outD)
    end
  end. *)

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

(*

To prove:
- Push is constant time; state and prove it.
- If I finish it, think about best way to prove functional correctness.
  - Equivalence to pure version?
    - Prove that the pure version is also correct by showing that it's equal to a *lesser* queue using just one list

*)