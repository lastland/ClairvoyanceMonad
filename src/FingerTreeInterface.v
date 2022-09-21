(* Instantiate Interfaces with FingerTreeM *)

(* Note: finger trees use laziness: [consA] and [snocA] are recursive,
   so one could try to apply them repeatedly to a "dangerous" tree
   to take O(log n) time every time instead of O(1).
   But the recursive calls are to be forced (and amortized) by future
   operations. *)
From Coq Require Import List RelationClasses.
From Clairvoyance Require Import
  Core Approx ApproxM List Misc Cost Interfaces.
From Clairvoyance Require FingerTree FingerTreeM.

Import ListNotations.

Set Primitive Projections.
Set Implicit Arguments.
Set Contextual Implicit.
Set Maximal Implicit Insertion.

Definition a := nat.

(** Operations symbols *)
Inductive Op : Type :=
| Empty
| Cons (x : a)
| Snoc (x : a)
| Head
| Tail
| Append
.

(* Pure reference implementation [eval_op_Seq] and cost specification [CostSpec_Seq] *)
Section Seq.
Import FingerTree.

Definition Seq := FingerTree.Seq.

Definition eval_op_Seq (o : Op) (vs : list (Seq a)) : list (Seq a) :=
  match o, vs with
  | Empty, _ => [Nil]
  | Cons x, q :: _ => [cons x q]
  | Snoc x, q :: _ => [snoc q x]
  | Head, q :: _ => []  (* Doesn't create a new FT *)
  | Tail, q :: _ => [tail q]
  | Append, q :: q' :: _ => [append q q']
  | _, _ => []
  end.

(* TODO: splitAt, as an example of operation with two outputs *)

#[global] Instance PureImpl_Seq : PureImpl Op (Seq a) := eval_op_Seq.

#[global] Instance CostSpec_Seq : CostSpec Op (Seq a) :=
  fun o vs =>
    match o, vs with
    | (Empty | Cons _ | Snoc _ | Head | Tail), _ => 1
    | Append, q :: q' :: _ => max (depth q) (depth q')
    | _, _ => 0
    end.

End Seq.

(* Clairvoyant translation *)
Section SeqA.
Import FingerTreeM.

Definition SeqA' := SeqA a.

Definition exec_op_SeqA (o : Op) (vs : list SeqA') : M (list SeqA') :=
  match o, vs with
  | Empty, _ => ret [Nil]
  | Cons x, q :: _ => let! q := consA (Thunk x) (Thunk q) in ret [q]
  | Snoc x, q :: _ => let! q := snocA (Thunk q) (Thunk x) in ret [q]
  | Head, q :: _ => let! _ := headA (Thunk q) in ret []  (* Doesn't create a new FT *)
  | Tail, q :: _ => let! q := tailA (Thunk q) in ret [q]
  | Append, q :: q' :: _ => let! q := appendA (Thunk q) (Thunk q') in ret [q]
  | _, _ => ret []
  end.

#[global] Instance CvImpl_SeqA : CvImpl Op SeqA' := exec_op_SeqA.

(** ** [ApproxOrder_Seq]: Order structure of [SeqA] *)

#[global] Instance Exact_Seq : Exact (Seq a) (SeqA a).
Admitted.

#[global] Instance LessDefined_SeqA : LessDefined (SeqA a).
Admitted.

#[global] Instance PreOrder_less_defined_SeqA : PreOrder (less_defined (a := SeqA a)).
Admitted.

#[global] Instance Lub_SeqA : Lub (SeqA a). Admitted.
#[global] Instance LubLaw_SeqA : LubLaw (SeqA a). Admitted.

#[local] Instance exec_op_mon (o : Op) :
  Morphisms.Proper (Morphisms.respectful less_defined less_defined)
    (exec_op (op := Op) (valueA := SeqA') o).
Proof.
Admitted.


#[global] Instance HasBottom_SeqA : HasBottom (SeqA a) := fun q =>
  match q with
  | Nil => Nil
  | Unit _ => Unit Undefined
  | More _ _ _ => More Undefined Undefined Undefined
  end.

#[global] Instance BottomIsLeast_SeqA : BottomIsLeast (SeqA a).
Admitted.

#[global] Instance ApproxOrder_Seq : ApproxOrder Op (Seq a) SeqA'.
Proof.
  econstructor; try typeclasses eauto.
Defined.

(** * Main theorem: HasAmortizedCost_Seq *)

#[global] Instance Potential_SeqA : Potential SeqA' := fun t =>
  0 (* TODO *).

#[global] Instance HasPotential_SeqA : HasPotential SeqA'.
Admitted.

#[global] Instance MonotoneCvImpl_SeqA : MonotoneCvImpl CvImpl_SeqA.
Admitted.

#[global] Instance Physicist'sArgument_SeqA : Physicist'sArgument CostSpec_Seq CvImpl_SeqA.
Proof.
  econstructor.
Admitted.

Theorem HasAmortizedCost_Seq : HasAmortizedCost CostSpec_Seq CvImpl_SeqA.
Proof.
  apply physicist's_method.
Qed.
