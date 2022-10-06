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

(* Auxiliaries for [approx_algebra] *)

Section AA.

Notation Seq := FingerTree.Seq.
Import FingerTreeM.

Context {a : Type}.

#[global] Instance Exact_Seq : Exact (Seq a) (SeqA a).
Admitted.

#[global] Instance LessDefined_SeqA : LessDefined (SeqA a).
Admitted.

#[global] Instance PreOrder_less_defined_SeqA : PreOrder (less_defined (a := SeqA a)).
Admitted.

#[global] Instance Lub_SeqA : Lub (SeqA a). Admitted.
#[global] Instance LubLaw_SeqA : LubLaw (SeqA a). Admitted.

#[global] Instance BottomOf_SeqA : BottomOf (SeqA a) := fun q =>
  match q with
  | Nil => Nil
  | Unit _ => Unit Undefined
  | More _ _ _ => More Undefined Undefined Undefined
  end.

#[global] Instance BottomIsLeast_SeqA : BottomIsLeast (SeqA a).
Admitted.

End AA.

(**)

Definition a := nat.
Definition value := FingerTree.Seq a.
Definition valueA := FingerTreeM.SeqA a.
Notation stack := (list value) (only parsing).
Notation stackA := (list valueA) (only parsing).

(** Operations symbols *)
Inductive op : Type :=
| Empty
| Cons (x : a)
| Snoc (x : a)
| Head
| Tail
| Append
.

Notation Eval := (Eval op value).
Notation Budget := (Budget op value).
Notation Exec := (Exec op valueA).
Notation ApproxAlgebra := (ApproxAlgebra value valueA).
Notation Potential := (Potential valueA).

Import FingerTree.

Definition eval : Eval :=
  fun (o : op) (args : list value) => match o, args with
  | Empty, _ => [Nil]
  | Cons x, q :: _ => [cons x q]
  | Snoc x, q :: _ => [snoc q x]
  | Head, q :: _ => []  (* Doesn't create a new FT *)
  | Tail, q :: _ => [tail q]
  | Append, q :: q' :: _ => [append q q']
  | _, _ => []
  end.

Definition budget : Budget :=
  fun (o : op) (args : list value) => match o, args with
  | (Empty | Cons _ | Snoc _ | Head | Tail), _ => 1
  | Append, q :: q' :: _ => max (depth q) (depth q')
  | _, _ => 0
  end.

Import FingerTreeM.

Definition exec : Exec :=
  fun (o : op) (args : list valueA) => match o, args with
  | Empty, _ => let! s := emptyA in ret [s]
  | Cons x, s :: _ => let! s := consA (Thunk x) (Thunk s) in ret [s]
  | Snoc x, s :: _ => let! s := snocA (Thunk s) (Thunk x) in ret [s]
  | Head, s :: _ => let! _ := headA (Thunk s) in ret []  (* Doesn't create a new FT *)
  | Tail, s :: _ => let! s := tailA (Thunk s) in ret [s]
  | Append, s :: s' :: _ => let! s := appendA (Thunk s) (Thunk s') in ret [s]
  | _, _ => ret []
  end.

#[export] Existing Instances eval budget exec.

Lemma monotonic_exec (o : op) : Monotonic (exec o).
Proof.
Admitted.

Definition approx_algebra : ApproxAlgebra.
Proof. econstructor; try typeclasses eauto. Defined.
#[export] Existing Instance approx_algebra.

#[export] Instance wf : WellFormed value := fun _ => True.
#[export] Instance wf_eval : WfEval.
Proof.
  intros o xs _. induction (eval o xs); repeat constructor; auto.
Qed.

Lemma well_defined_exec : WellDefinedExec.
Proof. constructor; exact monotonic_exec. Qed.
#[export] Existing Instance well_defined_exec.

(* "debt" in BankersQueue *)
Definition potential : Potential := (* ... *)
  fun t => _depthX t.
#[export] Existing Instance potential.

Lemma well_defined_potential : WellDefinedPotential.
Proof. Admitted.
#[export] Existing Instance well_defined_potential.

Theorem physicist's_argument : Physicist'sArgument.
Proof.
  red.
Admitted.
#[export] Existing Instance physicist's_argument.

Theorem amortized_cost : AmortizedCostSpec.
Proof. apply physicist's_method. Qed.
