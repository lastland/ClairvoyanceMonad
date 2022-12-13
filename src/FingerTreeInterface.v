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
Import FingerTree.
Import FingerTreeM.

#[global] Instance Exact_Tuple {a b} `{Exact a b} : Exact (Tuple a) (TupleA b) := fun x =>
  match x with
  | FingerTree.Pair x y => Pair (exact x) (exact y)
  | FingerTree.Triple x y z => Triple (exact x) (exact y) (exact z)
  end.

#[global] Instance Exact_Crowd {a b} `{Exact a b} : Exact (Crowd a) (CrowdA b) := fun x =>
  match x with
  | FingerTree.One x => One (exact x)
  | FingerTree.Two x y => Two (exact x) (exact y)
  | FingerTree.Three x y z => Three (exact x) (exact y) (exact z)
  end.

#[global] Instance Exact_Seq : forall {a b} `{Exact a b}, Exact (Seq a) (SeqA b) :=
  fix _exact {a b} `{Exact a b} (x : Seq a) : SeqA b :=
    let _ : Exact (Seq (Tuple a)) (SeqA (TupleA b)) := _exact in
    match x with
    | FingerTree.Nil => Nil
    | FingerTree.Unit x => Unit (exact x)
    | FingerTree.More x y z => More (exact x) (exact y) (exact x)
    end.

Inductive less_defined_Tuple {a} `{LessDefined a} : LessDefined (TupleA a) :=
| less_defined_Pair {x x' y y'} : x `less_defined` x' -> y `less_defined` y' ->
    less_defined_Tuple (Pair x y) (Pair x' y')
| less_defined_Triple {x x' y y' z z'}
  : x `less_defined` x' -> y `less_defined` y' -> z `less_defined` z' ->
    less_defined_Tuple (Triple x y z) (Triple x' y' z')
.
#[global] Existing Instance less_defined_Tuple.

Inductive less_defined_Crowd {a} `{LessDefined a} : LessDefined (CrowdA a) :=
| less_defined_One {x x'} : x `less_defined` x' -> less_defined_Crowd (One x) (One x')
| less_defined_Two {x x' y y'} : x `less_defined` x' -> y `less_defined` y' ->
    less_defined_Crowd (Two x y) (Two x' y')
| less_defined_Three {x x' y y' z z'}
  : x `less_defined` x' -> y `less_defined` y' -> z `less_defined` z' ->
    less_defined_Crowd (Three x y z) (Three x' y' z')
.
#[global] Existing Instance less_defined_Crowd.

Unset Elimination Schemes.

Inductive less_defined_Seq {a} `{LessDefined a} : LessDefined (SeqA a) :=
| less_defined_Nil : less_defined_Seq Nil Nil
| less_defined_Unit {x x'} : x `less_defined` x' -> less_defined_Seq (Unit x) (Unit x')
| less_defined_More {x x' y y' z z'}
  : x `less_defined` x' -> y `less_defined` y' -> z `less_defined` z' ->
    less_defined_Seq (More x y z) (More x' y' z')
.
#[global] Existing Instance less_defined_Seq.

Definition less_defined_Seq_ind (P : forall a, LessDefined a -> SeqA a -> SeqA a -> Prop)
  (f : forall a {ld : LessDefined a}, P a ld Nil Nil)
  (f0 : forall a {ld : LessDefined a} (x x' : T a), x `less_defined` x' -> P a _ (Unit x) (Unit x'))
  (f1 : forall a {ld : LessDefined a} (x x' : T (CrowdA a)) (y y' : T (SeqA (TupleA a)))
          (z z' : T (CrowdA a)),
        x `less_defined` x' ->
        forall (IH : @LessDefined_T _ (P (TupleA a) _) y y'),
        z `less_defined` z' -> P a _ (More x y z) (More x' y' z'))
  : forall a (H : LessDefined a) (s s0 : SeqA a) (l : less_defined_Seq s s0), P a H s s0 :=
  fix _ind a H x y H :=
  match H with
  | less_defined_Nil => f _
  | @less_defined_Unit _ _ x x' x0 => f0 _ x x' x0
  | @less_defined_More _ _ x x' y y' z z' x0 x1 x2 =>
      f1 _ x x' y y' z z' x0 match x1 with LessDefined_Undefined _ => LessDefined_Undefined _ | LessDefined_Thunk _ _ H => LessDefined_Thunk _ _ (_ind _ _ _ _ H) end x2
  end.

Set Elimination Schemes.

#[global] Instance PreOrder_less_defined_Tuple {a}
    `{!LessDefined a, !PreOrder (less_defined (a := a))}
  : PreOrder (less_defined (a := TupleA a)).
Proof.
  constructor.
  - intros []; constructor; reflexivity.
  - intros ? ? ? [] HH; inv HH; constructor; etransitivity; eauto.
Qed.

#[global] Instance PreOrder_less_defined_Crowd {a}
    `{!LessDefined a, !PreOrder (less_defined (a := a))}
  : PreOrder (less_defined (a := CrowdA a)).
Proof.
  constructor.
  - intros []; constructor; reflexivity.
  - intros ? ? ? [] HH; inv HH; constructor; etransitivity; eauto.
Qed.

#[global] Instance PreOrder_less_defined_Seq {a}
    `{!LessDefined a, !PreOrder (less_defined (a := a))}
  : PreOrder (less_defined (a := SeqA a)).
Proof.
  constructor.
  - intros x; induction x; constructor; reflexivity + auto.
    destruct IH; constructor. apply H. typeclasses eauto.
  - intros x y z HH; revert PreOrder0 z. induction HH; intros zz PO Hz; inv Hz; constructor;
      try (etransitivity; eassumption).
    inv IH; [ constructor | ]. inv H6. constructor. eapply H1; eauto.
    typeclasses eauto.
Qed.

#[global] Instance Lub_SeqA {a} `{Lub a} : Lub (SeqA a). 
Admitted.
#[global] Instance LubLaw_SeqA {a} `{LubLaw a} : LubLaw (SeqA a). 
Print LubLaw. 
Admitted.

#[global] Instance BottomOf_SeqA {a} : BottomOf (SeqA a) := fun q =>
  match q with
  | Nil => Nil
  | Unit _ => Unit Undefined
  | More _ _ _ => More Undefined Undefined Undefined
  end.

#[global] Instance BottomIsLeast_SeqA {a} `{LessDefined a} : BottomIsLeast (SeqA a).
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


Require  Coq.Classes.RelationClasses.

Lemma monotonic_exec (o : op) : Monotonic (exec o).
Proof.
unfold Monotonic. intros.
destruct o; simpl.
- (* Empty *) reflexivity.
- (* Cons *)
  inversion H. reflexivity.
  subst.
  apply bind_mon.
  unfold consA.
  apply bind_mon.
  apply force_mon.
  + eauto.
  + intros x y LT. 
    clear H H1 H0 xs ys x1 y0.
    generalize x y LT.
    induction 1; simpl.
    apply bind_mon.
    reflexivity.
    intros x1 y1 LT1. 
    apply ret_mon.
    admit.
    apply bind_mon. reflexivity.
    intros x2 y2 LT2.
    apply ret_mon.
    eapply less_defined_More; try reflexivity.
    eapply LessDefined_Thunk. 
    eapply less_defined_One.
    eapply LessDefined_Thunk. 
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
