(* Instantiate Interfaces with BankersQueue *)
From Coq Require Import List Lia.
From Clairvoyance Require Import Core Approx ApproxM List Misc BankersQueue Cost Interfaces Tick.

Import ListNotations.

Set Primitive Projections.
Set Implicit Arguments.
Set Contextual Implicit.
Set Maximal Implicit Insertion.

#[global] Instance BottomOf_QueueA {a} : BottomOf (QueueA a) :=
  fun q => MkQueueA (nfrontA q) Undefined (nbackA q) Undefined.

#[global] Instance BottomIsLeast_QueueA {a} : BottomIsLeast (QueueA a).
Proof.
  intros []; constructor; constructor.
Qed.

Definition a := nat.
Definition value := Queue a.
Definition valueA := T (QueueA a).
Notation stack := (list value) (only parsing).
Notation stackA := (list valueA) (only parsing).

Inductive op : Type :=
| Empty
| Push (x : a)
| Pop
.

Notation Eval := (Eval op value).
Notation Budget := (Budget op value).
Notation Exec := (Exec op valueA).
Notation ApproxAlgebra := (ApproxAlgebra value valueA).
Notation Potential := (Potential valueA).

Definition eval : Eval :=
  fun (o : op) (args : list value) => match o, args with
  | Empty, _ => [empty]
  | Push x, q :: _ => [push q x]
  | Pop, q :: _ =>
    match pop q with
    | None => []
    | Some (x, q) => [q]
    end
  | _, _ => []
  end.

Definition budget : Budget :=
  fun (o : op) (args : list value) => match o with
  | Empty | Push _ | Pop => 7
  end.

Definition exec : Exec :=
  fun (o : op) (args : list valueA) => match o, args with
  | Empty, _ => let! q := emptyA in ret [Thunk q]
  | Push x, q :: _ => let! q' := pushA q (Thunk x) in ret [Thunk q']
  | Pop, q :: _ =>
    let! pop_q := popA q in
    match pop_q with
    | None => ret []
    | Some (x, q) => ret [q]
    end
  | _, _ => ret []
  end.

#[export] Existing Instances eval budget exec.

#[export] Instance wf : WellFormed value := BankersQueue.well_formed.

#[export] Instance wf_eval : WfEval.
Proof.
  red. intros [] vs Hvs; cbn.
  - constructor; [ apply well_formed_empty | constructor ].
  - destruct Hvs; constructor; [ | constructor ].
    apply well_formed_push. auto.
  - destruct Hvs; [ constructor | ].
    destruct pop as [ [] | ] eqn:Epop; [ | constructor ].
    constructor; [ | constructor]. eapply well_formed_pop; eauto.
Qed.

Lemma monotonic_exec (o : op) : Monotonic (exec o).
Proof.
  intros ? ? E. destruct o; cbn.
  - reflexivity.
  - destruct E as [ | ? ? ? ? E1 E].
    + reflexivity.
    + apply bind_mon; [ apply pushA_mon; reflexivity + auto | intros; apply ret_mon ].
      repeat constructor; auto.
  - destruct E as [ | ? ? ? ? E1 E ]; [ reflexivity | ].
    apply bind_mon; [ apply popA_mon; auto | intros ? ? []; [ reflexivity | ] ].
    destruct x1, y0.
    apply ret_mon. repeat constructor; apply H.
Qed.

Definition approx_algebra : ApproxAlgebra.
Proof. econstructor; try typeclasses eauto. Defined.
#[export] Existing Instance approx_algebra.

Lemma well_defined_exec : WellDefinedExec.
Proof. constructor; exact monotonic_exec. Qed.
#[export] Existing Instance well_defined_exec.

Definition onThunk {a b} (y : b) (f : a -> b) (u : T a) : b :=
  match u with
  | Undefined => y
  | Thunk x => f x
  end.

(* "debt" in BankersQueue *)
Definition potential : Potential := (* ... *)
  onThunk 0 (fun qA => 2 * sizeX 0 (frontA qA) - 2 * nbackA qA).
#[export] Existing Instance potential.

Lemma subadditive_onThunk {a} `{LessDefined a, Lub a} (f : a -> nat) `{!SubadditiveMeasure f}
  : SubadditiveMeasure (onThunk 0 f).
Proof.
  red. intros ? ? [? [ H1 H2 ] ]; inv H1; inv H2; cbn; [lia .. | ].
  apply subadditive_measure. eauto.
Qed.

Lemma well_defined_potential : WellDefinedPotential.
Proof.
  constructor.
  - apply @subadditive_onThunk. apply @LubDebt_QueueA.
  - exact (fun _ => eq_refl).
Qed.
#[export] Existing Instance well_defined_potential.

Lemma less_defined_onThunk {a b} `{Exact b a, LessDefined a, BottomOf a, !BottomIsLeast a} (x : T a) (y : b)
  : x `less_defined` exact y -> onThunk (bottom_of (exact y)) (fun x => x) x `less_defined` exact y.
Proof.
  intros Hy; inv Hy; cbn; [ apply bottom_is_least | auto ].
Qed.

Lemma less_defined_onThunk_inv {a} `{LessDefined a, BottomOf a, !BottomIsLeast a}
    (x : T a) (y y' : a)
  : onThunk y' (fun x => x) x `less_defined` y -> x `less_defined` Thunk y.
Proof.
  intros Hy; destruct x; constructor. apply Hy.
Qed.

Lemma pushD_val (q : Queue a) x outD :
  let qA := fst (Tick.val (pushD q x outD)) in
  (qA, Thunk x) = Tick.val (pushD q x outD).
Proof.
  destruct (Tick.val (pushD q x outD)) eqn:Ev; cbn; f_equal.
  unfold pushD in Ev. cbn in Ev. destruct (Tick.val (mkQueueD _ _ _ _ _)) in Ev.
  cbn in Ev. inv Ev. auto.
Qed.

Theorem physicist's_argument : Physicist'sArgument.
Proof.
  red. intros [] vs Hvs output Houtput; cbn [exec].
  - exists (bottom_of (exact vs)).
    split; [ apply bottom_is_least | ].
    unfold emptyA; mgo_.
    split; [ assumption | ].
    replace (sumof _ _) with 0.
    2: symmetry; apply (potential_bottom_list (approx_algebra := approx_algebra) potential_bottom _).
    lia.
  - destruct vs; cbn [eval] in Houtput.
    { exists []; split; [ constructor | ].
      mgo_. split; auto. lia. }
    inv Houtput. inv H3.
    exists (fst (Tick.val (pushD v x (onThunk (bottom_of (exact (push v x))) (fun q => q) x0))) :: bottom_of (exact vs)).
    split.
    { constructor.
      { apply pushD_approx. inv H2; cbn. { apply bottom_is_least. } { assumption. } }
      { apply bottom_is_least. } }
    mgo_.
    inv Hvs.
    relax.
    { eapply pushA_cost'.
      - eassumption.
      - apply less_defined_onThunk in H2. exact H2.
      - apply pushD_val.
      - reflexivity. }
    cbn beta; intros ? ? [HH1 HH2]. change (debt (a := T _)) with potential in HH2.
    replace (debt (onThunk _ _ _)) with (potential x0) in HH2.
    2:{ destruct x0; reflexivity. }
    mgo_.
    split.
    { constructor; [ | constructor ]. revert HH1. apply less_defined_onThunk_inv. }
    remember (potential _).
    replace (sumof _ _) with 0; [ lia | ].
    symmetry; apply (sumof_bottom (Hf_bottom := @potential_bottom _ _ _ _ well_defined_potential)).
  - destruct vs; cbn [eval] in Houtput.
    { exists []; split; [ constructor | ].
      mgo_. split; auto. lia. }
    pose (outD := match output with [] => None | q :: _ => Some (@Undefined a, q) end).
    pose (inD := Tick.val (popD v outD)).
    exists (inD :: bottom_of (exact vs)).
    split.
    { constructor.
      + apply popD_approx.
        destruct pop as [ [] | ]; inv Houtput.
        { constructor; constructor; constructor + assumption. }
        { constructor. }
      + apply bottom_is_least. }
    mgo_.
    inv Hvs.
    relax.
    { eapply (popA_cost' (outD := outD)).
      - eassumption.
      - destruct pop as [ [] | ]; inv Houtput.
        + constructor. constructor; [ constructor | ]. auto.
        + constructor.
      - reflexivity. }
    cbn beta.
    intros ? ? [HH1 HH2].
    change (debt (Tick.val (popD v outD))) with (potential inD) in HH2.
    destruct pop as [ [] | ]; inv Houtput.
    + inv HH1. inv H5. destruct y. mgo_.
      split; [ constructor; [apply H0 | constructor ] | ].
      change (debt x0) with (potential x0) in HH2.
      replace (sumof _ _) with 0; [ lia | ].
      symmetry; apply (sumof_bottom (Hf_bottom := @potential_bottom _ _ _ _ well_defined_potential)).
    + inv HH1. mgo_. split; [ constructor | ].
      replace (sumof _ _) with 0; [ lia | ].
      symmetry; apply (sumof_bottom (Hf_bottom := @potential_bottom _ _ _ _ well_defined_potential)).
Qed.
#[export] Existing Instance physicist's_argument.

Theorem amortized_cost : AmortizedCostSpec.
Proof. apply physicist's_method. Qed.

(* Print Assumptions amortized_cost. *)
