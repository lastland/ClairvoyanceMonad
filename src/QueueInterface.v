(* Instantiate Interfaces with BankersQueue *)
From Coq Require Import List Lia.
From Clairvoyance Require Import Core Approx ApproxM List Misc BankersQueue Cost Interfaces Tick.

Import ListNotations.
Import Tick.Notations.

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
Notation Demand := (Demand op value valueA).
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

Definition forcingD {a b} (y : b) (u : T a) (f : a -> Tick b) : Tick b :=
  match u with
  | Undefined => Tick.ret y
  | Thunk x => f x
  end.

Definition forceD {a} (y : a) (u : T a) : a :=
  match u with
  | Undefined => y
  | Thunk x => x
  end.

Lemma less_defined_forceD {a} `{LessDefined a} (x : T a) (y : a) (z : a)
  : y `less_defined` z ->
    x `less_defined` Thunk z ->
    forceD y x `less_defined` z.
Proof.
  intros Hy Hx; inv Hx; cbn; auto.
Qed.

Definition demand : Demand :=
  fun (o : op) (args : list value) (d : list valueA) => match o, args, d with
  | Empty, _, _ => Tick.ret (bottom_of (exact args))
  | Push x, (q :: tl), (outD :: _) =>
    let outD := forceD (bottom_of (exact (push q x))) outD in
    let+ (qD, _) := pushD q x outD in
    Tick.ret (qD :: bottom_of (exact tl))
  | Pop, (q :: tl), outD =>
    let outD' := match outD with [] => None | qD' :: _ => Some (Undefined, qD') end in
    let+ qD := popD q outD' in
    Tick.ret (qD :: bottom_of (exact tl))
  | _, _, _ => Tick.ret (bottom_of (exact args))
  end%tick.
#[export] Existing Instance demand.

Lemma pd : PureDemand.
Proof.
  do 2 red. intros [] [|q qs] [|yD ysD] Hq; try apply bottom_is_least; cbn in Hq |- *.
  - inv Hq.
    destruct (Tick.val (pushD q x _)) eqn:EpushD.
    constructor; [ | apply bottom_is_least ].
    apply (f_equal fst) in EpushD. cbn in EpushD. rewrite <- EpushD.
    apply pushD_approx.
    apply less_defined_forceD; [ apply bottom_is_least | auto ].
  - constructor; [ | apply bottom_is_least ].
    unfold valueA. rewrite pop_popD; [ reflexivity | ].
    destruct pop as [ [] |]; [ inv Hq | reflexivity ].
  - constructor; [ | apply bottom_is_least ].
    apply popD_approx. destruct pop as [ [] |]; inv Hq.
    repeat constructor; auto.
Qed.

Lemma cd : CvDemand.
Proof.
  do 2 red. intros []; cbn.
  - intros qs yD Hy n xD; injection 1; intros -> ->. unfold emptyA.
    mgo'. split; [ | auto ]. constructor; assumption.
  - intros [| q qs] yD Hy; inv Hy.
    { intros ? ?; injection 1; intros -> ->; cbn; mgo'. split; reflexivity. }
    intros n xD. destruct pushD as [ ? [] ] eqn:EpushD. intros Hpush; inv Hpush.
    apply optimistic_bind.
    assert (t0 = Thunk x); [ | subst t0 ].
    { apply (f_equal (fun m => snd (Tick.val m))) in EpushD.
      unfold pushD in EpushD. cbn in EpushD.
      match goal with [ H : context [ match ?u with _ => _ end ] |- _ ] => destruct u end.
      cbn in EpushD. auto. }
    eapply optimistic_mon; [ eapply pushD_spec |].
    { eapply less_defined_forceD; [ apply bottom_is_least | eassumption ]. }
    { rewrite EpushD. reflexivity. }
    cbn beta. intros ? ? []. mforward idtac.
    split.
    { constructor; auto. inv H2; cbn in H; constructor; auto. }
    { rewrite EpushD in H0. cbn in H0. lia. }
  - intros [| q qs] yD Hy.
    { intros ? ? Hd; inv Hd; cbn. mforward idtac. split; auto. }
    destruct popD eqn:EpopD. intros ? ? Hd; inv Hd.
    mforward idtac.
    match goal with [ HH : _ _ ?w = _ |- _ ] => pose (v := w); fold v in HH end.
    eapply optimistic_mon; [ eapply popD_spec | ].
    2:{ apply (eq_sym (f_equal Tick.val EpopD)). }
    { destruct pop as [ [] | ].
      { inv Hy. repeat constructor; auto. }
      { inv Hy. reflexivity. } }
    cbn beta. intros ? ? [Hdef Hcost].
    rewrite EpopD in Hcost; simpl in Hcost.
    destruct (pop q) as [ [] | ] eqn:Hpop; inv Hy; inv Hdef.
    + destruct y. mforward idtac. split; [ | lia ].
      { constructor; [ apply H0 | auto ]. }
    + mforward idtac. split; [ reflexivity | lia ].
Qed.

#[export] Existing Instances pd cd.

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

Theorem physicist's_argumentD : Physicist'sArgumentD.
Proof.
  assert (Hsp : forall v, sumof potential (bottom_of v) = 0).
  { apply (sumof_bottom (Hf_bottom := @potential_bottom _ _ _ _ well_defined_potential)). }
  red. intros [] vs Hvs output Houtput; cbn [demand].
  - intros ? ? Hd; inv Hd. rewrite Hsp. lia.
  - destruct vs; intros ? ? Hd.
    { inv Hd. rewrite Hsp; lia. }
    destruct output.
    { inv Hd. rewrite Hsp; lia. }
    destruct pushD as [ ? [] ] eqn:EpushD in Hd. inv Hd.
    cbn. rewrite Hsp. inv Hvs.
    inv Houtput. inv H6.
    unshelve eassert (HH := pushD_cost H1 _ (f_equal Tick.val (eq_sym EpushD))).
    { apply less_defined_forceD; [ apply bottom_is_least | auto ]. }
    rewrite EpushD in HH. cbn [Tick.cost] in HH. cbn [sumof fold_right].
    change (potential t) with (debt t).
    destruct v0; cbn [forceD] in HH.
    { change (potential (Thunk x0)) with (debt x0). lia. }
    { cbn. change (debt (bottom_of ?w)) with 0 in HH. lia. }
  - destruct vs; intros ? ? Hd.
    { inv Hd; rewrite Hsp; lia. }
    destruct popD as [] eqn:EpopD in Hd. inv Hd. cbn.
    rewrite Hsp. inv Hvs.
    cbn in Houtput.
    lazymatch goal with [ HH : _ _ ?ww = _ |- _ ] => pose (w := ww); fold w in EpopD end.
    unshelve eassert (HH := popD_cost (outD := w) H1 _).
    { destruct pop as [ [] | ]; inv Houtput; repeat constructor; cbn; auto. }
    rewrite EpopD in HH; cbn [Tick.val Tick.cost] in HH.
    match type of HH with (_ <= _ + ?z) => replace z with (sumof potential output) in HH end.
    { change (potential val) with (debt val). lia. }
    { destruct pop as [ [] | ]; inv Houtput; [ | auto ]. inv H5. cbn. auto. }
Qed.
#[export] Existing Instance physicist's_argumentD.

Theorem amortized_cost : AmortizedCostSpec.
Proof. apply physicist's_method. Qed.

(* Print Assumptions amortized_cost. *)
