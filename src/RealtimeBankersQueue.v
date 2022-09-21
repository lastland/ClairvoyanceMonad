(** Real-time Banker's Queue *)

(** Operations take non-amortized constant time. *)

(* TODO: following BankersQueue we can formalize the amortized complexity bounds.
   But how can we formalize the stronger non-amortized bounds? *)

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

Record Queue (a : Type) : Type := MkQueue
  { front : list a
  ; back : list a
  ; schedule : list a
  }.

Definition empty {a} : Queue a := MkQueue [] [] [].

(* rotate x y z = x ++ rev y ++ z *)
(* Assumes 1 + length f = length b *)
Fixpoint rotate {a} (f b d : list a) : list a :=
  match f, b with
  | [], y :: _ => y :: d
  | x :: f, y :: b => x :: rotate f b (y :: d)
  | _, [] => []  (* Should never happen *)
  end.

Definition mkQueue {a} (f b s : list a) : Queue a :=
  match s with
  | [] => let f := rotate f b [] in MkQueue f [] f
  | _ :: s => MkQueue f b s
  end.

Definition push {a} (q : Queue a) (x : a) : Queue a :=
  mkQueue (front q) (x :: back q) (schedule q).

Definition pop {a} (q : Queue a) : option (a * Queue a) :=
  match front q with
  | [] => None
  | x :: f => Some (x, mkQueue f (back q) (schedule q))
  end.

Record QueueA (a : Type) : Type := MkQueueA
  { frontA : T (listA a)
  ; backA : T (listA a)
  ; scheduleA : T (listA a) }.

Definition emptyA {a : Type} : QueueA a := let n := Thunk NilA in MkQueueA n n n.

Fixpoint rotateA_ {a} (f b : listA a) (d : T (listA a)) : M (listA a) :=
  tick >>
  match f, b with
  | NilA, ConsA y _ => ret (ConsA y d)
  | ConsA x f, ConsA y b =>
    forcing f (fun f =>
    let! b := force b in
    let~ r := rotateA_ f b (Thunk (ConsA y d)) in
    ret (ConsA x r))
  | _, NilA => ret NilA  (* Should not happen *)
  end.

Definition rotateA {a} (f b d : T (listA a)) : M (listA a) :=
  let! f := force f in
  let! b := force b in
  rotateA_ f b d.

Definition mkQueueA {a} (f b s : T (listA a)) : M (QueueA a) :=
  tick >>
  let! s := force s in
  match s with
  | NilA =>
    let~ f' := rotateA f b (Thunk NilA) in
    ret (MkQueueA f' (Thunk NilA) f')
  | ConsA _ s' =>
    ret (MkQueueA f b s')
  end.

Definition pushA {a} (q : T (QueueA a)) (x : T a) : M (QueueA a) :=
  tick >>
  let! q := force q in
  mkQueueA (frontA q) (Thunk (ConsA x (backA q))) (scheduleA q).

Definition popA {a} (q : T (QueueA a)) : M (option (T a * T (QueueA a))) :=
  tick >>
  let! q := force q in
  let! front_q := force (frontA q) in
  match front_q with
  | NilA => ret None
  | ConsA x f => let~ q := mkQueueA f (backA q) (scheduleA q) in ret (Some (x, q))
  end.

Import Tick.Notations.

Definition headX {a} (xs : T (listA a)) : T a :=
  match xs with
  | Thunk (ConsA x _) => x
  | _ => Undefined
  end.

Fixpoint rotateD {a} (f b d : list a) (out : listA a)
  : Tick (T (listA a) * T (listA a) * T (listA a)) :=
  Tick.tick >>
  match f, b, out with
  | [], _ :: _, ConsA y' d' => Tick.ret (Thunk NilA, Thunk (ConsA y' Undefined), d')
  | x :: f, y :: b, ConsA x' r' =>
    let+ (f', b', d') := thunkD (rotateD f b (y :: d)) r' in
    Tick.ret (Thunk (ConsA x' f'), Thunk (ConsA (headX d') b'), tailX d')
  | _, [], _ | _, _, NilA => bottom (* Should not happen *)
  end.

Definition mkQueueD {a} (f b s : list a) (out : QueueA a)
  : Tick (T (listA a) * T (listA a) * T (listA a)) :=
  Tick.tick >>
  match s with
  | [] =>
    let f' := lub (frontA out) (scheduleA out) in
    let+ (f', b', _) := thunkD (rotateD f b []) f' in
    Tick.ret (f', b', Thunk NilA)
  | _ :: _ => Tick.ret (frontA out, backA out, Thunk (ConsA Undefined (scheduleA out)))
  end.

Definition pushD {a} (q : Queue a) (x : a) (out : QueueA a) : Tick (T (QueueA a) * T a) :=
  Tick.tick >>
  let+ (f, b, d) := mkQueueD (front q) (x :: back q) (schedule q) out in
  Tick.ret (Thunk (MkQueueA f (tailX b) d), headX b).

Definition popD {a} (q : Queue a) (out : option (T (QueueA a) * T a)) : Tick (T (QueueA a)) :=
  Tick.tick >>
  match front q with
  | [] => Tick.ret (Thunk (MkQueueA (Thunk NilA) Undefined Undefined))
  | x :: f =>
    match out with
    | Some (qout, xout) =>
      let+ (f', b', s') := thunkD (mkQueueD f (back q) (schedule q)) qout in
      Tick.ret (Thunk (MkQueueA (Thunk (ConsA xout f')) b' s'))
    | None => bottom
    end
  end.

#[global] Instance Exact_Queue {a aA} `{Exact a aA} : Exact (Queue a) (QueueA aA) :=
  fun q => MkQueueA (exact (front q)) (exact (back q)) (exact (schedule q)).

Record less_defined_QueueA {a} `{LessDefined a} (q1 q2 : QueueA a) : Prop :=
  { ld_frontA : frontA q1 `less_defined` frontA q2
  ; ld_backA : backA q1 `less_defined` backA q2
  ; ld_scheduleA : scheduleA q1 `less_defined` scheduleA q2
  }.

#[global] Instance LessDefined_QueueA {a} `{LessDefined a} : LessDefined (QueueA a) :=
  less_defined_QueueA.

#[global] Instance PreOrder_LessDefined_QueueA {a} : PreOrder (less_defined (a := QueueA a)).
Proof.
  constructor.
  - constructor; reflexivity.
  - intros x y z Hxy Hyz; constructor; etransitivity; solve [apply Hxy|apply Hyz].
Qed.

Ltac injclear H := injection H; clear H.

Lemma thunkD_spec {a0 a b} `{Exact a0 a} `{LessDefined a} `{Bottom a}
    (fD : a0 -> b -> Tick a) (f : a -> M b) x outD
  : (forall outD' xD dcost, Tick.MkTick dcost xD = fD x outD' ->
     f xD [[ fun out cost => outD' `less_defined` out /\ cost <= dcost ]]) ->
    forall xD dcost, Tick.MkTick dcost xD = thunkD (fD x) outD ->
    thunk (f xD) [[ fun out cost => outD `less_defined` out /\ cost <= dcost ]].
Proof.
  intros Hf xD dcost Hdcost.
  destruct outD as [ outD | ].
  - apply optimistic_thunk_go. eapply optimistic_mon; [ apply Hf; eassumption | cbn ].
    intros * []; split; [ apply LessDefined_Thunk; auto | auto ].
  - apply optimistic_skip. split; [ reflexivity | lia ].
Qed.

Lemma thunkD_3_spec {a1' a2' a3' a1 a2 a3 b}
    `{Exact a1' a1, Exact a2' a2, Exact a3' a3}
    `{LessDefined a1, LessDefined a2, LessDefined a3}
    `{Bottom a1, Bottom a2, Bottom a3}
    (fD : a1' -> a2' -> a3' -> b -> Tick (a1 * a2 * a3)) (f : a1 -> a2 -> a3 -> M b)
    x1 x2 x3 outD
  : (forall outD' x1D x2D x3D dcost, Tick.MkTick dcost (x1D, x2D, x3D) = fD x1 x2 x3 outD' ->
     f x1D x2D x3D [[ fun out cost => outD' `less_defined` out /\ cost <= dcost ]]) ->
    forall x1D x2D x3D dcost, Tick.MkTick dcost (x1D, x2D, x3D) = thunkD (fD x1 x2 x3) outD ->
    thunk (f x1D x2D x3D) [[ fun out cost => outD `less_defined` out /\ cost <= dcost ]].
Proof.
  intros Hf x1D x2D x3D dcost Hdcost.
  destruct outD as [ outD | ].
  - apply optimistic_thunk_go. eapply optimistic_mon; [ apply Hf; eassumption | cbn ].
    intros * []; split; [ apply LessDefined_Thunk; auto | auto ].
  - apply optimistic_skip. split; [ reflexivity | lia ].
Qed.

Lemma rotateD_spec {a} {f b : list a} (outD : _)
  : outD `is_approx` rotate f b [] ->
    forall fD bD sD dcost, Tick.MkTick dcost (fD, bD, sD) = rotateD f b [] outD ->
    rotateA fD bD (Thunk NilA) [[ fun out cost => outD `less_defined` out /\ cost <= dcost ]].
Proof.
Admitted.

Lemma mkQueueD_spec {a} (f b s : list a) (outD : QueueA a)
  : outD `is_approx` mkQueue f b s ->
    forall fD bD sD dcost, Tick.MkTick dcost (fD, bD, sD) = mkQueueD f b s outD ->
    mkQueueA fD bD sD [[ fun out cost => outD `less_defined` out /\ cost <= dcost ]].
Proof.
  intros HoutD fD bD sD dcost Hdcost.
  unfold mkQueueA. mgo_.
  unfold mkQueueD in Hdcost.
  destruct s as [| x0 s ].
  - destruct thunkD as [dcost' [ [fD' bD'] sD'] ] eqn:Edcost' in Hdcost.
    unfold Tick.bind in Hdcost; cbn in Hdcost.
    injclear Hdcost; intros -> <- <- ->.
    mgo_.
    (* TODO: how to handle thunk *)
    destruct (lub _ _) eqn:Elub in Edcost'; cbn in Edcost'.
    + apply optimistic_thunk_go.
      eapply optimistic_mon.
      { eapply rotateD_spec; [ | symmetry; apply Edcost'].
        apply less_defined_Thunk_inv. rewrite <- Elub.
        apply lub_least_upper_bound; apply HoutD. }
      cbn; intros ? ? [ ]; mgo_.
      split; [ | lia].
      assert (Hcobounded : cobounded (frontA outD) (scheduleA outD)).
      { exists (exact (rotate f b [])); split; apply HoutD. }
      constructor; cbn; [ | apply HoutD | ].
      all: etransitivity; [ | apply LessDefined_Thunk; eassumption ].
      all: rewrite <- Elub.
      { apply lub_upper_bound_l; assumption. }
      { apply lub_upper_bound_r; assumption. }
    + apply optimistic_skip. mgo_. split; [ | lia ].
      assert (Hcobounded : cobounded (frontA outD) (scheduleA outD)).
      { exists (exact (rotate f b [])); split; apply HoutD. }
      constructor; cbn.
      { rewrite <- Elub; apply lub_upper_bound_l; assumption. }
      { apply HoutD. }
      { rewrite <- Elub; apply lub_upper_bound_r; assumption. }
  - unfold Tick.bind in Hdcost; cbn in Hdcost.
    injclear Hdcost; intros -> -> -> ->. mgo_.
    split; reflexivity.
Qed.

Lemma pushD_spec {a} (q : Queue a) (x : a) (outD : QueueA a)
  : outD `is_approx` push q x ->
    forall qD xD dcost, Tick.MkTick dcost (qD, xD) = pushD q x outD ->
    pushA qD xD [[ fun out cost => outD `less_defined` out /\ cost <= dcost ]].
Proof.
  intros HoutD qD xD dcost Hdcost.
  unfold pushA, pushD in *.
  mgo_.
Admitted.

Lemma pushD_lowspec {a} (q : Queue a) (x : a) (outD : QueueA a)
  : outD `is_approx` push q x ->
    forall qD xD dcost, Tick.MkTick dcost (qD, xD) = pushD q x outD ->
    pushA qD xD [[ fun out cost => outD `less_defined` out -> dcost <= cost ]].
Proof.
Admitted.

Definition debt_ {a} (q : Queue a) (qA : QueueA a) : nat :=
  max (sizeX 1 (scheduleA qA)) (sizeX 1 (frontA qA) - length (back q)).

Definition debt {a} (q : Queue a) (qA : T (QueueA a)) : nat :=
  match qA with
  | Undefined => 0
  | Thunk qA => debt_ q qA
  end.

Definition wf_Queue {a} (q : Queue a) : Prop :=
  length (front q) = length (back q) + length (schedule q).

Definition rpost (a a' : Type) : Type := a -> a' -> nat -> nat -> Prop.

(* "Relational specification" *)
Definition rspec {a} (u u' : Tick a) (P : rpost a a) : Prop :=
  P (Tick.val u) (Tick.val u') (Tick.cost u) (Tick.cost u').

Lemma bind_rspec {a b} (u u' : Tick a) (k k' : a -> Tick b) (P : rpost b b)
  : rspec u u' (fun x x' nx nx' =>
      rspec (k x) (k' x') (fun y y' ny ny' =>
        P y y' (nx + ny) (nx' + ny'))) ->
    rspec (Tick.bind u k) (Tick.bind u' k') P.
Admitted.

Lemma ret_rspec {a} (x x' : a) (P : rpost a a)
  : P x x' 0 0 -> rspec (Tick.ret x) (Tick.ret x') P.
Proof. exact (fun H => H). Qed.

Lemma tick_rspec (P : rpost unit unit)
  : P tt tt 1 1 -> rspec Tick.tick Tick.tick P.
Proof. exact (fun H => H). Qed.

(*
Lemma thunkD_rspec {a b} `{Bottom b} (f f' : a -> Tick b) (P : rpost b b) (d d' : T a)
  : (forall e e', d = Thunk e -> d' = Thunk e' -> rspec (f e) (f' e') P) ->
    rspec (thunkD f d) (thunkD f d') P.
*)

Lemma mono_rspec {a} (u u' : Tick a) (P Q : rpost a a)
  : (forall x x' n n', P x x' n n' -> Q x x' n n') -> rspec u u' P -> rspec u u' Q.
Proof. exact (fun H => H _ _ _ _). Qed.

Lemma and_rspec {a} (u u' : _ a) (P Q : rpost a a)
  : rspec u u' P -> rspec u u' Q -> rspec u u' (fun x x' n n' => P x x' n n' /\ Q x x' n n').
Proof.
  exact (@conj _ _).
Qed.

Lemma l_val_rspec {a} (u u' : _ a) (P : a -> Prop)
  : P (Tick.val u) -> rspec u u' (fun x _ _ _ => P x).
Proof.
  exact (fun x => x).
Qed.

Lemma r_val_rspec {a} (u u' : _ a) (P : a -> Prop)
  : P (Tick.val u') -> rspec u u' (fun _ x _ _ => P x).
Proof.
  exact (fun x => x).
Qed.

(* Direct approach: find simple formulas for the demand functions *)

Lemma rotateD_cost {a} (f b d : list a) (outD : listA a)
  : outD `is_approx` rotate f b d ->
    Tick.cost (rotateD f b d outD) = min (sizeX' 1 outD) (S (length f)).
Proof.
  revert b d outD; induction f as [ | x f IH ]; intros [ | y b] * Hout; cbn in *; f_equal.
  - destruct outD as [ | ? [] ]; cbn; try rewrite Nat.min_0_r; reflexivity.
  - rewrite exact_list_unfold_cons in Hout. inversion Hout; subst; cbn.
    destruct xs; cbn; [ rewrite Nat.min_0_r | ]; reflexivity.
  - rewrite exact_list_unfold_nil in Hout. inversion Hout; subst; cbn. reflexivity.
  - rewrite exact_list_unfold_cons in Hout. inversion Hout; subst; cbn.
    inversion H3; subst; cbn; [ reflexivity | ].
    rewrite IH; auto.
    destruct (Tick.val _) as [ [? ?] ? ]; cbn. rewrite Nat.add_0_r; reflexivity.
Qed.

Lemma mkQueueD_cost {a} (f b s : list a) (outD : QueueA a)
  : outD `is_approx` mkQueue f b s ->
    Tick.cost (mkQueueD f b s outD) =
      match s with
      | [] => 1 + min (sizeX 1 (lub (frontA outD) (scheduleA outD))) (S (length f))
      | _ :: _ => 1
      end.
Proof.
  unfold mkQueue, mkQueueD. intros Hout.
  destruct s; cbn; [ | reflexivity ].
  unfold exact, Exact_Queue in Hout; cbn in Hout. destruct Hout; cbn in *.
  f_equal. destruct (lub _ _) eqn:H; cbn in *; [ | reflexivity ].
  rewrite rotateD_cost; auto.
  { destruct (Tick.val _) as [ [? ?] ?]; cbn; rewrite Nat.add_0_r; reflexivity. }
  { apply less_defined_Thunk_inv. rewrite <- H.
    apply lub_least_upper_bound; auto. }
Qed.

(* Relational approach: ???
   (should be more general/mechanizable) *)

Lemma rotateD_rcost {a} (f b d : list a) (outD outD' : listA a)
  : S (length f) = length b ->
    outD' `is_approx` rotate f b d ->
    outD `less_defined` outD' ->
    rspec (rotateD f b d outD) (rotateD f b d outD') (fun '(fD, bD, dD) '(fD', bD', dD') n n' =>
       n' + min (sizeX' 1 outD) (S (length f)) <= n  + min (sizeX' 1 outD') (S (length f))).
Proof.
Admitted.

Lemma rotateD_rcost' {a} (f b d : list a) (outD outD' : T (listA a))
  : S (length f) = length b ->
    outD' `is_approx` rotate f b d ->
    outD `less_defined` outD' ->
    rspec (thunkD (rotateD f b d) outD) (thunkD (rotateD f b d) outD') (fun '(fD, bD, dD) '(fD', bD', dD') n n' =>
       n' + min (sizeX 1 outD) (S (length f)) <= n  + min (sizeX 1 outD') (S (length f))).
Proof.
  intros Hf Happrox Hld. destruct Hld as [ outD_ | Hld ]; cbn.
  - destruct outD_; cbn; [ | auto ].
    destruct (Tick.val _) as [ [fD bD] dD] eqn:Ev.
    rewrite rotateD_cost; [ lia | ].
    apply less_defined_Thunk_inv; auto.
  - apply rotateD_rcost; auto. apply less_defined_Thunk_inv; auto.
Qed.

Lemma rotateD_sound {a} (f b d : list a) (outD : listA a)
  : outD `is_approx` rotate f b d ->
    Tick.val (rotateD f b d outD) `is_approx` (f, b, d).
Proof.
  revert b d outD; induction f; intros [] d outD Hout; cbn.
  - repeat constructor.
  - destruct outD; cbn.
    + repeat constructor.
    + cbn in Hout. rewrite exact_list_unfold_cons in Hout. inversion Hout; subst.
      repeat constructor; cbn in *; auto.
      rewrite exact_list_unfold_cons; auto.
  - repeat constructor.
  - destruct outD; cbn.
    + repeat constructor.
    + cbn in Hout. rewrite exact_list_unfold_cons in Hout. inversion Hout; subst. destruct x2; cbn.
      * apply less_defined_Thunk_inv in H4.
        specialize (IHf l (a1 :: d) x H4).
        inversion IHf as [ [HH1 HH2] HH3]; destruct (Tick.val (rotateD _ _ _ _)) as [ [f' b'] d'];
          cbn in *.
        repeat (constructor; cbn); try (rewrite exact_list_unfold_cons; constructor); auto.
        { inversion HH3; subst; cbn; auto. rewrite exact_list_unfold_cons in H1.
          inversion H1; subst. auto. }
        { inversion HH3; subst; cbn; auto. rewrite exact_list_unfold_cons in H1.
          inversion H1; subst. auto. }
      * repeat (constructor; cbn; try rewrite exact_list_unfold_cons); auto.
Qed.

Lemma thunkD_sound {a' a b' b} `{BottomLeast b, Exact b' b, Exact a' a, LessDefined a}
    (f : a -> Tick b) (x : b') (out : a')
  : (forall outD_, outD_ `is_approx` out -> Tick.val (f outD_) `is_approx` x) ->
    forall outD : T a, outD `is_approx` out -> Tick.val (thunkD f outD) `is_approx` x.
Proof.
  intros Hf outD Hout. destruct outD; cbn.
  - apply Hf. apply less_defined_Thunk_inv; auto.
  - apply bottom_least.
Qed.

Lemma sizeX1_length {a} (x : T (listA a)) (y : list a)
  : x `is_approx` y -> sizeX 1 x <= 1 + length y.
Proof.
Admitted.

(* need rotateD_spec (result is approximation of input) *)
Lemma mkQueueD_rcost {a} (f b s : list a) (outD outD' : QueueA a)
  : S (length f) = length b + length s ->
    outD' `is_approx` mkQueue f b s ->
    outD `less_defined` outD' ->
    rspec (mkQueueD f b s outD) (mkQueueD f b s outD') (fun '(fD, bD, sD) '(fD', bD', sD') n n' =>
       n' + max (sizeX 1 sD') (1 + sizeX 1 fD' - length b) + debt_ (mkQueue f b s) outD
    <= n  + max (sizeX 1 sD ) (1 + sizeX 1 fD  - length b) + debt_ (mkQueue f b s) outD').
Proof.
  unfold mkQueue, mkQueueD.
  intros Hf Hout Hout'.
  apply bind_rspec, tick_rspec.
  destruct s eqn:Es.
  - apply bind_rspec.
    assert (Hlub : lub (frontA outD) (scheduleA outD) `less_defined` lub (frontA outD') (scheduleA outD')).
    { admit. }
    cbn in Hf; rewrite Nat.add_0_r in Hf.
    remember (lub (frontA outD) (scheduleA outD)) as x eqn:Ex.
    remember (lub (frontA outD') (scheduleA outD')) as y eqn:Ey.
    assert (y `less_defined` exact (rotate f b [])).
    { subst y; apply lub_least_upper_bound; apply Hout. }
    eapply mono_rspec; [ | apply and_rspec;
      [ apply rotateD_rcost'; auto | apply and_rspec;
          [ eapply l_val_rspec with (P := (fun v => v `less_defined` _));
            eapply thunkD_sound;
            [ exact (@rotateD_sound _ f b []) | etransitivity; eassumption ]
          | eapply r_val_rspec with (P := (fun v => v `less_defined` _));
            eapply thunkD_sound;
            [ apply (@rotateD_sound _ f b []) | auto ] ] ] ].
    intros [ [fD bD] dD] [ [fD' bD'] dD'] n n' [Hrotate [ [ [HfD HbD] HdD] [ [HfD' HbD'] HdD'] ] ].
    cbn [fst snd exact Exact_prod Exact_id id] in *.
    apply ret_rspec; unfold debt_; cbn [front back schedule sizeX sizeX' length].
    assert (sizeX 1 fD' <= length b).
    { apply sizeX1_length in HfD'. lia. }
    assert (sizeX 1 fD <= length b).
    { apply sizeX1_length in HfD. lia. }
    assert (sizeX 1 x = max (sizeX 1 (scheduleA outD)) (sizeX 1 (frontA outD))).
    { admit. }
    assert (sizeX 1 y = max (sizeX 1 (scheduleA outD')) (sizeX 1 (frontA outD'))).
    { admit. }
    rewrite 2 Nat.sub_0_r, <- H2, <- H3.
    assert (sizeX 1 x <= sizeX 1 y).
    { admit. }
    revert H0 H1 H2 H3 H4 Hrotate; clear; lia.
  - apply ret_rspec. unfold debt_.
    destruct Hout' as [Hfront Hback Hsch].
    do 2 destruct (scheduleA _); cbn [sizeX' sizeX back]; lia.
Admitted.

Lemma pushD_rcost {a} (q : Queue a) (x : a) (outD outD' : QueueA a)
  : wf_Queue q ->
    outD' `is_approx` push q x ->
    outD `less_defined` outD' ->
    rspec (pushD q x outD) (pushD q x outD') (fun '(qD, xD) '(qD', xD') n n' =>
       n' + debt q qD' + debt_ (push q x) outD
    <= n  + debt q qD  + debt_ (push q x) outD').
Proof.
  intros Hq Hout Hout'.
  unfold pushD, push.
  apply bind_rspec, tick_rspec.
  apply bind_rspec. eapply mono_rspec; [ | apply mkQueueD_rcost; auto ]; cbn.
  2:{ f_equal. apply Hq. }
  intros [ [fD bD] sD] [ [fD' bD'] sD'] n n' HmkQueue.
  apply ret_rspec. revert HmkQueue; cbn.
  remember (debt_ (mkQueue _ _ _) outD).
  remember (debt_ (mkQueue _ _ _) outD').
  unfold debt_; cbn.
  lia.
Qed.

(*********************************)
