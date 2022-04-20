(** Real-time Banker's Queue *)

(** Operations take non-amortized constant time. *)

(* TODO: following BankersQueue we can formalize the amortized complexity bounds.
   But how can we formalize the stronger non-amortized bounds? *)

From Coq Require Import List Arith Lia.
From Clairvoyance Require Import Core Approx ApproxM List Misc BankersQueue.
From Clairvoyance Require Launchbury.

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

Lemma pushD_spec {a} (q : Queue a) (x : a) (outD : QueueA a)
  : outD `is_approx` push q x ->
    forall qD xD dcost, Tick.MkTick dcost (qD, xD) = pushD q x outD ->
    pushA qD xD {{ fun out cost => outD `less_defined` out /\ cost <= dcost }}.
Proof.
Admitted.

Lemma pushD_lowspec {a} (q : Queue a) (x : a) (outD : QueueA a)
  : outD `is_approx` push q x ->
    forall qD xD dcost, Tick.MkTick dcost (qD, xD) = pushD q x outD ->
    pushA qD xD [[ fun out cost => outD `less_defined` out -> dcost <= cost ]].
Proof.
Admitted.

Definition debt_ {a} (q : Queue a) (qA : QueueA a) : nat :=
  max (sizeX 0 (scheduleA qA)) (sizeX 0 (frontA qA) - length (back q)).

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
       n' + min (sizeX' 1 outD) (length f) <= n  + min (sizeX' 1 outD') (length f)).
Proof.
Admitted.

(* need rotateD_spec (result is approximation of input) *)
Lemma mkQueueD_rcost {a} (f b s : list a) (outD outD' : QueueA a)
  : S (length f) = length b + length s ->
    outD' `is_approx` mkQueue f b s ->
    outD `less_defined` outD' ->
    rspec (mkQueueD f b s outD) (mkQueueD f b s outD') (fun '(fD, bD, sD) '(fD', bD', sD') n n' =>
       n' + max (sizeX 0 sD') (sizeX 0 fD' - length b) + debt_ (mkQueue f b s) outD
    <= n  + max (sizeX 0 sD ) (sizeX 0 fD  - length b) + debt_ (mkQueue f b s) outD').
Proof.
  unfold mkQueue, mkQueueD.
  intros Hf Hout Hout'.
  apply bind_rspec, tick_rspec.
  destruct s.
  - apply bind_rspec.
    assert (Hlub : lub (frontA outD) (scheduleA outD) `less_defined` lub (frontA outD') (scheduleA outD')).
    { admit. }
    inversion Hlub.
    + cbn. admit.
    + cbn. eapply mono_rspec; [ | apply rotateD_rcost; auto ]; cbn.
      2,3: admit.
      intros [ [fD bD] dD] [ [fD' bD'] dD'] n n' Hrotate.
      apply ret_rspec. cbn.
      unfold debt_; cbn.
      admit.
  - apply ret_rspec. cbn. admit.
Admitted.

Lemma pushD_rcost {a} (q : Queue a) (x : a) (outD outD' : QueueA a)
  : outD' `is_approx` push q x ->
    outD `less_defined` outD' ->
    rspec (pushD q x outD) (pushD q x outD') (fun '(qD, xD) '(qD', xD') n n' =>
       n' + debt q qD' + debt_ (push q x) outD
    <= n  + debt q qD  + debt_ (push q x) outD').
Proof.
  intros Hout Hout'.
  unfold pushD, push.
  apply bind_rspec, tick_rspec.
  apply bind_rspec. eapply mono_rspec; [ | apply mkQueueD_rcost; solve [auto] ]; cbn.
  intros [ [fD bD] sD] [ [fD' bD'] sD'] n n' HmkQueue.
  apply ret_rspec. revert HmkQueue; cbn.
  remember (debt_ (mkQueue _ _ _) outD).
  remember (debt_ (mkQueue _ _ _) outD').
  unfold debt_; cbn.
  assert (HH : sizeX 0 fD <= sizeX 0 fD'). admit.
  admit.
Admitted.

(*********************************)

Import Clairvoyance.Launchbury.
Import L.Notations.

Record QueueF (t : Type -> Type) (_list : Type) (_Q : Type) : Type := MkQueueF
  { frontF : t _list
  ; backF : t _list
  ; scheduleF : t _list
  }.

#[global] Instance Data_QueueA {a} : Data (QueueF T (listA a)) :=
  {| d_ := QueueA a
  ;  des := fun q => {| frontF := frontA q ; backF := backA q ; scheduleF := scheduleA q |}
  ;  con := fun q => {| frontA := frontF q ; backA := backF q ; scheduleA := scheduleF q |}
  |}.

Section F.
Context {t a} {list_ : Data (listF t a)} {Queue_ : Data (QueueF t list_)}.

Definition emptyF : L t Queue_ :=
  let^~ f := L.ret (con NilF) in
  L.ret (con {| frontF := f ; backF := f ; scheduleF := f |}).

CoFixpoint rotateF (f b d : t list_) : L t list_ :=
  let^ f := L.force f in
  let^ b := L.force b in
  match des f, des b with
  | NilF, ConsF y _ => L.ret (con (ConsF y d))
  | ConsF x f, ConsF y b =>
    let^~ d := L.ret (con (ConsF y d)) in
    let^~ r := rotateF f b d in
    L.ret (con (ConsF x r))
  | _, _ => L.ret (con NilF) (* should not happen *)
  end.

Definition mkQueueF (f b s : t list_) : L t Queue_ :=
  let^ _ := L.tick in
  let^ s := L.force s in
  match des s with
  | NilF =>
    let^~ z := L.ret (con NilF) in
    let^~ f := rotateF f b z in
    L.ret (con (MkQueueF f z f))
  | ConsF _ s' => L.ret (con (MkQueueF f b s'))
  end.

Definition pushF (q : t Queue_) (x : t a) : L t Queue_ :=
  let^ _ := L.tick in
  let^ q := L.force q in
  let q := des q in
  let^~ b := L.ret (con (ConsF x (backF q))) in
  mkQueueF (frontF q) b (scheduleF q).

Definition popF (q : t Queue_) : L t (option (t a * t Queue_)) :=
  let^ _ := L.tick in
  let^ q := L.force q in
  let q := des q in
  let^ f := L.force (frontF q) in
  match des f with
  | NilF => L.ret None
  | ConsF x f =>
    let^~ q := mkQueueF f (backF q) (scheduleF q) in
    L.ret (Some (x, q))
  end.

End F.
