From Coq Require Import Arith Psatz Relations RelationClasses.
From Clairvoyance Require Import Core Approx ApproxM Tick Prod Option FormalTranslation.

From Hammer Require Import Tactics.

Import Tick.Notations.
Open Scope tick_scope.

Set Implicit Arguments.
Set Contextual Implicit.
Set Maximal Implicit Insertion.

#[local] Existing Instance Exact_id | 1.

(* Auxiliary stuff *)

(* Tear a goal down by destructing on every case that the goal matches on. *)
Ltac teardown := repeat (simpl; match goal with
                                | [_ : context [match ?x with _ => _ end] |- _ ] => destruct x
                                | [_ : context [if ?x then _ else _] |- _ ] => destruct x
                                | |- context [match ?x with _ => _ end] => destruct x
                                | |- context [if ?x then _ else _] => destruct x
                                end).

Ltac teardown_eqns := repeat (simpl; match goal with
                                     | |- context [match ?x with _ => _ end] =>
                                         let H := fresh "H" in destruct x eqn:H
                                     | |- context [if ?x then _ else _] =>
                                         let H := fresh "H" in destruct x eqn:H
                                     end).

Ltac keep_mgo_ :=
  mgo_; repeat (apply optimistic_thunk_go; mgo_).

Ltac mgo_brute_force :=
  solve [mgo_; repeat ((apply optimistic_skip + apply optimistic_thunk_go); mgo_)].

(* I have had some problems with inversion_clear. This does the same thing, but
   hopefully better. Note that it might not work as expected if the inverted
   hypothesis "contains" equalities. *)
Tactic Notation "invert_clear" hyp(H) "as" simple_intropattern(pat) :=
  (* Rename the original hypothesis so that its name can be reused if
     desired. *)
  let H' := fresh "H'" in
  rename H into H';
  (* Mark our place in the context with a trivial hypothesis. *)
  let HI := fresh "HI" in
  pose I as HI;
  (* Perform the inversion, possibly adding some equalities to the bottom of the
     context. *)
  inversion H' as pat;
  (* Substitute equalities from the bottom up, stopping when we reach a
     non-equality hypothesis. *)
  repeat lazymatch goal with
    | _ : ?type |- _ => match type with
                        | ?x = ?y => subst x + subst y
                        end
    end;
  (* Clear the marker and the original hypothesis. *)
  clear HI;
  clear H'.

Tactic Notation "invert_clear" hyp(H) :=
  invert_clear H as [ ].

Tactic Notation "invert_clear" integer(n) "as" simple_intropattern(pat) :=
  progress (intros until n);
  match goal with
  | H : _ |- _ => invert_clear H as pat
  end.

(* For some reason, trying to chain this into the above notation causes
   problems. *)
Tactic Notation "invert_clear" integer(n) :=
  progress (intros until n);
  match goal with
  | H : _ |- _ => invert_clear H as [ ]
  end.

(* Auxiliary tactic. *)
Ltac head_is_constructor t := match t with
                              | ?f ?x => head_is_constructor f
                              | _ => is_constructor t
                              end.

(* An incomplete tactic that indicates whether the head of a term
   is a constructor or projection. *)
Ltac head_is_constructor_or_proj t :=
  match t with
  | ?f ?x => head_is_constructor_or_proj f
  | fst => idtac
  | snd => idtac
  | _ => is_constructor t
  end.

(* Tactic to invert/subst/clear a single hypothesis of the form

   P x1 x2 ... (C y1 y2 ... ym) ... xn

   where C is a constructor. This is a common way to make progress. *)
Ltac invert_constructor :=
  let rec should_invert T := match T with
                             | ?P ?x => head_is_constructor x + should_invert P
                             end in
  intros;
  match goal with
  | H : ?T |- _ => should_invert T; invert_clear H
  end.

(* Prove that a relation is a partial order by showing that it is a preorder and
   that it is antisymmetric. *)
Lemma make_partial_order A (R : A -> A -> Prop) `{PreOrder A R} :
  (forall (x y : A), R x y -> R y x -> x = y) -> PartialOrder eq R.
Proof.
  intros.
  unfold PartialOrder, relation_equivalence, predicate_equivalence, pointwise_lifting, relation_conjunction,
    predicate_intersection, pointwise_extension, Basics.flip.
  split.
  - destruct 1. split; reflexivity.
  - intros [ H1 H2 ]. apply H0; auto.
Qed.

Lemma LessDefined_T_antisym A `{LessDefined A} :
  (forall (x y : A), x `less_defined` y -> y `less_defined` x -> x = y) ->
  forall (x y : T A), x `less_defined` y -> y `less_defined` x -> x = y.
Proof.
  intro. repeat invert_clear 1; try f_equal; auto.
Qed.
#[global] Hint Resolve LessDefined_T_antisym.

#[global] Instance PartialOrder_LessDefined_T (A : Type)
  `{LessDefined A, PartialOrder A eq less_defined} :
  PartialOrder eq (@less_defined (T A) _).
Proof.
  apply make_partial_order, LessDefined_T_antisym. firstorder.
Qed.

Definition forceD (A : Type) (y : A) (u : T A) : A :=
  match u with
  | Undefined => y
  | Thunk x => x
  end.

(* Actual important stuff begins here. *)

Inductive Front A :=
| FOne : A -> Front A
| FTwo : A -> A -> Front A.
#[global] Hint Constructors Front : core.

Inductive FrontA A :=
| FOneA : T A -> FrontA A
| FTwoA : T A -> T A -> FrontA A.
#[global] Hint Constructors FrontA : core.

Inductive LessDefined_FrontA A `{LessDefined A} : LessDefined (FrontA A) :=
| LessDefined_FOneA x1 x2 : x1 `less_defined` x2 -> FOneA x1 `less_defined` FOneA x2
| LessDefined_FTwoA x1 x2 y1 y2 :
  x1 `less_defined` x2 -> y1 `less_defined` y2 -> FTwoA x1 y1 `less_defined` FTwoA x2 y2.
#[global] Hint Constructors LessDefined_FrontA : core.
#[global] Existing Instance LessDefined_FrontA.

Lemma LessDefined_FrontA_refl A `{LessDefined A} :
  (forall (x : A), x `less_defined` x) -> forall (x : FrontA A), x `less_defined` x.
Proof.
  destruct x;
    repeat match goal with t: T A |- _ => destruct t end;
    auto.
Qed.
#[global] Hint Resolve LessDefined_FrontA_refl : core.

#[global] Instance Reflexive_LessDefined_FrontA A `{LessDefined A, Reflexive A less_defined} :
  Reflexive (@less_defined (FrontA A) _).
Proof.
  unfold Reflexive. auto.
Qed.

Lemma LessDefined_FrontA_trans A `{LessDefined A} :
  (forall (x y z : A), x `less_defined` y -> y `less_defined` z -> x `less_defined` z) ->
  forall (x y z : FrontA A), x `less_defined` y -> y `less_defined` z -> x `less_defined` z.
Proof.
  intro.
  repeat invert_clear 1;
    repeat match goal with
      | H : ?x `less_defined` ?y |- _ => invert_clear H
      end;
    repeat constructor; eauto.
Qed.
#[global] Hint Resolve LessDefined_FrontA_trans : core.

#[global] Instance Transitive_LessDefined_FrontA A `{LessDefined A, Transitive A less_defined} :
  Transitive (@less_defined (FrontA A) _).
Proof.
  unfold Transitive. eauto.
Qed.

#[global] Instance PreOrder_LessDefined_FrontA A `{LDA : LessDefined A, PreOrder A LDA} :
  PreOrder (@less_defined (FrontA A) _).
Proof.
  destruct H. constructor; eauto.
Qed.

Lemma LessDefined_FrontA_antisym A `{LessDefined A} :
  (forall (x y : A), x `less_defined` y -> y `less_defined` x -> x = y) ->
  forall (x y : FrontA A), x `less_defined` y -> y `less_defined` x -> x = y.
Proof.
  intro. repeat inversion_clear 1;
    repeat match goal with
      | H : ?x `less_defined` ?y |- _ => invert_clear H
      end;
    f_equal; eauto.
Qed.
#[global] Hint Resolve LessDefined_FrontA_antisym : core.

#[global] Instance PartialOrder_LessDefined_FrontA A `{LessDefined A} `{PartialOrder A eq less_defined} :
  PartialOrder eq (@less_defined (FrontA A) _).
Proof.
  apply make_partial_order. apply LessDefined_FrontA_antisym. firstorder.
Qed.

#[global] Instance Exact_Front A B `{Exact A B} : Exact (Front A) (FrontA B) :=
  fun u => match u with
           | FOne x => FOneA (exact x)
           | FTwo x y => FTwoA (exact x) (exact y)
           end.

#[global] Instance ExactMaximal_Front A B `{ExactMaximal B A} :
  ExactMaximal (FrontA B) (Front A).
Proof.
  intros xA []; unfold exact, Exact_Front; inversion 1; subst; f_equal.
  - destruct x2; unfold exact, Exact_T.
    + f_equal. apply H. inversion H2; subst. assumption.
    + inversion H2.
  - destruct x2; unfold exact, Exact_T.
    + f_equal. apply H. inversion H3; subst. assumption.
    + inversion H3.
  - destruct y2; unfold exact, Exact_T.
    + f_equal. apply H. inversion H5; subst. assumption.
    + inversion H5.
Qed.

#[global] Instance Lub_FrontA (A : Type) `{Lub A} : Lub (FrontA A) :=
  fun f1 f2 =>
    match f1, f2 with
    | FOneA x1, FOneA x2 => FOneA (lub x1 x2)
    | FTwoA x1 y1, FTwoA x2 y2 => FTwoA (lub x1 x2) (lub y1 y2)
    | _, _ => FOneA Undefined
    end.

#[global] Instance LubLaw_FrontA (A : Type)
  `{LDA : LessDefined A, Reflexive A less_defined, LBA : Lub A, @LubLaw _ LBA LDA} :
  LubLaw (FrontA A).
Proof.
  split.
  - repeat invert_clear 1; repeat constructor; apply lub_least_upper_bound; auto.
  - invert_clear 1. invert_clear H1.
    invert_clear H1; invert_clear H2; repeat constructor; apply lub_upper_bound_l; eauto.
  - invert_clear 1. invert_clear H1.
    invert_clear H1; invert_clear H2; repeat constructor; apply lub_upper_bound_r; eauto.
Qed.

Inductive Rear A : Type :=
| RZero : Rear A
| ROne : A -> Rear A.

Inductive RearA A : Type :=
| RZeroA : RearA A
| ROneA : T A -> RearA A.

Inductive LessDefined_RearA A `{LessDefined A} : LessDefined (RearA A) :=
| LessDefined_RZeroA : RZeroA `less_defined` RZeroA
| LessDefined_ROneA x1 x2 :
  x1 `less_defined` x2 -> ROneA x1 `less_defined` ROneA x2.
#[global] Hint Constructors LessDefined_RearA : core.
#[global] Existing Instance LessDefined_RearA.

Lemma LessDefined_RearA_refl A `{LessDefined A} :
  (forall (x : A), x `less_defined` x) -> forall (x : RearA A), x `less_defined` x.
Proof.
  destruct x;
    repeat match goal with t: T A |- _ => destruct t end;
    auto.
Qed.
#[global] Hint Resolve LessDefined_RearA_refl : core.

#[global] Instance Reflexive_LessDefined_RearA A `{LessDefined A, Reflexive A less_defined} :
  Reflexive (@less_defined (RearA A) _).
Proof.
  unfold Reflexive. auto.
Qed.

Lemma LessDefined_RearA_trans A `{LessDefined A} :
  (forall (x y z : A), x `less_defined` y -> y `less_defined` z -> x `less_defined` z) ->
  forall (x y z : RearA A), x `less_defined` y -> y `less_defined` z -> x `less_defined` z.
Proof.
  intro.
  repeat invert_clear 1;
    repeat match goal with
      | H : ?x `less_defined` ?y |- _ => invert_clear H
      end;
    repeat constructor; eauto.
Qed.
#[global] Hint Resolve LessDefined_RearA_trans : core.

#[global] Instance Transitive_LessDefined_RearA A `{LessDefined A, Transitive A less_defined} :
  Transitive (@less_defined (RearA A) _).
Proof.
  unfold Transitive. eauto.
Qed.

#[global] Instance PreOrder_LessDefined_RearA A `{LDA : LessDefined A, PreOrder A LDA} :
  PreOrder (@less_defined (RearA A) _).
Proof.
  destruct H. constructor; eauto.
Qed.

Lemma LessDefined_RearA_antisym A `{LessDefined A} :
  (forall (x y : A), x `less_defined` y -> y `less_defined` x -> x = y) ->
  forall (x y : RearA A), x `less_defined` y -> y `less_defined` x -> x = y.
Proof.
  intro. repeat inversion_clear 1;
    repeat match goal with
      | H : ?x `less_defined` ?y |- _ => invert_clear H
      end;
    f_equal; eauto.
Qed.
#[global] Hint Resolve LessDefined_RearA_antisym : core.

#[global] Instance PartialOrder_LessDefined_RearA A `{LessDefined A, PartialOrder A eq less_defined} :
  PartialOrder eq (@less_defined (RearA A) _).
Proof.
  apply make_partial_order. apply LessDefined_RearA_antisym. firstorder.
Qed.

#[global] Instance Exact_Rear A B `{Exact A B} : Exact (Rear A) (RearA B) :=
  fun u => match u with
           | RZero => RZeroA
           | ROne x => ROneA (exact x)
           end.

#[global] Instance Lub_RearA (A : Type) `{Lub A} : Lub (RearA A) :=
  fun r1 r2 =>
    match r1, r2 with
    | RZeroA, RZeroA => RZeroA
    | ROneA x1, ROneA x2 => ROneA (lub x1 x2)
    | _, _ => RZeroA
    end.

#[global] Instance LubLaw_RearA (A : Type)
  `{LDA : LessDefined A, Reflexive A less_defined, LBA : Lub A, @LubLaw _ LBA LDA} :
  LubLaw (RearA A).
Proof.
  split.
  - repeat invert_clear 1; repeat constructor; apply lub_least_upper_bound; auto.
  - invert_clear 1. invert_clear H1.
    invert_clear H1; invert_clear H2; repeat constructor; apply lub_upper_bound_l; eauto.
  - invert_clear 1. invert_clear H1.
    invert_clear H1; invert_clear H2; repeat constructor; apply lub_upper_bound_r; eauto.
Qed.

Inductive Queue (A : Type) : Type :=
| Nil : Queue A
| Deep : Front A -> Queue (A * A) -> Rear A -> Queue A.

Unset Elimination Schemes.

Inductive QueueA (A : Type) : Type :=
| NilA : QueueA A
| DeepA : T (FrontA A) -> T (QueueA (prodA A A)) -> T (RearA A) -> QueueA A.

Lemma QueueA_ind (P : forall A, QueueA A -> Prop) :
  (forall A, P A NilA) ->
  (forall A f m r, TR1 (P (prodA A A)) m -> P A (DeepA f m r)) ->
  forall (A : Type) (q : QueueA A), P A q.
Proof.
  intros HNilA HDeepA. fix SELF 2.
  destruct q.
  - apply HNilA.
  - apply HDeepA. destruct t0.
    + constructor. apply SELF.
    + constructor.
Qed.

Set Elimination Schemes.

Inductive LessDefined_QueueA A `{LessDefined A} : LessDefined (QueueA A) :=
| LessDefined_NilA : NilA `less_defined` NilA
| LessDefined_DeepA f1 f2 q1 q2 r1 r2 :
  f1 `less_defined` f2 -> q1 `less_defined` q2 -> r1 `less_defined` r2 ->
  DeepA f1 q1 r1 `less_defined` DeepA f2 q2 r2.
#[global] Hint Constructors LessDefined_QueueA : core.
#[global] Existing Instance LessDefined_QueueA.

Lemma LessDefined_QueueA_refl A `{LessDefined A, Reflexive A less_defined} :
  (forall (x : A), x `less_defined` x) -> forall (x : QueueA A), x `less_defined` x.
Proof.
  induction x.
  - constructor.
  - assert (@Reflexive (prodA A A) less_defined) by apply Reflexive_LessDefined_prodA.
    assert (@Reflexive (T (FrontA A)) less_defined) by apply Reflexive_LessDefined_T.
    assert (@Reflexive (T (RearA A)) less_defined) by apply Reflexive_LessDefined_T.
    constructor; auto.
    invert_clear H2; constructor. apply H2; auto.
Qed.
#[global] Hint Resolve LessDefined_QueueA_refl : core.

#[global] Instance Reflexive_LessDefined_QueueA A `{LDA : LessDefined A, !Reflexive LDA} :
  Reflexive (@less_defined (QueueA A) _).
Proof.
  unfold Reflexive. eauto.
Qed.

Lemma LessDefined_QueueA_trans A `{LessDefined A, Transitive A less_defined} :
  (forall (x y z : A), x `less_defined` y -> y `less_defined` z -> x `less_defined` z) ->
  forall (x y z : QueueA A), x `less_defined` y -> y `less_defined` z -> x `less_defined` z.
Proof.
  induction y.
  - repeat invert_clear 1. auto.
  - assert (@Transitive (T (FrontA A)) less_defined) by apply Transitive_LessDefined_T.
    assert (@Transitive (T (RearA A)) less_defined) by apply Transitive_LessDefined_T.
    assert (@Transitive (prodA A A) less_defined) by apply Transitive_LessDefined_prodA.
    repeat invert_clear 1. repeat constructor; try (etransitivity; eauto).
    invert_clear H2; repeat match goal with
                       | H : ?x `less_defined` ?y |- _ =>
                           (head_is_constructor x + head_is_constructor y); invert_clear H
                       end; constructor.
    apply H2; auto.
Qed.
#[global] Hint Resolve LessDefined_QueueA_trans : core.

#[global] Instance Transitive_LessDefined_QueueA A `{LDA : LessDefined A, Transitive A LDA} :
  Transitive (@less_defined (QueueA A) _).
Proof.
  unfold Transitive. eauto.
Qed.

#[global] Instance PreOrder_LessDefined_QueueA A `{LDA : LessDefined A, PreOrder A LDA} :
  PreOrder (@less_defined (QueueA A) _).
Proof.
  destruct H. constructor; eauto.
Qed.

(* You think you want this to be parameterized over TWO types; i.e.,

   `Exact (Queue A) (QueueA B).`

   You think you want that, but you don't.

   Why? Suppose we're trying to prove by induction a predicate that mentions
   `exact q`, where `q` is an expression of type `Queue A`, and we have not
   taken an instance argument whose type has the form `Exact A B`.

   Question: What `Exact` instance is being used in the theorem statement?

   Answer: `Exact_Queue A (Exact_id A)`.

   Now consider the case where we have an inductive hypothesis that mentions
   `exact m`, where `m` is an expression of type `Queue A`.

   Question: What `Exact` instance is being used in the inductive hypothesis?

   Answer: `Exact_Queue (A * A) (Exact_id (A * A))`, because this is the same
   instance that was used for the initial induction, except with A * A
   substituted for A.

   But suppose that `Exact_Queue` took two type arguments.

   Question: What `Exact` instance would be used in the `Deep` case?

   Answer: `Exact_Queue A B (Exact_prod A A Exact_id Exact_id) (Exact_prod B B
   Exact_id Exact_id)`.

   Since there is an instance mismatch, we will find the theorem impossible to
   prove without a tedious auxiliary lemma (if at all; I admit that I haven't
   tried very hard). Worse, the problem may not be immediately apparent, since
   Coq will reject terms that SEEM to have exactly the right type. *)
#[global] Instance Exact_Queue : forall A B `{Exact A B}, Exact (Queue A) (QueueA B) :=
  fix Exact_Queue A B _ q :=
    match q with
    | Nil => NilA
    | Deep f q r => DeepA (exact f) (Thunk (Exact_Queue _ _ _ q)) (exact r)
    end.

#[global] Instance BottomOf (A : Type) : BottomOf (QueueA A) :=
  fun q => match q with
           | NilA => NilA
           | DeepA _ _ _ => DeepA Undefined Undefined Undefined
           end.

#[global] Instance BottomIsLeast_QueueA (A : Type) `{LessDefined A} : BottomIsLeast (QueueA A).
Proof.
  invert_clear 1; repeat constructor.
Qed.

#[global] Instance Lub_QueueA : forall (A : Type) `{Lub A}, Lub (QueueA A) :=
  fix lub_QueueA (A : Type) _ (q1 q2 : QueueA A) :=
    match q1, q2 with
    | NilA, NilA => NilA
    | DeepA f1 m1 r1, DeepA f2 m2 r2 =>
        DeepA (lub f1 f2) (@lub _ (@Lub_T _ (lub_QueueA _ _)) m1 m2) (lub r1 r2)
    | _, _ => NilA
    end.

#[global] Instance LubLaw_QueueA (A : Type)
  `{LDA : LessDefined A, Reflexive A less_defined, LBA : Lub A, @LubLaw _ LBA LDA} :
  LubLaw (QueueA A).
Proof.
  split.
  - induction z; repeat invert_clear 1; repeat constructor;
      try solve [ apply lub_least_upper_bound; auto ].
    invert_clear H1; repeat match goal with
                       | H : ?x `less_defined` ?y |- _ =>
                           (head_is_constructor x + head_is_constructor y); invert_clear H
                       end; repeat constructor; auto.
      apply H1; auto.
      + apply Reflexive_LessDefined_prodA.
      + apply LubLaw_prodA.
  - induction x; invert_clear 1;
      match goal with
      | H : ?P /\ ?Q |- _ => invert_clear H
      end;
      repeat match goal with
        | H : ?x `less_defined` ?y |- _ =>
            (head_is_constructor x + head_is_constructor y); invert_clear H
        end; repeat constructor; try solve [ apply lub_upper_bound_l; eauto ].
    invert_clear H1; auto.
    repeat match goal with
           | H : ?x `less_defined` ?y |- _ =>
               (head_is_constructor x + head_is_constructor y); invert_clear H
           end; constructor; try reflexivity.
      apply H1.
    + apply Reflexive_LessDefined_prodA.
    + apply LubLaw_prodA.
    + eauto.
  - induction y; invert_clear 1;
      match goal with
      | H : ?P /\ ?Q |- _ => invert_clear H
      end;
      repeat match goal with
        | H : ?x `less_defined` ?y |- _ =>
            (head_is_constructor x + head_is_constructor y); invert_clear H
        end; repeat constructor; try solve [ apply lub_upper_bound_r; eauto ].
    invert_clear H1; auto.
    repeat match goal with
           | H : ?x `less_defined` ?y |- _ =>
               (head_is_constructor x + head_is_constructor y); invert_clear H
           end; constructor; try reflexivity.
    apply H1.
    + apply Reflexive_LessDefined_prodA.
    + apply LubLaw_prodA.
    + eauto.
Qed.

(* empty *)

Definition empty (A : Type) : Queue A := Nil.

Definition emptyD (A : Type) (outD : QueueA A) : Tick unit :=
  Tick.tick >>
    match outD with
    | NilA => Tick.ret tt
    | _ => bottom
    end.

From Clairvoyance Require Import Core.

Definition emptyA (A : Type) : M (QueueA A) := tick >> ret NilA.

Lemma emptyD_spec (A : Type) `{LDA : LessDefined A, !Reflexive LDA} (outD : QueueA A) :
  outD `is_approx` empty ->
  let dcost := Tick.cost (emptyD outD) in
  emptyA [[ fun out cost => outD `less_defined` out /\ cost <= dcost ]].
Proof.
  unfold emptyA. mgo_.
Qed.

(* push *)

(* Note that this definition is written so as to "look" maximally lazy. *)
Fixpoint push (A : Type) (q : Queue A) (x : A) : Queue A :=
  let '(f, m, r) :=
    match q with
    | Nil =>
        let f' := FOne x in
        let m' := Nil in
        let r' := RZero in
        (f', m', r')
    | Deep f m r =>
        let (m, r) :=
          match r with
          | RZero =>
              let r' := ROne x in
              (m, ROne x)
          | ROne y =>
              let p := (y, x) in
              let m' := push m p in
              let r' := RZero in
              (m', r')
          end in
        (f, m, r)
    end in
  Deep f m r.

Lemma push_ind :
  forall (P : forall (A : Type), Queue A -> A -> Queue A -> Prop),
    (forall A x, P A Nil x (Deep (FOne x) Nil RZero)) ->
    (forall A x f m, P A (Deep f m RZero) x (Deep f m (ROne x))) ->
    (forall A x f m y, P (prod A A) m (y, x) (push m (y, x)) -> P A (Deep f m (ROne y)) x (Deep f (push m (y, x)) RZero)) ->
    forall A (q : Queue A) (x : A), P A q x (push q x).
Proof.
  intros ? H1 H2 H3. fix SELF 2. intros ? q.
  refine (match q with
          | Nil => _
          | Deep f m RZero => _
          | Deep f m (ROne y) => _
          end); intros.
  - apply H1.
  - apply H2.
  - apply H3. apply SELF.
Qed.

Lemma push_is_Deep (A : Type) (q : Queue A) (x : A) : exists f m r, push q x = Deep f m r.
Proof.
  refine (match q with
          | Nil => _
          | Deep f m RZero => _
          | Deep f m (ROne y) => _
          end); simpl; eauto.
Qed.

(* Note that this definition *is* maximally lazy. *)
Fixpoint pushA' (A : Type) (q : QueueA A) (x : T A) : M (QueueA A) :=
  tick >>
    let! (f, m, r) :=
      match q with
      | NilA =>
          let~ f' := ret (FOneA x) in
          let~ m' := ret NilA in
          let~ r' := ret RZeroA in
          ret (f', m', r')
      | DeepA f m r =>
          let! (m, r) :=
            let! r := force r in
            match r with
            | RZeroA =>
                let~ r' := ret (ROneA x) in
                ret (m, r')
            | ROneA y =>
                let~ p := ret (pairA y x) in
                (* The termination checker rejects a more "imperative" approach
                   here; i.e., let! m := force m in ... *)
                let~ m' := forcing m (fun m => pushA' m p) in
                let~ r' := ret RZeroA in
                ret (m', r')
            end in
          ret (f, m, r)
      end in
    ret (DeepA f m r).

Definition pushA (A : Type) (q : T (QueueA A)) (x : T A) : M (QueueA A) :=
  forcing q (fun q => pushA' q x).

Lemma pushA_mon (A : Type) `{LDA : LessDefined A, PreOrder A LDA} (q' q : T (QueueA A)) x' x
  : q' `less_defined` q ->
    x' `less_defined` x ->
    pushA q' x' `less_defined` pushA q x.
Proof.
  invert_clear 1; try solve [ solve_mon ].
  rename x0 into q'. rename y into q. rename H0 into Hq.
  simpl. induction q as [ | ? f m r ]; intro Hx.
  - invert_clear Hq. simpl. apply tick_mon.
    apply bind_mon; try solve [ solve_mon ]. intros [ fq' r' ] [ fq r ].
    invert_clear 1 as [ Hfq Hr ]. simpl in *.
    destruct fq' as [ f' q' ]. destruct fq as [ f q ].
    invert_clear Hfq as [ Hf Hq ]. simpl in *.
    solve_mon.
  - rename H0 into IH. invert_clear Hq as [ | f' ? m' ? r' ? Hf Hm Hr ].
    simpl. apply tick_mon.
    repeat (apply bind_mon); try solve [ solve_mon ].
    + clear dependent r'. clear r. intros r' r Hr.
      invert_clear Hr as [ | y' y Hy ]; try solve [ solve_mon ].
      invert_clear Hm; try solve [ solve_mon ].
      rename x0 into m'. rename y0 into m. rename H0 into Hm.
      invert_clear IH as [ ? IH | ]; try solve [ solve_mon ].
      apply bind_mon; try solve [ solve_mon ].
      intros yz' yz Hyz. simpl. apply bind_mon.
      * apply thunk_mon. apply IH; try solve [ auto ]. typeclasses eauto.
      * intros. solve_mon.
    + clear dependent r'. clear r. clear dependent m'. clear dependent m.
      intros [ m' r' ] [ m r ] [ Hm Hr ]. solve_mon.
    + clear dependent f'. clear f. clear dependent m'. clear dependent m.
      clear dependent r'. clear r.
      intros [ [ f' m' ] r' ] [ [ f m ] r ] [ [ Hf Hm ] Hr ]. solve_mon.
Qed.

(* In order to accommodate polymorphic recursion, the type parameter of the
   demand must be allowed to differ from the type parameter of the input. *)

(* XXX The `Exact` parameter here is, I think, a hack.  Basically, in order to
   integrate with the "framework" for proving the physicist's argument from the
   lazy physicist's argument, the element (second pair component) in the input
   demand needs to always be Thunk x in the case of pushD.  But, of course, it
   needs to have a different type in the case of pushD'.  That's where the Exact
   parameter comes in.  I proved the entire file except for ONE CASE in cv
   without needing this change. *)
Fixpoint pushD' (A B : Type) `{Exact A B} (q : Queue A) (x : A) (outD : QueueA B) :
  Tick (prodA (QueueA B) B) :=
  let+ qD :=
    Tick.tick >>
      match outD with
      | DeepA fD mD rD =>
          match q with
          | Nil => Tick.ret (Thunk NilA)
          | Deep f m r =>
              match r with
              | RZero => Tick.ret (Thunk (DeepA fD mD (Thunk RZeroA)))
              | ROne y =>
                  let+ uD := thunkD (pushD' m (y, x)) mD in
                  let '(pairA mD pD) := uD in
                  let (yD, xD) :=
                    match pD with
                    | Thunk (pairA yD xD) => (yD, xD)
                    | _ => bottom
                    end in
                  Tick.ret (Thunk (DeepA fD mD (Thunk (ROneA yD))))
              end
          end
      | _ => bottom
      end in
  Tick.ret (pairA qD (exact x)).

(* Specialize pushD' for the case where B = A, which is what we actually care
   about. *)
Definition pushD (A : Type) : Queue A -> A -> QueueA A -> Tick (prodA (QueueA A) A) :=
  pushD'.

Lemma pushD'_approx : forall (A B : Type) `{LDB : LessDefined B, !Reflexive LDB, Exact A B}
                        (q : Queue A) (x : A) (outD : QueueA B),
    outD `is_approx` push q x -> Tick.val (pushD' q x outD) `is_approx` (q, x).
Proof.
  intros ? ? LDB EAB RLDB ? ? ?. revert A q x B LDB EAB RLDB outD.
  apply (push_ind (fun A q x q' => forall B `{LDB : LessDefined B, !Reflexive LDB, Exact A B} (outD : QueueA B),
                       outD `less_defined` exact q' ->
                       Tick.val (pushD' q x outD) `less_defined` exact (q, x)));
    intros until outD.
  - refine (match outD with
            | DeepA (Thunk (FOneA xD)) _ _ => _
            | _ => _
            end); intro Happrox;
      repeat match goal with
        | H : ?x `less_defined` ?y |- _ =>
            (head_is_constructor_or_proj x + head_is_constructor_or_proj y); invert_clear H
        end; repeat constructor; simpl; repeat constructor; reflexivity.
  - refine (match outD with
            | DeepA fD mD _ => _
            | _ => bottom
            end); intro Happrox; teardown;
      repeat match goal with
        | H : ?x `less_defined` ?y |- _ =>
            (head_is_constructor_or_proj x + head_is_constructor_or_proj y); invert_clear H
        end; repeat constructor; auto; reflexivity.
  - refine (match outD with
            | DeepA fD mD' _ => _
            | _ => _
            end); try solve [ repeat constructor; reflexivity ].
    intro Happrox.
    invert_clear Happrox as [ | ? ? ? ? ? ? HfD HmD' HrD ].
    invert_clear HmD' as [ | mA' ? HmA' ].
    + solve_approx.
    + specialize (H _ _ _ _ _ HmA').
      simpl. destruct (Tick.val (pushD' m (y, x) mA')) as [ mD pD ].
      invert_clear H as [ HmD HpD ].
      invert_clear HpD as [ | [ b1D b2D ] ? Hb1b2D ];
        repeat (invert_approx); solve_approx.
Qed.

Corollary pushD_approx (A : Type) `{LDA : LessDefined A, !Reflexive LDA}
  (q : Queue A) (x : A) (outD : QueueA A) :
  outD `is_approx` push q x -> Tick.val (pushD' q x outD) `is_approx` (q, x).
Proof.
  eapply pushD'_approx.
Qed.

Lemma pushD'_exact (A B : Type) `{Exact A B} (q : Queue A) (x : A) :
  Tick.val (pushD' q x (exact (push q x))) = exact (q, x).
Proof.
  revert dependent B. revert dependent A.
  induction q.
  - reflexivity.
  - destruct r.
    + reflexivity.
    + simpl. intros. unfold exact in IHq.
      rewrite (IHq (a, x) (prodA B B) _). reflexivity.
Qed.

Lemma pushD'_sndA (A B : Type) `{Exact A B}
  (q : Queue A) (x : A) (outD : QueueA B) :
  sndA (Tick.val (pushD' q x outD)) = exact x.
Proof.
  destruct q; reflexivity.
Qed.

#[local] Existing Instance Reflexive_LessDefined_T.
#[local] Existing Instance Reflexive_LessDefined_prodA.

Lemma pushD'_spec (A B : Type) :
  forall `{LDB : LessDefined B, !Reflexive LDB, Exact A B}
    (q : Queue A) (x : A) (outD : QueueA B),
    outD `is_approx` push q x ->
    forall qD xD, pairA qD xD = Tick.val (pushD' q x outD) ->
             let dcost := Tick.cost (pushD' q x outD) in
             pushA qD xD [[ fun out cost =>
                              outD `less_defined` out /\ cost <= dcost ]].
Proof.
  intros LDB HReflexive EAB q x outD Happrox qD xD HAD dcost.
  revert A q x B LDB HReflexive EAB outD Happrox qD xD HAD dcost.
  apply (push_ind
           (fun A q x q' =>
              forall B `{LDB : LessDefined B, !Reflexive LDB, Exact A B} outD,
                outD `is_approx` q' ->
                forall qD xD,
                  pairA qD xD = Tick.val (pushD' q x outD) ->
                  let dcost := Tick.cost (pushD' q x outD) in
                  pushA qD xD [[fun out cost =>
                                  outD `less_defined` out /\
                                    cost <= dcost]])).
  - intros A x B LDB HReflexive EAB outD Happrox qD xD. revert Happrox.
    refine (match outD with
            | NilA => _
            | DeepA fD _ _ => _
            end); mgo'.
    keep_mgo_.
  - intros A x f m B LDB HReflexive EAB outD Happrox qD xD. revert Happrox.
    simpl.
    refine (match outD with
            | DeepA fD mD _ => _
            | _ => _
            end); mgo';
      apply optimistic_thunk_go; destruct t; mgo'; solve_approx.
  - intros A x f m y IH B LDB HReflexive EAB outD Happrox qD xD.
    revert Happrox.
    refine (match outD with
            | DeepA fD mD rD => _
            | _ => _
            end); try solve [ invert_clear 1 ].
    invert_clear 1 as [ | ? ? ? ? ? ? HfD HmD HrD ].
    invert_clear HmD as [ | mA ? HmA ].
    + invert_clear 1. mgo_brute_force.
    + specialize (IH _ _ _ _ _ HmA).
      revert IH. simpl. destruct (Tick.val (pushD' m (y, x) mA)) as [ qD' xD' ] eqn:EpushD'.
      assert (xD' = exact (y, x)) as HxD'.
      { rewrite <- (@pushD'_sndA _ _ _ m (y, x) mA). rewrite EpushD'. auto. }
      rewrite HxD'.
      intro IH. specialize (IH _ _ eq_refl).
      destruct xD' as [ [ b1D b2D ] | ].
      * invert_clear 1.
        mgo_. apply optimistic_thunk_go.
        mgo_. apply optimistic_thunk_go.
        eapply optimistic_mon; [eassumption |].
        keep_mgo_. tauto.
      * invert_clear HxD'.
Qed.

Corollary pushD_spec (A : Type) :
  forall `{LDA : LessDefined A, !Reflexive LDA}
    (q : Queue A) (x : A) (outD : QueueA A),
    outD `is_approx` push q x ->
    forall qD xD, pairA qD xD = Tick.val (pushD' q x outD) ->
             let dcost := Tick.cost (pushD' q x outD) in
             pushA qD xD [[ fun out cost =>
                              outD `less_defined` out /\ cost <= dcost ]].
Proof.
  intros. apply pushD'_spec; auto.
Qed.

(* pop *)

(* Note that this definition is written so as to "look" maximally lazy. *)
Fixpoint pop (A : Type) (q : Queue A) : option (A * Queue A) :=
  match q with
  | Nil => None
  | Deep f m r =>
      let (x, q) :=
        match f with
        | FOne x =>
            let q :=
              let p := pop m in
              match p with
              | Some yzm' =>
                  let (yz, m') := yzm' in
                  let (y, z) := yz in
                  let f' := FTwo y z in
                  Deep f' m' r
              | None =>
                  match r with
                  | RZero => Nil
                  | ROne y =>
                      let f' := FOne y in
                      let m' := Nil in
                      let r' := RZero in
                      Deep f' m' r'
                  end
              end
            in (x, q)
        | FTwo x y =>
            let f' := FOne y in
            let q' := Deep f' m r in
            (x, q')
        end in
      Some (x, q)
  end.

Lemma pop_ind :
  forall (P : forall (A : Type), Queue A -> option (A * Queue A) -> Prop),
    (forall A, P A Nil None) ->
    (forall A m r x y z m',
        pop m = Some ((y, z), m') ->
        P (prod A A) m (pop m) ->
        P A (Deep (FOne x) m r) (Some (x, Deep (FTwo y z) m' r))) ->
    (forall A m x,
        pop m = None ->
        P (prod A A) m (pop m) ->
        P A (Deep (FOne x) m RZero) (Some (x, Nil))) ->
    (forall A m x y,
        pop m = None ->
        P (prod A A) m (pop m) ->
        P A (Deep (FOne x) m (ROne y)) (Some (x, Deep (FOne y) Nil RZero))) ->
    (forall A m r x y, P A (Deep (FTwo x y) m r) (Some (x, Deep (FOne y) m r))) ->
    forall A (q : Queue A), P A q (pop q).
Proof.
  intros ? H1 H2 H3 H4 H5. fix SELF 2. intros ? q.
  refine (match q with
          | Nil => _
          | Deep f m r => _
          end); intros.
  - apply H1.
  - refine (match f with
            | FOne x => _
            | FTwo x y => _
            end).
    + simpl. refine ((match pop m as u return pop m = u -> _ with
                      | Some (y, z, m') => _
                      | None => _
                      end) eq_refl); intro H; rewrite H.
      * apply H2.
        -- exact H.
        -- apply SELF.
      * refine (match r with
                | RZero => _
                | ROne y => _
                end).
        -- apply H3.
           ++ exact H.
           ++ apply SELF.
        -- apply H4.
           ++ exact H.
           ++ apply SELF.
    + apply H5.
Qed.

Lemma pop_None_inv (A : Type) (q : Queue A) : pop q = None -> q = Nil.
Proof.
  destruct q.
  - auto.
  - destruct f; discriminate.
Qed.

(* Note that this definition *is* maximally lazy. *)
Fixpoint popA' (A : Type) (q : QueueA A) : M (option (T (prodA A (QueueA A)))) :=
  tick >>
    match q with
    | NilA => ret None
    | DeepA f m r =>
        let! (x, q) :=
          let! f := force f in
          match f with
          | FOneA x =>
              let~ q :=
                let! p := popA' $! m in
                match p with
                | Some yzm' =>
                    let! (pairA yz m') := force yzm' in
                    let! (pairA y z) := force yz in
                    let~ f' := ret (FTwoA y z) in
                    ret (DeepA f' m' r)
                | None =>
                    let! r := force r in
                    match r with
                    | RZeroA => ret NilA
                    | ROneA y =>
                        let~ f' := ret (FOneA y) in
                        let~ m' := ret NilA in
                        let~ r' := ret RZeroA in
                        ret (DeepA f' m' r')
                    end
                end in
              ret (x, q)
          | FTwoA x y =>
              let~ f' := ret (FOneA y) in
              let~ q' := ret (DeepA f' m r) in
              ret (x, q')
          end in
        let~ p := ret (pairA x q) in
        ret (Some p)
    end.

Definition popA (A : Type) (q : T (QueueA A)) : M (option (T (prodA A (QueueA A)))) :=
  popA' $! q.

Lemma popA_mon (A : Type) `{LDA : LessDefined A, PreOrder A LDA} (q' q : T (QueueA A))
  : q' `less_defined` q ->
    popA q' `less_defined` popA q.
Proof.
  invert_clear 1; try solve [ solve_mon ].
  rename x into q'. rename y into q. rename H0 into Hq.
  simpl. induction q as [ | ? f m r ].
  - invert_clear Hq. solve_mon.
  - rename H0 into IH. invert_clear Hq as [ | f' ? m' ? r' ? Hf Hm Hr ]. simpl.
    apply tick_mon. repeat (apply bind_mon); try solve [ solve_mon ].
    + clear dependent f'. clear f. intros f f' Hf.
      invert_clear Hf as [ x x' Hx | ]; try solve [ solve_mon ].
      apply bind_mon; try solve [ intros; solve_mon ].
      apply thunk_mon. apply bind_mon.
      * invert_clear Hm; try solve [ solve_mon ].
        invert_clear IH as [ ? IH | ]; try solve [ solve_mon ].
        simpl. apply IH; try solve [ auto ]. typeclasses eauto.
      * intros. solve_mon. destruct x2, x'1. invert_clear H4. solve_mon.
        destruct x2, x'1. invert_clear H6. solve_mon.
    + intros [ ? ? ] [ ? ? ] [ ? ? ]. solve_mon.
Qed.

Fixpoint popD' (A B : Type) (q : Queue A) (outD : option (T (prodA B (QueueA B)))) :
  Tick (T (QueueA B)) :=
  Tick.tick >>
    match q with
    | Nil => Tick.ret (Thunk NilA)
    | Deep f m r =>
        let+ (fD, mD, rD) :=
          let (xD, qD) :=
            match outD with
            | Some (Thunk (pairA xD qD)) => (xD, qD)
            | _ => bottom
            end in
          match f with
          | FOne x =>
              let p := pop m in
              let (pD, rD) :=
                match p with
                | Some (yz, m') =>
                    match qD with
                    | Thunk (DeepA fD mD' rD) =>
                        let yzD :=
                          (* XXX *)
                          Thunk (match fD with
                                 | Thunk (FTwoA yD zD) => pairA yD zD
                                 | _ => bottom
                                 end) in
                        (Thunk (Some (Thunk (pairA yzD mD'))), rD)
                    | _ => bottom
                    end
                | None =>
                    let rD :=
                      match r with
                      | RZero => Thunk RZeroA
                      | ROne y =>
                          let yD :=
                            match qD with
                            | Thunk (DeepA (Thunk (FOneA yD)) _ _) => yD
                            | _ => bottom
                            end in
                          Thunk (ROneA yD)
                      end in
                    (Thunk None, rD)
                end in
              let+ mD := thunkD (popD' m) pD in
              Tick.ret (Thunk (FOneA xD), mD, rD)
          | FTwo x y =>
              let '(yD, mD, rD) :=
                match qD with
                | Thunk (DeepA fD' mD rD) =>
                    let yD :=
                      match fD' with
                      | Thunk (FOneA yD) => yD
                      | _ => bottom
                      end in
                    (yD, mD, rD)
                | _ => bottom
                end in
              Tick.ret (Thunk (FTwoA xD yD), mD, rD)
          end in
        Tick.ret (Thunk (DeepA fD mD rD))
    end.

Definition popD (A : Type) (q : Queue A) (outD : option (T (prodA A (QueueA A)))) :
  Tick (T (QueueA A)) :=
  popD' q outD.

Lemma popD'_approx : forall (A B : Type) `{LDB : LessDefined B, Exact A B}
                       (q : Queue A) (outD : option (T (prodA B (QueueA B)))),
    outD `is_approx` pop q -> Tick.val (popD' q outD) `is_approx` q.
Proof.
  Ltac finish H :=
    solve_approx; apply H; solve_approx.
  intros ? ? LDB EAB ? ?. revert A q B LDB EAB outD.
  apply (pop_ind (fun A q u =>
                    forall B LDB EAB outD,
                      outD `less_defined` exact u ->
                      Tick.val (popD' q outD) `less_defined` exact q)); intros.
  - solve_approx.
  - simpl. rewrite H in *. invert_clear H1. invert_clear H1.
    + sauto.
    + destruct x1. invert_clear H1. invert_clear H2.
      * sauto.
      * invert_clear H2. invert_clear H2.
        -- cbn. finish H0.
        -- simpl. finish H0. fcrush.
  - simpl. rewrite H in *. invert_clear H1. invert_clear H1.
    + finish H0.
    + destruct x1. invert_clear H1. finish H0.
  - simpl. rewrite H in *. invert_clear H1. invert_clear H1.
    + finish H0.
    + destruct x1. simpl. invert_clear H1. invert_clear H2.
      * finish H0.
      * invert_clear H2. invert_clear H2.
        -- finish H0.
        -- invert_clear H2. finish H0.
  - simpl. invert_clear H. invert_clear H.
    + simpl. finish idfun.
    + destruct x1. invert_clear H. invert_clear H0.
      * simpl. finish idfun.
      * invert_clear H0. invert_clear H0.
        -- finish idfun.
        -- invert_clear H0. finish idfun.
Qed.

Corollary popD_approx : forall (A : Type) `{LessDefined A}
                          (q : Queue A) (outD : option (T (prodA A (QueueA A)))),
    outD `is_approx` pop q -> Tick.val (popD' q outD) `is_approx` q.
Proof.
  intros. apply popD'_approx. auto.
Qed.

Lemma popD'_exact (A B : Type) `{Exact A B} (q : Queue A) :
  Tick.val (popD' q (exact (pop q))) = exact q.
Proof.
  revert dependent B. revert dependent A.
  induction q.
  - reflexivity.
  - intros. specialize (IHq (prodA B B) _).
    simpl. destruct f; [ | reflexivity ].
    destruct (pop q) as [ [ [ y z ] m' ] | ] eqn:Epop.
    + simpl.
      change (exact (Some (y, z, m')))
        with
        (@Some (T (prodA (prodA B B) (QueueA (prodA B B))))
           (@Thunk (prodA (prodA B B) (QueueA (prodA B B)))
              (@pairA (prodA B B) (QueueA (prodA B B))
                 (@Thunk (prodA B B)
                    (@pairA B B (@exact A (T B) (@Exact_T A B H) y)
                       (@exact A (T B) (@Exact_T A B H) z)))
                 (@Thunk (QueueA (prodA B B))
                    (@Exact_Queue (A * A) (prodA B B) (@Prod.Exact_prodA A A B B H H) m')))))
        in IHq.
      rewrite IHq. reflexivity.
    + change (popD' q (exact None))
        with
        ((@popD' (A * A) (prodA B B) q (@None (T (prodA (prodA B B) (QueueA (prodA B B)))))))
        in IHq. simpl. rewrite IHq.
      destruct r; reflexivity.
Qed.

Lemma popD'_spec :
  forall (A B : Type) `{LDB : LessDefined B, !Reflexive LDB, Exact A B}
    (q : Queue A) (outD : option (T (prodA B (QueueA B)))),
    outD `is_approx` pop q ->
    forall qD, qD = Tick.val (popD' q outD) ->
    let dcost := Tick.cost (popD' q outD) in
    popA qD [[ fun out cost => outD `less_defined` out /\ cost <= dcost ]].
Proof.
  intros ? ? LDB RLDB EAB ? ?. revert A q B LDB RLDB EAB outD.
  apply (pop_ind (fun A q u =>
                    forall B LDB RLDB EAB outD,
                      outD `is_approx` u ->
                      forall qD, qD = Tick.val (popD' q outD) ->
                            let dcost := Tick.cost (popD' q outD) in
                            popA qD [[ fun out cost => outD `less_defined` out /\ cost <= dcost ]])).
  - intros. subst. mgo_.
  - simpl. intros A m r x y z m' ->.
    invert_clear 3. invert_clear H0.
    + intros. subst. mgo_brute_force.
    + (* pop m = None *)
      destruct x1 as [ xD qD ].
      invert_clear H0 as [ HxQ HqD ]. invert_clear HqD
        as [ | qA ? HqA ].
      * simpl. intros. subst. mgo_brute_force.
      (* qD = Thunk _ *)
      * simpl. invert_clear HqA as [ | fD ? mD ? rD ? HfD HmD HrD ].
        simpl. invert_clear HfD as [ | fA ? HfA ].
        (* fD = Undefined *)
        -- intros. subst. mgo_.
           apply optimistic_thunk_go. mgo_.
           eapply optimistic_mon.
           ++ eapply H; [ | | reflexivity ].
              all: fcrush.
           ++ intros. destruct H0. invert_clear H0 as [ | ? yzm'D Hyzm'D ].
              invert_clear Hyzm'D as [ | ? yzm'A Hyzm'A ].
              destruct yzm'A as [ yzD m'D ].
              invert_clear Hyzm'A as [ ? HmD' ].
              mgo_. destruct yzD.
              ** destruct x0. mgo_brute_force.
              (* yzD = Undefined *)
              ** invert_clear H0.
        -- invert_clear HfA. intros. subst. mgo_.
           apply optimistic_thunk_go. mgo_.
           eapply optimistic_mon.
           ++ eapply H; [ | | reflexivity ].
              all: fcrush.
           ++ intros. destruct H2. invert_clear H2.
              mgo_. invert_clear H2. mgo_.
              destruct y2. destruct H2. invert_clear H2.
              destruct y0. invert_approx.
              keep_mgo_.
  - simpl. intros ? ? ? -> ? ? ? ? ? ?. invert_clear 1. invert_clear H0.
    + intros ? ->. mgo_brute_force.
    + destruct x1. simpl. intros ? ->.
      mgo_. apply optimistic_thunk_go.
      mgo_. eapply optimistic_mon.
      * eapply H; [ | | | reflexivity ].
        all: fcrush.
      * simpl. destruct 1. repeat invert_approx.
        mgo_brute_force.
  (* f = FOne x, pop m = None, r = ROne y *)
  - simpl. intros ? ? ? ? -> ? ? ? ? ? ?. invert_clear 1.
    invert_clear H0.
    + intros ? ->. mgo_brute_force.
    + destruct x1. repeat invert_approx.
      simpl. intros ? ->. mgo_. apply optimistic_thunk_go.
      destruct (popD' m None) eqn:HpopD'. simpl. mgo_.
      eapply optimistic_mon.
      * eapply H; [ | | | rewrite HpopD'; reflexivity ].
        all: fcrush.
      * intros. destruct x0. mgo_. repeat invert_approx.
        keep_mgo_; [ fcrush | ].
        destruct H1;
          replace cost with (Tick.cost (@popD' _ (prodA B B) m None))
          by (rewrite HpopD'; auto); lia.
  (* f = FTwo x y *)
  - invert_clear 2. invert_clear H.
    * intros ? ->. keep_mgo_.
    (* outD = Some (Thunk (pairA xD qD)) *)
    * destruct x1. invert_clear H. invert_clear H0.
      (* qD = Undefined *)
      -- intros ? ->. keep_mgo_.
      -- repeat invert_approx; intros ? ->; keep_mgo_; fcrush.
Qed.

Corollary popD_spec :
  forall (A : Type) `{LDA : LessDefined A, !Reflexive LDA}
    (q : Queue A) (outD : option (T (prodA A (QueueA A)))),
    outD `is_approx` pop q ->
    forall qD, qD = Tick.val (popD' q outD) ->
    let dcost := Tick.cost (popD' q outD) in
    popA qD [[ fun out cost => outD `less_defined` out /\ cost <= dcost ]].
Proof.
  intros. apply popD'_spec; auto.
Qed.

Class Debitable (A : Type) :=
  debt : A -> nat.

#[global] Instance Debitable_T (A : Type) `{Debitable A} : Debitable (T A) :=
  fun xD => match xD with
            | Thunk x => debt x
            | Undefined => 0
            end.

Definition size_FrontA (A : Type) (fA : FrontA A) : nat :=
  match fA with
  | FOneA _ => 1
  | FTwoA _ _ => 2
  end.

Definition size_RearA (A : Type) (rA : RearA A) : nat :=
  match rA with
  | RZeroA => 0
  | ROneA _ => 1
  end.

#[global] Instance Debitable_QueueA : forall (A : Type), Debitable (QueueA A) :=
  fix debt_QueueA (A : Type) (qA : QueueA A) :=
    match qA with
    | NilA => 0
    | DeepA fD mD rD =>
        let c := T_rect _ size_FrontA 2 fD - T_rect _ size_RearA 0 rD
        in c + @Debitable_T _ (debt_QueueA _) mD
    end.

Lemma pushD'_cost : forall (A B : Type) `{LessDefined B, Exact A B} (q : Queue A) (x : A) (outD : QueueA B),
    outD `is_approx` push q x ->
    let inM := pushD' q x outD in
    let cost := Tick.cost inM in
    let (qD, _) := Tick.val inM in
    debt qD + cost <= 2 + debt outD.
Proof.
  intros A B LDB EAB q x. revert A q x B LDB EAB.
  apply (push_ind (fun (A : Type) (q : Queue A) (x : A) (q' : Queue A) =>
                     forall B LDB EAB outD,
                       outD `is_approx` q' ->
                       let inM := pushD' q x outD in
                       let cost := Tick.cost inM in
                       let (qD, _) := Tick.val inM in
                       debt qD + cost <= 2 + debt outD)).
  - fcrush unfold:debt.
  - fcrush unfold:debt.
  - intros until outD. refine (match outD with
                               | DeepA fD mD _ => _
                               | _ => _
                               end); invert_clear 1.
    invert_clear H1.
    + sauto unfold:debt.
    + specialize (H _ _ _ _ H1). simpl in *.
      destruct (Tick.val (pushD' m (y, x) x0))
        as [ mD' [ [ yD xD ] | ] ]
             eqn:HpushD; sauto unfold:*.
Qed.

Corollary pushD_cost : forall (A : Type) `{LessDefined A} (q : Queue A) (x : A) (outD : QueueA A),
    outD `is_approx` push q x ->
    let inM := pushD q x outD in
    let cost := Tick.cost inM in
    let (qD, _) := Tick.val inM in
    debt qD + cost <= 2 + debt outD.
Proof.
  intros. apply pushD'_cost. auto.
Qed.

Lemma popD_None: forall A B (q : Queue A),
    pop q = None ->
    popD' q None = Tick.MkTick 1 (Thunk (NilA : QueueA B)).
Proof. sauto. Qed.

Lemma popD'_cost : forall (A B : Type)
                     `{LessDefined B, Exact A B}
                     (q : Queue A) (outD : option (T (prodA B (QueueA B)))),
    outD `is_approx` pop q ->
    let d := match outD with
             | Some (Thunk (pairA _ qD)) => debt qD
             | _ => 0
             end in
    let inM := popD' q outD in
    let cost := Tick.cost inM in
    let inD := Tick.val inM in
    debt inD + cost <= 3 + d.
Proof.
  intros A B LDB EAB q. revert A q B LDB EAB.
  induction q; intros B LDB EAB outD HoutD.
  - sfirstorder.
  - simpl in *. destruct f as [ x | x y ].
    + (* f = FOne x *)
      invert_clear HoutD as [ | pD ? HpD ].
      (* outD = Some pD *)
      destruct (pop q) as [ p | ] eqn:Hpop.
      * (* pop q = Some p *)
        destruct p as [ [ y z ] m ].
        invert_clear HpD as [ | pA ? HpA ].
        -- (* pD = Thunk (DeepA (Thunk (FOneA bottom)) bottom bottom) *)
            sauto.
        -- destruct pA as [ xD qD ]. invert_clear HpA as [ HxD HqD ].
           invert_clear HqD as [ | qA ? HqA ].
           ++ sauto.
           ++ invert_clear HqA as [ | fD ? mD ? rD ? HfD HmD HrD ].
              simpl. invert_clear HfD as [ | fA ? HfA ].
              (* fD = Undefined *)
              ** specialize (IHq _ _ _ (Some (Thunk (pairA (Thunk bottom) mD)))
                               ltac:(solve_approx)).
                 sauto unfold:debt.
              ** (* fD = Thunk fA *)
                 invert_clear HfA as [ | yD ? zD ? HyD HzD ].
                 specialize (IHq _ _ _ (Some (Thunk (pairA (Thunk (pairA yD zD)) mD)))
                               ltac:(solve_approx)).
                 sauto unfold:debt.
      * (* pop q = None *)
        destruct r as [| y]; sauto use:popD_None.
    + (* f = FTwo x y *)
      invert_clear HoutD as [| ? ? H]. invert_clear H as [ | xD].
      * (* x0 = Undefined *) sauto.
      * destruct xD. invert_clear H as [Hfst Hsnd].
        invert_clear Hsnd.
        -- simpl; lia.
        -- invert_clear H. invert_clear H; cbn; sauto.
Qed.

Corollary popD_cost :
  forall (A : Type) `{LessDefined A}
         (q : Queue A) (outD : option (T (prodA A (QueueA A)))),
    outD `is_approx` pop q ->
    let d := match outD with
             | Some (Thunk (pairA _ qD)) => debt qD
             | _ => 0
             end in
    let inM := popD' q outD in
    let cost := Tick.cost inM in
    let inD := Tick.val inM in
    debt inD + cost <= 3 + d.
Proof.
  intros. apply popD'_cost. auto.
Qed.

From Coq Require Import List.
Import ListNotations.
From Clairvoyance Require Import Interfaces.
Open Scope tick_scope.

Lemma less_defined_forceD (A : Type) `{LessDefined A} (x : T A) (y : A) (z : A)
  : y `less_defined` z ->
    x `less_defined` Thunk z ->
    forceD y x `less_defined` z.
Proof.
  intros Hy Hx; inversion Hx; cbn; auto.
Qed.

Section Physicist'sArgument.

  Context (A : Type).
  Definition value := Queue A.
  Definition valueA := T (QueueA A).

  Inductive op : Type :=
  | Empty
  | Push (x : A)
  | Pop.

  #[export] Instance eval : Eval op value :=
    fun op args => match op, args with
                | Empty, [] => [empty]
                | Push x, [q] => [push q x]
                | Pop, [q] => match pop q with
                             | Some (_, q') => [q']
                             | _ => []
                             end
                | _, _ => []
                end.

  #[export] Instance budget : Budget op value :=
    fun _ _ => 3.

  #[export] Instance exec : Exec op valueA :=
    fun o args => match o, args with
               | Empty, [] => let! q := emptyA in ret [Thunk q]
               | Push x, [q] => let! q' := pushA q (Thunk x) in ret [Thunk q']
               | Pop, [q] => let! p := popA q in
                            match p with
                            | Some (Thunk (pairA x q)) => ret [q]
                            | Some Undefined => ret [Undefined]
                            | _ => ret []
                            end
               | _, _ => ret []
               end.

  #[export] Instance wf : WellFormed value := fun _ => True.

  Lemma wf_eval : WfEval.
  Proof using A.
    unfold WfEval. destruct o, vs; repeat constructor.
    - simpl. destruct vs; repeat constructor.
    - simpl. destruct vs, (pop v) as [ [ ? ? ] | ]; repeat constructor.
  Qed.
  #[export] Existing Instance wf_eval.

  Lemma monotonic_exec `{LDA : LessDefined A, !PreOrder LDA} (o : op) : Monotonic (exec o).
  Proof using A.
    assert (Reflexive (less_defined (a := QueueA A))) by typeclasses eauto.
    unfold Monotonic. destruct o; invert_clear 1; simpl; try solve [ solve_mon ].
    - invert_clear H1; solve_mon.
      apply pushA_mon; try solve [ auto ]. reflexivity.
    - invert_clear H1; try solve [ solve_mon ].
      apply bind_mon.
      + apply popA_mon; auto.
      + intros. invert_clear H1; solve_mon.
        * destruct y; try solve [ solve_mon ]. destruct x2; solve_mon.
        * destruct x, y1; try solve [ solve_mon ].
          subst. invert_clear H2. solve_mon.
  Qed.

  #[export] Instance approx_algebra
    `{LDA : LessDefined A, PreOrder A LDA, LBA : Lub A, @LubLaw A LBA LDA} :
    IsApproxAlgebra value valueA.
  Proof.
    econstructor; try typeclasses eauto.
  Defined.

  Lemma well_defined_exec
    `{LDA : LessDefined A, PreOrder A LDA, LBA : Lub A, @LubLaw A LBA LDA} :
    @WellDefinedExec op value valueA _ _.
  Proof using A.
    constructor; exact monotonic_exec.
  Qed.
  #[export] Existing Instance well_defined_exec.

  #[export] Instance demand : Demand op value valueA :=
    fun op args argsA =>
      match op, args, argsA with
      | Empty, [], [outD] =>
          let outD := forceD (bottom_of (exact empty)) outD in
          emptyD outD >> Tick.ret []
      | Push x, [q], [outD] =>
          let outD := forceD (bottom_of (exact (push q x))) outD in
          let+ (pairA qD _) := pushD q x outD in
          Tick.ret [qD]
      | Pop, [q], [] =>
          let+ qD := popD q None in
          Tick.ret [qD]
      | Pop, [q], [qD'] =>
          let+ qD := popD q (Some (Thunk (pairA Undefined qD')))
          in Tick.ret [qD]
      | _, _, _ => Tick.ret (bottom_of (exact args))
      end.

  Lemma pd
    `{LDA : LessDefined A, PA : !PreOrder LDA, LBA : Lub A, LLA : @LubLaw A LBA LDA} :
    @PureDemand op value valueA
                approx_algebra
                eval
                demand.
  Proof using A.
    assert (@Reflexive A less_defined)
      as HRA
        by (destruct PA; auto).
    assert (@Reflexive (QueueA A) less_defined)
      as HRQA
        by apply (@Reflexive_LessDefined_QueueA A LDA HRA).
    unfold PureDemand, pure_demand.
    intros o args output.
    set (o' := o). revert o'.
    set (args' := args). revert args'.
    set (output' := output). revert output'.
    refine (match o, args, output with
            | Empty, [], [_] => _
            | Push x, [q], [outD] => _
            | _, _, _ => _
            end); try solve [ repeat constructor +
                                invert_clear 1; try apply bottom_is_least; reflexivity ].
    simpl. invert_clear 1. invert_clear H.
    - simpl.
      destruct (Tick.val (pushD q x (bottom_of (exact (push q x))))) eqn:HpushD.
      constructor; auto.
      replace t with (fstA (Tick.val (pushD q x (bottom_of (exact (push q x)))))).
      + assert (bottom_of (exact (push q x)) `less_defined` exact (push q x)).
        apply bottom_is_least. auto.
        pose proof (@pushD_approx _ _ _ q x _ H).
        unfold less_defined, LessDefined_prodA in H1.
        change (pushD' q x (bottom_of (exact (push q x))))
          with
          (pushD q x (bottom_of (exact (push q x))))
          in H1.
        destruct (Tick.val (pushD q x (bottom_of (exact (push q x))))).
        sauto.
      + destruct (Tick.val (pushD q x (bottom_of (exact (push q x))))).
        invert_clear HpushD. auto.
    - simpl.
      destruct (Tick.val (pushD q x x0)) eqn:HpushD. simpl.
      constructor; auto.
      replace t with (fstA (Tick.val (pushD q x x0))).
      + pose proof (@pushD_approx _ _ _ q x _ H).
        change (pushD' q x x0)
          with
          (pushD q x x0)
          in H1.
        destruct (Tick.val (pushD q x x0)).
        fcrush.
      + destruct (Tick.val (pushD q x x0)). invert_clear HpushD. auto.
    - simpl. refine (match args with
                     | [] => _
                     | [q] => _
                     | _ => _
                     end).
      + repeat constructor.
      + destruct (pop q) eqn:Hpop.
        * simpl. destruct p as [ x q' ]. invert_clear 1. invert_clear H0.
          repeat constructor. apply popD_approx. rewrite Hpop. repeat constructor. auto.
        * pose proof (pop_None_inv Hpop). subst. invert_clear 1. repeat constructor.
      + simpl. intros. apply bottom_is_least. reflexivity.
  Qed.
  #[export] Existing Instance pd.

  Lemma cd
    `{LDA : LessDefined A, PreOrder A LDA, LBA : Lub A, @LubLaw A LBA LDA} :
    @CvDemand op value valueA _ _ _ _.
  Proof using A.
    rename H into PA. rename H0 into LLA.
    assert (Reflexive LDA) as RA by (destruct PA; auto).
    unfold CvDemand, cv_demand.
    destruct o.
    - simpl. destruct x.
      + invert_clear 1. invert_clear H0. invert_clear 1. unfold emptyA. mgo_.
      + invert_clear 1. invert_clear 1. mgo_.
    - simpl. intro x0. refine (match x0 with
                               | [] => _
                               | [q] => _
                               | _ => _
                               end); try solve [ invert_clear 1; invert_clear 1; mgo_ ].
      invert_clear 1. invert_clear H0.
      destruct pushD eqn:EpushD. unfold pushD in EpushD. destruct val. invert_clear 1. mgo_.
      assert (t0 = Thunk x).
      { pose proof (@pushD'_sndA _ _ _ q x (forceD (bottom_of (exact (push q x))) x1)).
        rewrite EpushD in H0. simpl in H0. auto. }
      subst.
      eapply optimistic_mon; [ eapply pushD_spec | ].
      + eapply less_defined_forceD; [ apply bottom_is_less | eassumption ].
      + rewrite EpushD. simpl. reflexivity.
      + intros. mgo_.
        * destruct H0. destruct x1.
          -- simpl in H0. constructor. auto.
          -- constructor.
        * destruct H0. rewrite EpushD in H1. simpl in H1. lia.
    - simpl. intro x.
      refine (match x with
              | [] => _
              | [q] => _
              | _ => _
              end); try solve [ invert_clear 1; invert_clear 1; mgo_ ].
      destruct (pop q) as [ [ ? q' ] | ] eqn:Epop.
      + invert_clear 1. invert_clear H0. invert_clear 1. mgo_.
        eapply optimistic_mon.
        * eapply popD_spec; [ | reflexivity ]. rewrite Epop. solve_approx.
        * intro x1. refine (match x1 with
                            | Some (Thunk (pairA _ q0)) => _
                            | Some Undefined => _
                            | None => _
                            end);
            try solve [ invert_clear 1; repeat (invert_clear H0) ].
          intros ? [ ? ? ].
          invert_clear H0. invert_clear H0. invert_clear H0.
          mgo_. change (popD q (Some (Thunk (pairA Undefined x0))))
            with (popD' q (Some (Thunk (pairA Undefined x0)))).
          unfold popD. lia.
      + invert_clear 1. invert_clear 1.
        apply (pop_None_inv) in Epop. rewrite Epop. mgo_.
  Qed.

  #[export] Existing Instance cd.

  #[global] Instance potential : Potential valueA :=
    fun qD => match qD with
           | Thunk qA => debt qA
           | Undefined => 0
           end.

  Lemma well_defined_potential
    `{LDA : LessDefined A, PreOrder A LDA, LBA : Lub A, @LubLaw A LBA LDA} :
    @WellDefinedPotential value valueA _ _.
  Proof using A.
    constructor.
    - red. invert_clear 1. invert_clear H1.
      invert_clear H1; invert_clear H2; simpl; try solve [ lia ].
      induction y0.
      + invert_clear H1. invert_clear H2. unfold lub. simpl. lia.
      + invert_clear H1. invert_clear H2.
        unfold lub, debt. simpl.
        assert (Debitable_T (lub q1 q0) <= Debitable_T q1 + Debitable_T q0)
          by (invert_clear H3; invert_clear H4; invert_clear H6; simpl; try solve [ lia ];
              eapply H3; try solve [ typeclasses eauto + auto ]).
        invert_clear H5; invert_clear H7;
          try invert_clear H5; try invert_clear H7;
          invert_clear H1; invert_clear H2;
          try invert_clear H1; try invert_clear H2; simpl; lia.
    - red. simpl. lia.
  Qed.
  #[export] Existing Instance well_defined_potential.

  Lemma potential_bottom_of (q : value) :
    potential (bottom_of (exact q)) = 0.
  Proof using A.
    destruct q; reflexivity.
  Qed.
  Hint Resolve potential_bottom_of : core.

  Lemma sumof_potential_bottom_of (qs : list value) :
    sumof potential (bottom_of (exact qs)) = 0.
  Proof using A.
    induction qs; auto.
  Qed.
  Hint Resolve sumof_potential_bottom_of : core.

  Theorem physicist's_argumentD :
    forall `{LDA : LessDefined A, !PreOrder LDA, LBA : Lub A, @LubLaw A LBA LDA},
      @Physicist'sArgumentD
        op value valueA
        _ _ _ _ _ _.
  Proof using A.
    pose proof sumof_potential_bottom_of as Hpb.
    unfold bottom_of, exact in Hpb.
    unfold Physicist'sArgumentD.
    intros LDA HPreOrder LBA HLubLaw o args _ output.
    refine (match o, args, output with
            | Empty, [], [_] => _
            | Push x, [q], [outD] => _
            | Pop, [q], outD => _
            | _, _, _ => _
            end); try solve [ do 2 invert_clear 1; simpl in *;
                              try (rewrite Hpb); lia ].
    - sauto q: on.
    - invert_clear 1 as [ | ? ? ? ? HoutD _ ]. invert_clear HoutD as [ | ? ? HoutD ].
      + unfold demand. simpl. unfold bottom_of, BottomOf.
        pose proof (push_is_Deep q x) as Hpush. destruct Hpush as [? [? [? Hpush] ] ].
        rewrite Hpush. simpl. destruct q; fcrush.
      + pose proof (pushD_cost _ _ HoutD) as Hcost. cbn in Hcost.
        invert_clear 1.
        destruct (Tick.val (pushD q x x0)) as [ qD xD ]. simpl.
        change (potential qD) with (debt qD). lia.
    - simpl. destruct (pop q) eqn:Hpop.
      + destruct p as [ x q' ]. invert_clear 1 as [ | qD' ? ? ? HqD' ]. invert_clear H.
        assert (Some (Thunk (pairA Undefined qD')) `is_approx` pop q)
          as Happrox
            by (rewrite Hpop; repeat constructor; auto).
        pose proof (popD_cost _ Happrox) as Hcost. simpl in *.
        unfold Tick.bind. 
        hauto b: on.
      + sauto q: on.
  Qed.
  #[export] Existing Instance physicist's_argumentD.

  Theorem amortized_cost
    `{LDA : LessDefined A, PreOrder A LDA, LBA : Lub A, @LubLaw A LBA LDA} :
    @AmortizedCostSpec op value valueA _ _ _.
  Proof using A.
    eapply @physicist's_method; typeclasses eauto.
  Qed.

End Physicist'sArgument.
