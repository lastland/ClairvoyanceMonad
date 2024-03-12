From Coq Require Import Arith Psatz Relations RelationClasses.
From Clairvoyance Require Import Core Approx Tick Prod Option.

Import Tick.Notations.
Open Scope tick_scope.

Set Implicit Arguments.
Set Contextual Implicit.
Set Maximal Implicit Insertion.

#[local] Existing Instance Exact_id | 1.

(* Auxiliary stuff *)

(* Tear a goal down by destructing on every case that the goal matches on. *)
Ltac teardown := repeat (simpl; match goal with
                                | |- context [match ?x with _ => _ end] => destruct x
                                | |- context [if ?x then _ else _] => destruct x
                                end).

Ltac teardown_eqns := repeat (simpl; match goal with
                                     | |- context [match ?x with _ => _ end] =>
                                         let H := fresh "H" in destruct x eqn:H
                                     | |- context [if ?x then _ else _] =>
                                         let H := fresh "H" in destruct x eqn:H
                                     end).

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

#[global] Instance PartialOrder_LessDefined_T A `{LessDefined A, PartialOrder A eq less_defined} :
  PartialOrder eq (@less_defined (T A) _).
Proof.
  apply make_partial_order, LessDefined_T_antisym. firstorder.
Qed.

Definition unzipT A B (p : T (A * B)) : T A * T B :=
  match p with
  | Undefined => (Undefined, Undefined)
  | Thunk (x, y) => (Thunk x, Thunk y)
  end.

Definition zipT A B (p : T A) (q : T B) : T (A * B) :=
  match p, q with
  | Thunk x, Thunk y => Thunk (x, y)
  | _, _ => Undefined
  end.

Lemma zipT_less_defined A B `{LessDefined A, LessDefined B}
  (aD aD' : T A) (bD bD' : T B) :
  aD `less_defined` aD' ->
  bD `less_defined` bD' ->
  zipT aD bD `less_defined` zipT aD' bD'.
Proof.
  repeat invert_clear 1; simpl; repeat constructor; auto.
Qed.
#[global] Hint Resolve zipT_less_defined : core.

Lemma zipT_less_defined_approx A B `{LessDefined A, LessDefined B}
  (aD : T A) (a : A) (bD : T B) (b : B) :
  aD `is_approx` a ->
  bD `is_approx` b ->
  zipT aD bD `is_approx` (a, b).
Proof.
  change (exact (a, b)) with (zipT (Thunk a) (Thunk b)).
  apply zipT_less_defined.
Qed.
#[global] Hint Resolve zipT_less_defined_approx : core.

Definition forceD {a} (y : a) (u : T a) : a :=
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
| DeepA : T (FrontA A) -> T (QueueA (A * A)) -> T (RearA A) -> QueueA A.

Lemma QueueA_ind (P : forall A, QueueA A -> Prop) :
  (forall A, P A NilA) ->
  (forall A f m r, TR1 (P (prod A A)) m -> P A (DeepA f m r)) ->
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
  - assert (@Reflexive (A * A) less_defined) by apply Reflexive_LessDefined_prod.
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
  -  assert (@Transitive (T (FrontA A)) less_defined) by apply Transitive_LessDefined_T.
     assert (@Transitive (T (RearA A)) less_defined) by apply Transitive_LessDefined_T.
     assert (@Transitive (A * A) less_defined) by apply Transitive_LessDefined_prod.
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

   `Exact (Queue A) (Queue B).`

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
#[global] Instance Exact_Queue : forall A `{Exact A}, Exact (Queue A) (QueueA A) :=
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
      + apply Reflexive_LessDefined_prod.
      + apply LubLaw_prod.
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
    + apply Reflexive_LessDefined_prod.
    + apply LubLaw_prod.
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
    + apply Reflexive_LessDefined_prod.
    + apply LubLaw_prod.
    + eauto.
Qed.

#[global] Instance IsApproxAlgebra_QueueA (A : Type)
  `{LDA : LessDefined A, PreOrder A LDA, LBA : Lub A, @LubLaw A LBA LDA} :
  IsApproxAlgebra (Queue A) (T (QueueA A)).
Proof.
  econstructor; try typeclasses eauto.
Defined.

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

(* push *)

Fixpoint push (A : Type) (q : Queue A) (x : A) : Queue A :=
  match q with
  | Nil => Deep (FOne x) Nil RZero
  | Deep f m RZero => Deep f m (ROne x)
  | Deep f m (ROne y) => Deep f (push m (y, x)) RZero
  end.

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

Fixpoint pushD (A : Type) (q : Queue A) (x : A) (outD : QueueA A) : Tick (T (QueueA A) * T A) :=
  Tick.tick >>
    match q with
    | Nil =>
        let xD := match outD with
                  | DeepA (Thunk (FOneA xD)) _ _ => xD
                  | _ => bottom
                  end in
        Tick.ret (Thunk NilA, xD)
    | Deep f m RZero =>
        match outD with
        | DeepA fD mD rD =>
            let xD := match rD with
                      | Thunk (ROneA xD) => xD
                      | _ => bottom
                      end in
            Tick.ret (Thunk (DeepA fD mD (Thunk RZeroA)), xD)
        | _ => bottom
        end
    | Deep f m (ROne y) =>
        match outD with
        | DeepA fD mD _ =>
            let+ (mD, pD) := thunkD (pushD m (y, x)) mD in
            let (yD, xD) := unzipT pD in
            Tick.ret (Thunk (DeepA fD mD (Thunk (ROneA yD))), xD)
        | _ => bottom
        end
    end.

Lemma pushD_approx : forall (A : Type) `{LessDefined A} (q : Queue A) (x : A) (outD : QueueA A),
    outD `is_approx` push q x -> Tick.val (pushD q x outD) `is_approx` (q, x).
Proof.
  intros ? LDA ? ? ?. revert A q x LDA outD.
  apply (push_ind (fun A q x q' => forall `{LessDefined A} (outD : QueueA A),
                       outD `less_defined` exact q' ->
                       Tick.val (pushD q x outD) `less_defined` exact (q, x)));
    intros until outD.
  - refine (match outD with
            | DeepA (Thunk (FOneA xD)) _ _ => _
            | _ => _
            end); intro Happrox;
      repeat match goal with
        | H : ?x `less_defined` ?y |- _ =>
            (head_is_constructor_or_proj x + head_is_constructor_or_proj y); invert_clear H
        end; repeat constructor; simpl; repeat constructor; auto.
  - refine (match outD with
            | DeepA fD mD _ => _
            | _ => bottom
            end); intro Happrox; teardown;
      repeat match goal with
        | H : ?x `less_defined` ?y |- _ =>
            (head_is_constructor_or_proj x + head_is_constructor_or_proj y); invert_clear H
        end; repeat constructor; auto.
  - refine (match outD with
            | DeepA fD mD' _ => _
            | _ => _
            end); try solve [ repeat constructor ].
    intro Happrox.
    invert_clear Happrox as [ | ? ? ? ? ? ? HfD HmD' HrD ].
    invert_clear HmD' as [ | mA' ? HmA' ]. 1: repeat constructor; auto.
    specialize (H _ _ HmA').
    simpl. destruct (Tick.val (pushD m (y, x) mA')) as [ mD pD ].
    invert_clear H as [ HmD HpD ]. simpl in *.
    invert_clear HpD as [ | p ? Hp ]; [ | destruct p; invert_clear Hp ];
      repeat constructor; simpl; auto.
Qed.

Definition pushA (A : Type) (q : T (QueueA A)) (x : T A) : M (QueueA A) :=
  let fix pushA_ (A : Type) (qA : QueueA A) (x : T A) : M (QueueA A) :=
    bind tick
      (fun _ =>
         match qA with
         | NilA => ret (DeepA (Thunk (FOneA x)) (Thunk NilA) (Thunk RZeroA))
         | DeepA f m r =>
             forcing r
               (fun r =>
                  match r with
                  | RZeroA => ret (DeepA f m (Thunk (ROneA x)))
                  | ROneA y =>
                      let~ m' := (fun m => pushA_ _ m (zipT y x)) $! m in
                      ret (DeepA f m' (Thunk RZeroA))
                  end)
         end)
  in (fun q => pushA_ _ q x) $! q.

Lemma pushD_spec (A : Type) `{LDA : LessDefined A, !Reflexive LDA}
  (q : Queue A) (x : A) (outD : QueueA A)
  : outD `is_approx` push q x ->
    forall qD xD, (qD, xD) = Tick.val (pushD q x outD) ->
    let dcost := Tick.cost (pushD q x outD) in
    pushA qD xD [[ fun out cost => outD `less_defined` out /\ cost <= dcost ]].
Proof.
  intros. revert A q x LDA Reflexive0 outD H qD xD H0 dcost.
  apply (push_ind
           (fun A q x q' =>
              forall `{LDA : LessDefined A, !Reflexive LDA},
                forall outD,
                  outD `is_approx` q' ->
                  forall qD xD,
                    (qD, xD) = Tick.val (pushD q x outD) ->
                    let dcost := Tick.cost (pushD q x outD) in
                    pushA qD xD [[fun (out : QueueA A) (cost : nat) =>
                                    outD `less_defined` out /\ cost <= dcost]]));
    intros; revert H H0 dcost.
  - assert (@Reflexive (T A) less_defined) by apply Reflexive_LessDefined_T.
    refine (match outD with
            | DeepA (Thunk (FOneA xD)) _ _ => _
            | _ => _
            end); mgo'; repeat constructor; auto.
  - assert (@Reflexive (T (FrontA A)) less_defined) by apply Reflexive_LessDefined_T.
    assert (@Reflexive (T (QueueA (A * A))) less_defined) by apply Reflexive_LessDefined_T.
    refine (match outD with
            | DeepA fD mD _ => _
            | _ => _
            end); mgo'; destruct t; mgo'; repeat constructor; auto.
  - assert (@Reflexive (T (FrontA A)) less_defined) by apply Reflexive_LessDefined_T.
    revert H1. refine (match outD with
                       | DeepA fD mD _ => _
                       | _ => _
                       end); mgo_.
    + mgo'.
    + invert_clear H2. invert_clear H3.
      * mgo'. apply optimistic_skip. mgo'.
      * simpl in *.
        destruct (Tick.val (pushD m (y, x) x0)) as [ mD pD ] eqn: HpushD.
        symmetry in HpushD.
        destruct (H0 _ _ _ H3 _ _ HpushD) as [ ? [ ? [ ? [ ? ? ] ] ] ].
        destruct pD as [ [ ? ? ] | ]; simpl in *.
        -- invert_clear H1. mgo_.
           apply optimistic_thunk_go.
           repeat eexists.
           ++ exact H5.
           ++ auto.
           ++ lia.
        -- invert_clear H1. mgo_.
           apply optimistic_thunk_go.
           repeat eexists.
           ++ exact H5.
           ++ auto.
           ++ lia.
Qed.

(* pop *)

(* Note that this definition is structured so as to appear maximally lazy. *)
Fixpoint pop (A : Type) (q : Queue A) : option (A * Queue A) :=
  match q with
  | Nil => None
  | Deep f m r =>
      match f with
      | FOne x =>
          let q :=
            let p := pop m in
            match p with
            | Some (yz, m') =>
                let (y, z) := yz in
                Deep (FTwo y z) m' r
            | None =>
                match r with
                | RZero => Nil
                | ROne y => Deep (FOne y) Nil RZero
                end
            end
          in Some (x, q)
      | FTwo x y => Some (x, Deep (FOne y) m r)
      end
  end.

Fixpoint popA' (A : Type) (q : QueueA A) : M (option (T A * T (QueueA A))) :=
  tick >>
    match q with
    | NilA => ret None
    | DeepA f m r =>
        let! f := force f in
        match f with
        | FOneA x =>
            let~ q :=
              let! p := popA' $! m in
              match p with
              | Some (yz, m') =>
                  let (y, z) := unzipT yz in
                  ret (DeepA (Thunk (FTwoA y z)) m' r)
              | None =>
                  let! r := force r in
                  match r with
                  | RZeroA => ret NilA
                  | ROneA y => ret (DeepA (Thunk (FOneA y)) (Thunk NilA) (Thunk RZeroA))
                  end
              end
            in ret (Some (x, q))
        | FTwoA x y => ret (Some (x, Thunk (DeepA (Thunk (FOneA y)) m r)))
        end
    end.

Definition popA (A : Type) (q : T (QueueA A)) : M (option (T A * T (QueueA A))) :=
  popA' $! q.

Fixpoint popD (A : Type) (q : Queue A) (outD : option (T A * T (QueueA A))) :
  Tick (T (QueueA A)) :=
  Tick.tick >>
    match q with
    | Nil => Tick.ret (Thunk NilA)
    | Deep f m r =>
        match f with
        | FOne x =>
            let p := pop m in
            match p with
            | Some (yz, m') =>
                match outD with
                | Some (xD, qD) =>
                    let+ (mD, rD) :=
                      match qD with
                      | Thunk (DeepA fD mD' rD) =>
                          let pD :=
                            match fD with
                            (* XXX This is wrong! *)
                            | Thunk (FTwoA yD zD) => zipT yD zD
                            | _ => bottom
                            end in
                          let+ mD := popD m (Some (pD, mD')) in
                          Tick.ret (mD, rD)
                      | _ => bottom
                      end in
                    Tick.ret (Thunk (DeepA (Thunk (FOneA xD)) mD rD))
                | _ => bottom
                end
            | None =>
                match r with
                | RZero =>
                    match outD with
                    | Some (xD, _) =>
                        let+ mD := popD m None in
                        Tick.ret (Thunk (DeepA (Thunk (FOneA xD)) mD (Thunk RZeroA)))
                    | _ => bottom
                    end
                | ROne y =>
                    match outD with
                    | Some (xD, Thunk (DeepA (Thunk (FOneA yD)) _ _)) =>
                        let+ mD := popD m None in
                        Tick.ret (Thunk (DeepA (Thunk (FOneA xD)) mD (Thunk (ROneA yD))))
                    | _ => bottom
                    end
                end
            end
        | FTwo x y =>
            match outD with
            | Some (xD, qD) =>
                let '(yD, mD, rD) :=
                  match qD with
                  | Thunk (DeepA fD mD rD) =>
                      let yD :=
                        match fD with
                        | Thunk (FOneA yD) => yD
                        | _ => bottom
                        end in
                      (yD, mD, rD)
                  | _ => bottom
                  end in
                Tick.ret (Thunk (DeepA (Thunk (FTwoA xD yD)) mD rD))
            | _ => bottom
            end
        end
    end.

(* Lemma popD_approx (A : Type) `{LDA : LessDefined A, !Reflexive LDA} *)
(*   (q : Queue A) (outD : option (T A * T (QueueA A))) : *)
(*   outD `is_approx` pop q -> Tick.val (popD q outD) `is_approx` q. *)
(* Proof. *)
(*   induction q as [ | ? f m IHq r ]. *)
(*   - assert (@Reflexive (T (QueueA A)) less_defined) *)
(*       as HReflexive_T_QueueA_A *)
(*         by apply Reflexive_LessDefined_T. *)
(*     simpl. inversion_clear 1. reflexivity. *)
(*   - simpl. destruct f as [ x | x y ]. *)
(*     + destruct (pop m) as [ [ [ y z ] m' ] ? | ] eqn:Hpop. *)
(*       * inversion_clear 1 as [ | [ xD qD ] ? [ HxD HqD ] ]. simpl in *. *)
(*         inversion_clear HqD as [ | qA ? HqA ]; try solve [ auto ]. *)
(*         inversion_clear HqA as [ | fD' ? mD' ? rD ? HfD' HmD' HrD ]. *)
(*         inversion_clear HfD' as [ | fA ? HfA ]; try solve [ auto ]. *)
(*         inversion_clear HfA as [ | yD ? zD ? HyD HzD ]. *)
(*         simpl. repeat constructor; try solve [ auto ]. *)
(*         apply IHq; try solve [ auto with * ]. *)
(*         repeat constructor; try solve [ auto ]. simpl. *)
(*         change (exact (y, z)) with (zipT (Thunk y) (Thunk z)). *)
(*         apply zipT_less_defined; auto. *)
(*       * destruct r as [ | y ]. *)
(*         -- inversion_clear 1 as [ | [ xD qD ] ? [ HxD HqD ] ]. simpl in *. *)
(*            inversion_clear HqD as [ | qA ? HqA ]; try solve [ auto ]. *)
(*            inversion_clear HqA. simpl. *)
(*            repeat constructor; try solve [ auto ]. *)
(*            apply IHq; repeat constructor; auto with *. *)
(*         -- inversion_clear 1 as [ | [ xD qD ] ? [ HxD HqD ] ]. simpl in *. *)
(*            inversion_clear HqD as [ | qA ? HqA ]; try solve [ auto ]. *)
(*            inversion_clear HqA as [ | fD ? mD ? rD ? HfD HmD HrD ]. *)
(*            inversion_clear HfD as [ | fA ? HfA ]; try solve [ auto ]. *)
(*            inversion_clear HfA as [ yD ? HyD | ]. simpl. *)
(*            repeat constructor; try solve [ auto ]. *)
(*            apply IHq; repeat constructor; auto with *. *)
(*     + inversion_clear 1 as [ | [ xD qD ] ? [ HxD HqD ] ]. simpl in *. *)
(*       inversion_clear HqD as [ | qA ? HqA ]; try solve [ auto ]. *)
(*       inversion_clear HqA as [ | fD ? mD ? rD ? HfD HmD HrD ]. *)
(*       inversion_clear HfD as [ | fA ? HfA ]; try solve [ auto ]. *)
(*       inversion_clear HfA as [ yD ? HyD | ]. simpl. repeat constructor; auto. *)
(* Qed. *)

(* XXX This is probably unprovable right now. *)
Lemma popD_spec :
  forall (A : Type) `{LDA : LessDefined A, !Reflexive LDA}
         (q : Queue A) (outD : option (T A * T (QueueA A))),
    outD `is_approx` pop q ->
    forall qD, qD = Tick.val (popD q outD) ->
    let dcost := Tick.cost (popD q outD) in
    popA qD [[ fun out cost => outD `less_defined` out /\ cost <= dcost ]].
Proof.
  intros A HRefl_A LDA q outD.
  induction q eqn:Hq.
  - mgo'. repeat constructor; auto.
  - assert (@Reflexive (T A) less_defined)
      as HRefl_T_A
        by apply Reflexive_LessDefined_T.
    assert (@Reflexive (T (FrontA A)) less_defined)
      as HRefl_T_FrontA_A
        by apply Reflexive_LessDefined_T.
    assert (@Reflexive (T (QueueA (A * A))) less_defined)
      as HRefl_T_QueueA_A_A
        by apply Reflexive_LessDefined_T.
    assert (@Reflexive (T (RearA A)) less_defined)
      as HRefl_T_RearA_A
        by apply Reflexive_LessDefined_T.
    simpl. destruct f eqn:Hf.
    + destruct (pop q0) eqn:Hpop.
      * destruct p as [ [ y z ] m' ].
        inversion_clear 1 as [ | [ xD qD ] ? [ HxD HqD ] ]. simpl in *.
        inversion_clear HqD.
        -- intros. subst. mgo_.
           apply optimistic_skip. mgo_. repeat constructor; auto.
        -- inversion_clear H. inversion_clear H0.
           ++ simpl. inversion_clear 1. mgo_.
              apply optimistic_thunk_go. mgo_.
              specialize (IHq0 _ _ q0 (Some (bottom, q1))
                            ltac:(auto) ltac:(repeat constructor; auto)
                                               (Tick.val (popD q0 (Some (bottom, q1))))
                                               ltac:(auto)).
              eapply optimistic_mon; eauto.
              inversion_clear 1.
              inversion_clear H0.
              destruct y0.
              inversion_clear H. simpl in *.
              destruct t.
              ** simpl. destruct x1. mgo_.
                 split; lia + (repeat constructor; auto).
              ** simpl. mgo_.
                 split; lia + (repeat constructor; auto).
           ++ inversion_clear H.
              ** simpl. inversion_clear 1. mgo_.
                 apply optimistic_thunk_go. mgo_.
                 specialize (IHq0 _ _ q0 (Some (zipT x1 y1, q1))
                               ltac:(auto) ltac:(repeat constructor; simpl; auto with * )
                                                  (Tick.val (popD q0 (Some (zipT x1 y1, q1))))
                                                  ltac:(auto)).
                 eapply optimistic_mon; eauto.
                 inversion_clear 1. inversion_clear H4.
                 destruct y0. destruct t.
                 --- destruct x3. mgo_.
                     inversion_clear H. simpl in *.
                     destruct IHq0 as [ ? [ ? [ ? [ ? ? ] ] ] ].
                     split; repeat constructor; auto.
Admitted.

(* Length of a queue. *)
Fixpoint length (A : Type) (q : Queue A) : nat :=
  match q with
  | Nil => 0
  | Deep f m r => match f with
                  | FOne _ => 1
                  | FTwo _ _ => 2
                  end +
                    match r with
                    | RZero => 0
                    | ROne _ => 1
                    end +
                    2 * length m
  end.

(* Height of a queue approximation. *)
Fixpoint heightA (A : Type) (qA : QueueA A) : nat :=
  match qA with
  | NilA => 0
  | DeepA _ mD _ => 1 + match mD with
                        | Thunk mA => heightA mA
                        | Undefined => 0
                        end
  end.

(* Cost *)

Lemma pushD_cost_mono : forall (A : Type) `{LessDefined A} (q : Queue A) (x : A) (d1 d2 : QueueA A),
    d1 `less_defined` d2 ->
    Tick.cost (pushD q x d1) <= Tick.cost (pushD q x d2).
Proof.
  fix SELF 3. intros. refine (match q with
                              | Nil => _
                              | Deep f m RZero => _
                              | Deep f m (ROne y) => _
                              end).
  - teardown; auto.
  - teardown; lia.
  - teardown; lia + (repeat invert_constructor).
    unfold thunkD. teardown; lia + (repeat invert_constructor).
    do 2 rewrite Nat.add_0_r.
    apply le_n_S, (SELF _ (@LessDefined_prod A A H H) m). exact H1.
Qed.

Lemma pushD_cost_exact_maximal (A : Type) `{LDA : LessDefined A} `{Reflexive A LDA}
  (q : Queue A) (x : A) (outD : QueueA A) :
  outD `is_approx` push q x ->
  Tick.cost (pushD q x outD) <= Tick.cost (pushD q x (exact (push q x))).
Proof.
  intros. apply pushD_cost_mono. assumption.
Qed.

Lemma pushD_cost_worstcase :
  forall (A : Type) `{LDA : LessDefined A} `{Reflexive A LDA}
         (q : Queue A) (x : A) (outD : QueueA A),
    outD `is_approx` push q x ->
    Tick.cost (pushD q x outD) <= heightA outD.
Proof.
  intros. revert A q x LDA H outD H0.
  apply (push_ind (fun A q x q' =>
                     forall `{LDA : LessDefined A, !Reflexive LDA} outD,
                       outD `less_defined` exact (push q x) ->
                       Tick.cost (pushD q x outD) <= heightA outD));
    try solve [ invert_clear 2; teardown; lia ].
  simpl. invert_clear 3.
  invert_clear H1; simpl; try solve [ lia ].
  destruct (Tick.val (pushD m (y, x) x0)) as [ mD pD ] eqn:HpushD.
  specialize (H _ _ _ H1).
  destruct pD as [ [ yD xD ] | ]; simpl in *; lia.
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
        let c := match fD, mD with
                 | Undefined, Undefined => 0
                 | _, _ => T_rect _ size_FrontA 1 fD - T_rect _ size_RearA 0 rD
                 end
        in c + @Debitable_T _ (debt_QueueA _) mD
    end.

Lemma pushD_cost : forall (A : Type) `{LessDefined A} (q : Queue A) (x : A) (outD : QueueA A),
    outD `is_approx` push q x ->
    let inM := pushD q x outD in
    let cost := Tick.cost inM in
    let (qD, _) := Tick.val inM in
    debt qD + cost <= 2 + debt outD.
Proof.
  intros ? LDA ? ?. revert A q x LDA.
  apply (push_ind (fun (A : Type) (q : Queue A) (x : A) (q' : Queue A) =>
                     forall LDA outD,
                       outD `is_approx` q' ->
                       let inM := pushD q x outD in
                       let cost := Tick.cost inM in
                       let (qD, _) := Tick.val inM in
                       debt qD + cost <= 2 + debt outD)).
  - intros until outD. refine (match outD with
                               | DeepA (Thunk (FOneA xD)) _ _ => _
                               | _ => _
                               end); repeat (unfold debt; simpl); lia.
  - intros until outD. refine (match outD with
                               | DeepA fD mD (Thunk (ROneA xD)) => _
                               | _ => _
                               end); repeat (unfold debt; simpl); teardown; simpl; lia.
  - intros until outD. refine (match outD with
                               | DeepA fD mD _ => _
                               | _ => _
                               end); invert_clear 1.
    invert_clear H1.
    + repeat (unfold debt, T_rect, size_FrontA, size_RearA; teardown; simpl); lia.
    + specialize (H _ _ H1). simpl in *.
      destruct (Tick.val (pushD m (y, x) x0))
        as [ mD' [ [ yD xD ] | ] ]
             eqn:HpushD.
      * unfold debt. simpl. unfold T_rect, size_FrontA, size_RearA.
        teardown_eqns;
          unfold debt; simpl;
          change (Debitable_T mD') with (debt mD');
          change (Debitable_QueueA x0) with (debt x0); try lia;
          try solve [
              match goal with
              | H : context [ match ?a with _ => _ end ] |- _ => destruct a
              end; teardown;
              repeat (simpl in *; match goal with
                                  | H : ?x `less_defined` ?y |- _ =>
                                      (head_is_constructor x + head_is_constructor y); invert_clear H
                                  end)
            ].
        -- destruct t.
           ++ destruct x2.
              ** invert_clear H5.
              ** invert_clear H5. invert_clear H2. invert_clear H2.
           ++ invert_clear H5.
        -- destruct t.
           ++ destruct x2.
              ** invert_clear H5.
              ** invert_clear H2. invert_clear H2.
           ++ discriminate.
        -- destruct t.
           ++ destruct x2.
              ** discriminate.
              ** invert_clear H2. invert_clear H2.
           ++ discriminate.
        -- destruct mD', t; try destruct x2; try lia.
        -- destruct t, mD'; try destruct x1; try lia.
           ** invert_clear H2. invert_clear H2.
           ** invert_clear H2. invert_clear H2.
      * simpl. unfold debt. simpl.
        destruct fD, t; try destruct x1; try destruct x2; simpl.
        -- unfold debt at 1. simpl. change (Debitable_T mD') with (debt mD'). lia.
        -- invert_clear H2. invert_clear H2.
        -- change (Debitable_T mD') with (debt mD'). lia.
        -- invert_clear H2. invert_clear H2.
        -- unfold debt at 1. simpl. change (Debitable_T mD') with (debt mD'). lia.
        -- simpl. change (Debitable_T mD') with (debt mD'). lia.
        -- unfold debt at 1. simpl. change (Debitable_T mD') with (debt mD').
           destruct mD'; lia.
        -- invert_clear H2. invert_clear H2.
        -- unfold debt at 1. simpl. change (Debitable_T mD') with (debt mD').
           destruct mD'; lia.
Qed.

From Coq Require Import List.
Import ListNotations.
From Clairvoyance Require Import Interfaces.
Open Scope tick_scope.

Inductive op (A : Type) : Type :=
| Empty
| Push (x : A).

#[global] Instance WellFormed_Queue (A : Type) : WellFormed (Queue A) := fun _ => True.

#[global] Instance Eval_Queue (A : Type) : Eval (op A) (Queue A) :=
  fun op args => match op, args with
                 | Empty, [] => [empty]
                 | Push x, [q] => [push q x]
                 | _, _ => []
                 end.

#[global] Instance Budget_Queue (A : Type) : Budget (op A) (Queue A) :=
  fun _ _ => 2.

#[global] Instance Demand_Queue (A : Type) : Demand (op A) (Queue A) (T (QueueA A)) :=
  fun op args argsA =>
    match op, args, argsA with
    | Empty, [], [outD] =>
        let outD := forceD (bottom_of (exact empty)) outD in
        emptyD outD >> Tick.ret []
    | Push x, [q], [outD] =>
        let outD := forceD (bottom_of (exact (push q x))) outD in
        let+ (qD, _) := pushD q x outD in
        Tick.ret [qD]
    | _, _, _ => Tick.ret (bottom_of (exact args))
    end.

#[global] Instance Potential_Queue (A : Type) : Potential (T (QueueA A)) :=
  fun qD => match qD with
            | Thunk qA => debt qA
            | Undefined => 0
            end.

Lemma potential_bottom_of (A : Type) (q : Queue A) :
  Potential_Queue (bottom_of (exact q)) = 0.
Proof.
  destruct q; reflexivity.
Qed.
#[global] Hint Resolve potential_bottom_of : core.

Lemma sumof_potential_bottom_of (A : Type) (qs : list (Queue A)) :
  sumof Potential_Queue (bottom_of (exact qs)) = 0.
Proof.
  induction qs; auto.
Qed.
#[global] Hint Resolve sumof_potential_bottom_of : core.

Lemma potential_pushD_bottom_of (A : Type) (q : Queue A) (x : A) :
  let inD := pushD q x (bottom_of (exact (push q x))) in
  let (qD, _) := Tick.val inD in
  Tick.cost inD = 1 /\ Potential_Queue qD = 0.
Proof.
  refine (match q with
          | Nil => _
          | Deep f m RZero => _
          | Deep f m (ROne y) => _
          end); simpl; auto.
Qed.
#[global] Hint Resolve potential_pushD_bottom_of : core.

Theorem physicist's_argumentD :
  forall (A : Type) `{LDA : LessDefined A, PreOrder A LDA, LBA : Lub A, @LubLaw A LBA LDA},
    @Physicist'sArgumentD
      (op A) (Queue A) (T (QueueA A))
      _ _ _ _ _ _.
Proof.
  intro A. pose proof (@sumof_potential_bottom_of A) as Hpb.
  unfold bottom_of, exact in Hpb.
  unfold Physicist'sArgumentD.
  intros LDA HPreOrder LBA HLubLaw o args _ output.
  refine (match o, args, output with
          | Empty, [], [_] => _
          | Push x, [q], [outD] => _
          | _, _, _ => _
          end); try solve [ do 2 invert_clear 1; simpl in *;
                            try (rewrite Hpb); lia ].
  - invert_clear 1. invert_clear 1. simpl. invert_clear H; try invert_clear H; simpl; lia.
  - invert_clear 1 as [ | ? ? ? ? HoutD _ ]. invert_clear HoutD as [ | ? ? HoutD ].
    + invert_clear 1.
      pose proof (potential_pushD_bottom_of q x). cbn in H.
      destruct (Tick.val (pushD q x (bottom_of (exact (push q x))))) eqn:HpushD.
      simpl. lia.
    + pose proof (pushD_cost _ _ HoutD) as Hcost. cbn in Hcost.
      invert_clear 1.
      destruct (Tick.val (pushD q x x0)) as [ qD xD ]. simpl.
      change (Potential_Queue qD) with (debt qD). lia.
Qed.
#[export] Existing Instance physicist's_argumentD.

Lemma pd (A : Type)
  `{LDA : LessDefined A, PA : PreOrder A LDA, LBA : Lub A, LLA : @LubLaw A LBA LDA} :
  @PureDemand (op A) (Queue A) (T (QueueA A))
    IsApproxAlgebra_QueueA
    Eval_Queue
    Demand_Queue.
Proof.
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
    replace t with (fst (Tick.val (pushD q x (bottom_of (exact (push q x)))))).
      + apply pushD_approx, bottom_is_least. reflexivity.
      + destruct (Tick.val (pushD q x (bottom_of (exact (push q x))))).
        invert_clear HpushD. auto.
  - simpl.
    destruct (Tick.val (pushD q x x0)) eqn:HpushD. simpl.
    constructor; auto.
    replace t with (fst (Tick.val (pushD q x x0))).
    + apply pushD_approx. auto.
    + destruct (Tick.val (pushD q x x0)). invert_clear HpushD. auto.
Qed.

Definition Exec_QueueA (A : Type) : Exec (op A) (T (QueueA A)) :=
  fun o args => match o, args with
                | Empty, [] => let! q := emptyA in ret [Thunk q]
                | Push x, [q] => let! q' := pushA q (Thunk x) in ret [Thunk q']
                | _, _ => ret []
                end.
