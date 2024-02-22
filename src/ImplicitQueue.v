From Coq Require Import Arith Psatz Relations RelationClasses.
From Clairvoyance Require Import Core Approx Tick.

Import Tick.Notations.

Set Implicit Arguments.
Set Contextual Implicit.
Set Maximal Implicit Insertion.

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

#[local] Existing Instance Exact_id | 1.

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

#[global] Instance PreOrder_LessDefined_FrontA A `{LessDefined A, PreOrder A less_defined} :
  PreOrder (@less_defined (FrontA A) _).
Proof.
  destruct H0. constructor; eauto.
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
Admitted.

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

#[global] Instance PreOrder_LessDefined_RearA A `{LessDefined A, PreOrder A less_defined} :
  PreOrder (@less_defined (RearA A) _).
Proof.
  destruct H0. constructor; eauto.
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

#[global] Instance ExactMaximal_Rear A B `{ExactMaximal B A} :
  ExactMaximal (RearA B) (Rear A).
Admitted.

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

#[global] Instance Reflexive_LessDefined_QueueA A `{LDA : LessDefined A, Reflexive A LDA} :
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

Lemma LessDefined_QueueA_antisym A `{LessDefined A} :
  (forall (x y : A), x `less_defined` y -> y `less_defined` x -> x = y) ->
  forall (x y : QueueA A), x `less_defined` y -> y `less_defined` x -> x = y.
Proof.
Admitted.
#[global] Hint Resolve LessDefined_QueueA_antisym : core.

#[global] Instance PartialOrder_LessDefined_QueueA A `{LessDefined A, PartialOrder A eq less_defined} :
  PartialOrder eq (@less_defined (QueueA A) _).
Proof.
  apply make_partial_order. apply LessDefined_QueueA_antisym. firstorder.
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

#[global] Instance ExactMaximal_Queue A `{ExactMaximal A A} :
  ExactMaximal (QueueA A) (Queue A).
Admitted.

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

Fixpoint pushD (A : Type) (q : Queue A) (x : A) (outD : QueueA A) : Tick (T (QueueA A) * T A) :=
  Tick.tick >>
    match q with
    | Nil => match outD with
             | DeepA (Thunk (FOneA xD)) (Thunk NilA) (Thunk RZeroA) =>
                 Tick.ret (Thunk NilA, xD)
             | _ => bottom
             end
    | Deep f m RZero => match outD with
                        | DeepA fD mD (Thunk (ROneA xD)) =>
                            Tick.ret (Thunk (DeepA fD mD (Thunk RZeroA)), xD)
                        | _ => bottom
                        end
    | Deep f m (ROne y) => match outD with
                           | DeepA fD mD (Thunk RZeroA) =>
                               let+ (mD, pD) := thunkD (pushD m (y, x)) mD in
                               let (yD, xD) := unzipT pD in
                               Tick.ret (Thunk (DeepA fD mD (Thunk (ROneA yD))), xD)
                           | _ => bottom
                           end
    end.

Lemma push_is_Deep (A : Type) (q : Queue A) (x : A) : exists f m r, push q x = Deep f m r.
Proof.
  refine (match q with
          | Nil => _
          | Deep f m RZero => _
          | Deep f m (ROne y) => _
          end); simpl; eauto.
Qed.

Lemma pushD_approx : forall (A : Type) `{LessDefined A} (q : Queue A) (x : A) (outD : QueueA A),
    outD `is_approx` push q x -> Tick.val (pushD q x outD) `is_approx` (q, x).
Proof.
  intros ? LDA ? ? ?. revert A q x LDA outD.
  apply (push_ind (fun A q x q' => forall `{LessDefined A} (outD : QueueA A),
                       outD `less_defined` exact q' ->
                       Tick.val (pushD q x outD) `less_defined` exact (q, x)));
    intros until outD.
  - refine (match outD with
            | DeepA (Thunk (FOneA xD)) (Thunk NilA) (Thunk RZeroA) => _
            | _ => _
            end); intro Happrox;
      repeat match goal with
        | H : ?x `less_defined` ?y |- _ =>
            (head_is_constructor_or_proj x + head_is_constructor_or_proj y); invert_clear H
        end; repeat constructor; simpl; repeat constructor; auto.
  - refine (match outD with
            | DeepA fD mD (Thunk (ROneA xD)) => _
            | _ => bottom
            end); intro Happrox;
      repeat match goal with
        | H : ?x `less_defined` ?y |- _ =>
            (head_is_constructor_or_proj x + head_is_constructor_or_proj y); invert_clear H
        end; repeat constructor; auto.
  - refine (match outD with
            | DeepA fD mD' (Thunk RZeroA) => _
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

Fixpoint pop (A : Type) (q : Queue A) : option (A * Queue A) :=
  match q with
  | Nil => None
  | Deep (FOne x) m r => Some (x, match pop m with
                                  | None => match r with
                                            | RZero => Nil
                                            | ROne y => Deep (FOne y) Nil RZero
                                            end
                                  | Some (y, z, m) => Deep (FTwo y z) m r
                                  end)
  | Deep (FTwo x y) m r => Some (x, Deep (FOne y) m r)
  end.

Lemma pop_ind :
  forall (P : forall (A : Type), Queue A -> option (A * Queue A) -> Prop),
    (forall A, P A Nil None) ->
    (forall A x y m r, P A (Deep (FTwo x y) m r) (Some (x, Deep (FOne y) m r))) ->
    (forall A x m r, P (prod A A) m (pop m) -> P A (Deep (FOne x) m r) (Some (x, match pop m with
                                                                                 | None => match r with
                                                                                           | RZero => Nil
                                                                                           | ROne y => Deep (FOne y) Nil RZero
                                                                                           end
                                                                                 | Some (y, z, m) => Deep (FTwo y z) m r
                                                                                 end))) ->
    forall A (q : Queue A), P A q (pop q).
Proof.
  intros ? H1 H2 H3. fix SELF 2. intros ? q.
  refine (match q with
          | Nil => _
          | Deep (FOne x) m r => _
          | Deep (FTwo x y) m r => _
          end); intros.
  - apply H1.
  - apply H3. apply SELF.
  - apply H2.
Qed.

Fixpoint popD A (q : Queue A) (outD : option (T A * T (QueueA A))) :
  Tick (T (QueueA A)) :=
  Tick.tick >>
    match q with
    | Nil => match outD with
             | None => Tick.ret (Thunk NilA)
             | _ => bottom
             end
    | Deep (FOne x) m r => match outD with
                           | Some (xD, Thunk NilA) =>
                               (* `pop q` is `None`, `r` is `RZero` *)
                               Tick.ret (Thunk (DeepA (Thunk (FOneA xD)) (Thunk NilA) (Thunk RZeroA)))
                           | Some (xD, Thunk (DeepA (Thunk (FOneA yD)) (Thunk NilA) (Thunk RZeroA))) =>
                               (* `pop q` is `None`, `r` is `ROne y` *)
                               Tick.ret (Thunk (DeepA (Thunk (FOneA xD)) (Thunk NilA) (Thunk (ROneA yD))))
                           | Some (xD, Thunk (DeepA (Thunk (FTwoA yD zD)) mD rD)) =>
                               (* `pop q` is `Some ((y, z), q)` *)
                               let+ mD := popD m (Some (zipT yD zD, mD)) in
                               Tick.ret (Thunk (DeepA (Thunk (FOneA xD)) mD rD))
                           | _ => bottom
                           end
    | Deep (FTwo x y) m r => match outD with
                             | Some (xD, Thunk (DeepA (Thunk (FOneA yD)) mD rD)) =>
                                 Tick.ret (Thunk (DeepA (Thunk (FTwoA xD yD)) mD rD))
                             | _ => bottom
                             end
    end.

Lemma popD_approx :
  forall (A : Type) `{LessDefined A} (q : Queue A) (outD : option (T A * T (QueueA A))),
    outD `is_approx` pop q -> Tick.val (popD q outD) `is_approx` q.
Proof.
  intros A LDA q outD. revert A q LDA outD.
  apply (pop_ind (fun A q p =>
                    forall `{LessDefined A} (outD : option (T A * T (QueueA A))),
                      outD `less_defined` exact p ->
                      Tick.val (popD q outD) `less_defined` exact q));
  intros until outD.
  - refine (match outD with
            | None => _
            | _ => _
            end); repeat constructor.
  - refine (match outD with
            | Some (xD, Thunk (DeepA (Thunk (FOneA yD)) mD rD)) => _
            | _ => _
            end); intro Happrox;
      repeat (match goal with
              | H : ?x `less_defined` ?y |- _ =>
                  (head_is_constructor x + head_is_constructor y); invert_clear H
              end; simpl in * ); repeat constructor; auto.
  - refine (match outD with
            | Some (xD, Thunk NilA) => _
            | Some (xD, Thunk (DeepA (Thunk (FOneA yD)) (Thunk NilA) (Thunk RZeroA))) => _
            | Some (xD, Thunk (DeepA (Thunk (FTwoA yD zD)) mD rD)) => _
            | _ => _
            end); revert H;
      destruct (pop m) as [ [ [ y z ] m' ]  | ] eqn:Hpopeq;
      teardown;
      intros;
      repeat (match goal with
              | H : ?x `less_defined` ?y |- _ =>
                  (head_is_constructor x + head_is_constructor y); invert_clear H
              end; simpl in * );
      repeat constructor; auto.
    + replace m with (@Nil (A * A)); try symmetry; auto with *.
    + replace m with (@Nil (A * A)); try symmetry; auto with *.
    + apply H. invert_clear H1; invert_clear H2; repeat constructor; auto.
    + apply H. invert_clear H1; invert_clear H4; repeat constructor; auto.
Qed.

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
  fix SELF 4. intros ? ? HReflexive ? ? ?.
  refine (match q with
          | Nil => _
          | Deep f m RZero => _
          | Deep f m (ROne y) => _
          end); intro Happrox.
  1, 2: invert_clear Happrox; teardown; simpl; lia.
  invert_clear Happrox as [ | fD ? mD ? rD ? HfD HmD HrD ].
  invert_clear HrD as [ | rA ? HrA ]. 1: simpl; lia.
  invert_clear HrA. invert_clear HmD as [ | mA ? HmA ]. 1: simpl; lia.
  simpl. replace (Tick.cost (let
                        '(mD, pD) := Tick.val (pushD m (y, x) mA) in
                      let (yD, xD) := unzipT pD in
                      Tick.ret (Thunk (DeepA fD mD (Thunk (ROneA yD))), xD)))
    with 0. 2: destruct (Tick.val (pushD m (y, x) mA)) as [mD pD], (unzipT pD); auto.
  specialize (SELF _ _ _ _ _ _ HmA). lia.
Qed.

(* TODO Can this be derived from pushD_cost_worstcase? *)
Lemma push_cost_worstcase (A : Type) `{LDA : LessDefined A} `{Reflexive A LDA}
  (q : Queue A) (x : A) (outD : QueueA A) :
  outD `is_approx` push q x ->
  Tick.cost (pushD q x outD) <= Nat.log2 (2 + length q).
Proof.
  transitivity (Tick.cost (pushD q x (exact (push q x)))).
  - apply pushD_cost_exact_maximal. assumption.
  - clear dependent outD.
    revert dependent A. fix SELF 4. intros.
    refine (match q with
            | Nil => _
            | Deep f m RZero => _
            | Deep f m (ROne y) => _
            end).
    + auto.
    + simpl. change 1 with (Nat.log2 2). pose Nat.log2_le_mono. auto with arith.
    + simpl.
      destruct (Tick.val (pushD m (y, x) (Exact_Queue (push m (y, x))))).
      destruct (unzipT t0).
      simpl. rewrite Nat.add_0_r.
      transitivity (1 + Nat.log2 (2 + length m)).
      * apply le_n_S, (SELF _ LessDefined_prod Reflexive_LessDefined_prod).
      * transitivity (Nat.log2 (4 + 2 * length m)).
        -- replace (4 + 2 * length m) with (2 * (2 + length m)).
           ++ rewrite Nat.log2_double; auto with arith.
           ++ lia.
        -- apply Nat.log2_le_mono. destruct f; auto with arith.
Qed.

Lemma popD_cost_worstcase :
  forall (A : Type) `{LDA : LessDefined A} `{Reflexive A LDA}
         (q : Queue A) (outD : option (T A * T (QueueA A))),
    outD `is_approx` pop q ->
    Tick.cost (popD q outD) <= 1 + match outD with
                                   | None | Some (_, Undefined) => 0
                                   | Some (_, Thunk qA) => heightA qA
                                   end.
Proof.
  fix SELF 4. intros ? ? HReflexive ? ?. refine (match q with
                                                 | Nil => _
                                                 | Deep (FOne x) m r => _
                                                 | Deep (FTwo x y) m r => _
                                                 end).
  1, 3: invert_clear 1; teardown; simpl; lia.
  refine (match outD with
          | Some (xD, Thunk NilA) => _
          | Some (xD, Thunk (DeepA (Thunk (FOneA yD)) (Thunk NilA) (Thunk RZeroA))) => _
          | Some (xD, Thunk (DeepA (Thunk (FTwoA yD zD)) mD rD)) => _
          | _ => _
          end); simpl; try lia.
  clear q0 t0 f0.
  invert_clear 1 as [ | ? ? HmA ]. invert_clear HmA as [ Hx HqoutD ].
  invert_clear HqoutD as [ | ? ? HqoutA ].
  specialize (SELF _ _ _ m). revert SELF. revert HqoutA.
  refine (match pop m with
          | Some (y, z, m) => _
          | _ => _
          end).
  clear p0 p1.
  2: destruct r; intros;
  repeat match goal with
    | H : ?x `less_defined` ?y |- _ =>
        (head_is_constructor x + head_is_constructor y); invert_clear H
    end.
  intro HqoutA.
  assert (Some (zipT yD zD, mD) `less_defined` exact (Some (y, z, m))) as Hyzm.
  - invert_clear HqoutA as [ | ? ? ? ? ? ? HyzD HmD HrD ].
    invert_clear HyzD as [ | ? ? HyzA ].
    invert_clear HyzA as [ | ? ? ? ? HyD HzD ].
    invert_clear HyD; invert_clear HzD; repeat constructor; auto.
  - intro SELF. specialize (SELF _ Hyzm). lia.
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
        T_rect _ size_FrontA 1 fD - T_rect _ size_RearA 0 rD + @Debitable_T _ (debt_QueueA _) mD
    end.

Lemma pushD_cost : forall (A : Type) `{LessDefined A} (q : Queue A) (x : A) (outD : QueueA A),
    outD `is_approx` push q x ->
    let inM := pushD q x outD in
    let cost := Tick.cost inM in
    let (qD, _) := Tick.val inM in
    debt qD + cost <= 2 + debt outD.
Proof.
  (* Rearrange hypotheses to make the types work out. *)
  intros ? LDA ? ?. revert A q x LDA.
  apply (push_ind (fun (A : Type) (q : Queue A) (x : A) (q' : Queue A) =>
                     forall LDA outD,
                       outD `is_approx` q' ->
                       let inM := pushD q x outD in
                       let cost := Tick.cost inM in
                       let (qD, _) := Tick.val inM in
                       debt qD + cost <= 2 + debt outD)).
  - intros until outD. refine (match outD with
                               | DeepA (Thunk (FOneA xD)) (Thunk NilA) (Thunk RZeroA) => _
                               | _ => _
                               end); repeat (unfold debt; simpl); lia.
  - intros until outD. refine (match outD with
                               | DeepA fD mD (Thunk (ROneA xD)) => _
                               | _ => _
                               end); repeat (unfold debt; simpl); lia.
  - intros ? ? ? ? ? IH ? ? Happrox. invert_clear Happrox.
    invert_clear H1. 1: simpl; lia.
    invert_clear H1. invert_clear H0.
    + simpl. repeat (unfold debt, T_rect; simpl). destruct f1. 1: destruct x0. all: simpl; lia.
    + specialize (IH _ _ H0).
      destruct (push_is_Deep m (y, x)) as [ f' [ m' [ r' Hpush ] ] ]. rewrite Hpush in *.
      simpl.
      destruct (pushD m (y, x) x0) eqn:HpushD.
      simpl. destruct val.
      destruct t0; try destruct x1;
        do 3 (unfold debt at 1; simpl in * );
              destruct f1; try destruct x1; simpl; change (Debitable_T t) with (debt t); lia.
Qed.

Lemma popD_cost : forall (A : Type) `{LessDefined A} (q : Queue A) (outD : option (T A * T (QueueA A))),
    outD `is_approx` pop q ->
    let d := match outD with
             | None => 0
             | Some (_, qD) => debt qD
             end in
    let inM := popD q outD in
    let cost := Tick.cost inM in
    let inD := Tick.val inM in
    debt inD + cost <= 2 + d.
Proof.
  (* Rearrange hypotheses to make the types work out. *)
  intros ? LDA ?. revert A q LDA.
  apply (pop_ind (fun A q p =>
                    forall LDA outD,
                      outD `is_approx` p ->
                      let d := match outD with
                               | Some (_, qD) => debt qD
                               | None => 0
                               end in
                      let inM := popD q outD in
                      let cost := Tick.cost inM in
                      let inD := Tick.val inM in
                      debt inD + cost <= 2 + d));
    intros until outD.
  - destruct outD; simpl; lia.
  - refine (match outD with
            | Some (xD, Thunk (DeepA (Thunk (FOneA yD)) mD rD)) => _
            | _ => _
            end);
      repeat (unfold debt; simpl);
      try (destruct rD as [ rA | ]; [ destruct rA | ]; simpl);
      lia.
  - refine (match outD with
            | Some (xD, Thunk NilA) => _
            | Some (xD, Thunk (DeepA (Thunk (FOneA yD)) (Thunk NilA) (Thunk RZeroA))) => _
            | Some (xD, Thunk (DeepA (Thunk (FTwoA yD zD)) mD rD)) => _
            | _ => _
            end); try solve [ simpl; lia ].
    intro Happrox.
    invert_clear Happrox as [ | ? ? Happrox ].
    invert_clear Happrox as [ Hx HoutD ]. simpl in *. invert_clear HoutD as [ | ? ? HoutD ].
    destruct (pop m) as [ pD' | ] eqn:Hpop; simpl.
    + destruct pD' as [ p' q' ]. destruct p' as [ y z ].
      invert_clear HoutD as [ | ? ? ? ? ? ? Hyz Hm Hr ].
      invert_clear Hyz as [ | ? ? Hyz ]. invert_clear Hyz as [ | ? ? ? ? Hy Hz ].
      assert (Some (zipT yD zD, mD) `is_approx` Some (y, z, q')) as Happrox by
          (repeat constructor; simpl; auto; change (exact (y, z)) with (zipT (Thunk y) (Thunk z));
           apply zipT_less_defined; auto).
      specialize (H _ _ Happrox). simpl in H.
      destruct rD as [ r' | ]; [ destruct r' | ]; repeat (unfold debt; simpl);
        change (Debitable_T (Tick.val (popD m (Some (zipT yD zD, mD)))))
        with (debt (Tick.val (popD m (Some (zipT yD zD, mD)))));
        change (Debitable_T mD) with (debt mD);
        lia.
    + destruct r. 1: invert_clear HoutD.
      invert_clear HoutD as [ | ? ? ? ? ? ? Hyz Hm Hr ].
      invert_clear Hyz as [ | ? ? Hyz ]. invert_clear Hyz.
Qed.
