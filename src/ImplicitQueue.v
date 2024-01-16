From Coq Require Import Relations RelationClasses.
From Clairvoyance Require Import Core Approx Tick.

Import Tick.Notations.

Set Implicit Arguments.
Set Contextual Implicit.
Set Maximal Implicit Insertion.

(* Auxiliary stuff *)

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

Definition factorPairD A B (p : T (A * B)) : T A * T B :=
  match p with
  | Undefined => (Undefined, Undefined)
  | Thunk (x, y) => (Thunk x, Thunk y)
  end.

Definition unfactorPairD A B (p : T A) (q : T B) : T (A * B) :=
  match p, q with
  | Thunk x, Thunk y => Thunk (x, y)
  | _, _ => Undefined
  end.

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

Inductive QueueA (A : Type) : Type :=
| NilA : QueueA A
| DeepA : T (FrontA A) -> T (QueueA (A * A)) -> T (RearA A) -> QueueA A.

Inductive LessDefined_QueueA A `{LessDefined A} : LessDefined (QueueA A) :=
| LessDefined_NilA : NilA `less_defined` NilA
| LessDefined_DeepA f1 f2 q1 q2 r1 r2 :
  f1 `less_defined` f2 -> q1 `less_defined` q2 -> r1 `less_defined` r2 ->
  DeepA f1 q1 r1 `less_defined` DeepA f2 q2 r2.
#[global] Hint Constructors LessDefined_QueueA : core.
#[global] Existing Instance LessDefined_QueueA.

Lemma LessDefined_QueueA_refl A `{LessDefined A} :
  (forall (x : A), x `less_defined` x) -> forall (x : QueueA A), x `less_defined` x.
Proof.
Admitted.
#[global] Hint Resolve LessDefined_QueueA_refl : core.

#[global] Instance Reflexive_LessDefined_QueueA A `{LDA : LessDefined A, Reflexive A LDA} :
  Reflexive (@less_defined (QueueA A) _).
Proof.
  unfold Reflexive. eauto.
Qed.

Lemma LessDefined_QueueA_trans A `{LessDefined A} :
  (forall (x y z : A), x `less_defined` y -> y `less_defined` z -> x `less_defined` z) ->
  forall (x y z : QueueA A), x `less_defined` y -> y `less_defined` z -> x `less_defined` z.
Proof.
Admitted.
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

#[global] Instance Exact_Queue : forall A B `{Exact A B}, Exact (Queue A) (QueueA B) :=
  fix Exact_Queue _ _ _ q :=
    match q with
    | Nil => NilA
    | Deep f q r => DeepA (exact f) (Thunk (Exact_Queue _ _ _ q)) (exact r)
    end.

#[global] Instance ExactMaximal_Queue A B `{ExactMaximal B A} :
  ExactMaximal (QueueA B) (Queue A).
Admitted.

Fixpoint push A (q : Queue A) (x : A) : Queue A :=
  match q with
  | Nil => Deep (FOne x) Nil RZero
  | Deep f q RZero => Deep f q (ROne x)
  | Deep f q (ROne y) => Deep f (push q (y, x)) RZero
  end.

Fixpoint pushD A (q : Queue A) (x : A) (outD : QueueA A) : Tick (T (QueueA A) * T A) :=
  Tick.tick >>
    match outD, q with
    | DeepA (Thunk (FOneA xD)) (Thunk NilA) (Thunk RZeroA), Nil =>
        Tick.ret (Thunk NilA, xD)
    | DeepA fD qD (Thunk (ROneA xD)), Deep f q RZero =>
        Tick.ret (Thunk (DeepA fD qD (Thunk RZeroA)), xD)
    | DeepA fD qD (Thunk RZeroA), Deep f q (ROne y) =>
        let+ (qD, pD) := thunkD (pushD q (y, x)) qD in
        let (yD, xD) := factorPairD pD
        in Tick.ret (Thunk (DeepA fD qD (Thunk (ROneA yD))), xD)
    | _, _ => bottom
    end.

Lemma pushD_approx A `{LessDefined A} (q : Queue A) (x : A) (outD : QueueA A) :
  outD `is_approx` push q x -> Tick.val (pushD q x outD) `is_approx` (q, x).
Admitted.

Fixpoint pop A (q : Queue A) : option (A * Queue A) :=
  match q with
  | Nil => None
  | Deep (FTwo x y) q r => Some (x, Deep (FOne y) q r)
  | Deep (FOne x) q r => let q' := match r with
                                   | RZero => Nil
                                   | ROne y => Deep (FOne y) Nil RZero
                                   end
                         in let q'' := match pop q with
                                       | Some ((y, z), q) => Deep (FTwo y z) q r
                                       | None => q'
                                       end
                            in Some (x, q'')
  end.

Fixpoint popD A (q : Queue A) (outD : option (T A * T (QueueA A))) :
  Tick (T (QueueA A)) :=
  Tick.tick >>
    match outD, q with
    | None, Nil =>
        Tick.ret (Thunk NilA)
    | Some (xA, Thunk (DeepA (Thunk (FOneA yA)) qA rA)), Deep (FTwo _ _) _ _ =>
        Tick.ret (Thunk (DeepA (Thunk (FTwoA xA yA)) qA rA))
    | Some (xD, Thunk NilA), Deep (FOne _) q _ =>
        (* `pop q` is `None`, `r` is `RZero` *)
        Tick.ret (Thunk (DeepA (Thunk (FOneA xD)) (Thunk NilA) (Thunk RZeroA)))
    | Some (xD, Thunk (DeepA (Thunk (FOneA yD)) (Thunk NilA) (Thunk RZeroA))), Deep (FOne _) q _ =>
        (* `pop q` is `None`, `r` is `ROne y` *)
        Tick.ret (Thunk (DeepA (Thunk (FOneA xD)) (Thunk NilA) (Thunk (ROneA yD))))
    | Some (xD, Thunk (DeepA (Thunk (FTwoA yD zD)) qD rD)), Deep (FOne _) q _ =>
        (* `pop q` is `Some ((y, z), q)` *)
        let+ qD := popD q (Some (unfactorPairD yD zD, qD)) in
        Tick.ret (Thunk (DeepA (Thunk (FOneA xD)) qD rD))
    | _, _ => bottom
    end.

Lemma popD_approx A `{LessDefined A} (q : Queue A) (outD : option (T A * T (QueueA A))) :
  outD `is_approx` pop q -> Tick.val (popD q outD) `is_approx` q.
Admitted.
