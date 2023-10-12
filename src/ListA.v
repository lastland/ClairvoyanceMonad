Set Implicit Arguments.
Set Maximal Implicit Insertion.
Set Contextual Implicit.

From Coq Require Import Arith List Psatz Morphisms Relations SetoidClass.
From Equations Require Import Equations.
From Clairvoyance Require Import Core Approx ApproxM Tick Misc.

Unset Elimination Schemes.

(* The [listA] type discussed in Fig. 7 in Section 4. *)
Inductive listA (a : Type) : Type :=
  NilA | ConsA (x1 : T a) (x2 : T (listA a)).

(* For [listA], we need to define our own induction principle because Coq cannot
   generate the correct induction principles for nested inductive datatypes.

   See the [Nested Inductive Types] section in CPDT
   (http://adam.chlipala.net/cpdt/html/Cpdt.InductiveTypes.html). *)
Lemma listA_ind : forall (a : Type) (P : listA a -> Prop),
    P NilA ->
    (forall (x1 : T a),
        P (ConsA x1 Undefined)) ->
    (forall (x1 : T a) (x2 : listA a),
        P x2 ->
        P (ConsA x1 (Thunk x2))) ->
    forall l : listA a, P l.
Proof.
  intros a P Hnil Hundef Hthunk. fix SELF 1. intros. destruct l.
  - apply Hnil.
  - destruct x2.
    + apply Hthunk. apply SELF.
    + apply Hundef.
Defined.

Set Elimination Schemes.

(** * Size that doesn't count the list element

    As pointed out by the footnote of the figure, [T (listA A)] is not a
    recursive type, so we need to define a separate helper function [sizeX']
    that recurses on [listA]. *)
Fixpoint sizeX' {a} (n0 : nat) (xs : listA a) : nat :=
  match xs with
  | NilA => n0
  | ConsA _ Undefined => 1
  | ConsA _ (Thunk xs1') => S (sizeX' n0 xs1')
  end.

Definition sizeX {a} (n0 : nat) (xs : T (listA a)) : nat :=
  match xs with
  | Thunk xs' => sizeX' n0 xs'
  | Undefined => 0
  end.


Fixpoint sizeAX' {a} (f: T a -> nat) (n0 : nat) (xs : listA a) : nat :=
  match xs with
  | NilA => n0
  | ConsA _ Undefined => 1
  | ConsA a (Thunk xs1') => f a + S (sizeAX' f n0 xs1')
  end.

Definition sizeAX {a} (f: T a -> nat) (n0 : nat) (xs : T (listA a)) : nat :=
  match xs with
  | Thunk xs' => sizeAX' f n0 xs'
  | Undefined => 0
  end.


(* Some useful lemmas. *)
Lemma sizeX'_ge_1 {a} : forall (xs : listA a),
    1 <= sizeX' 1 xs.
Proof.
  induction xs; cbn; intros; lia.
Qed.

#[global] Hint Resolve sizeX'_ge_1 : core.

Lemma sizeX_ge_1 {a} : forall (xs : listA a),
    1 <= sizeX 1 (Thunk xs).
Proof.
  simpl; auto.
Qed.

#[global] Hint Resolve sizeX_ge_1 : core.


(** The function is defined with the help of the Equations library. Neither our
    methodology nor our definitions have to rely on Equations, but the tactics
    provided by Equations such as [funelim] makes our proofs slightly
    simpler. *)
Equations exact_listA {a b : Type} `{Exact a b} (xs : list a) : listA b :=
exact_listA nil := NilA ;
exact_listA (cons y ys) := ConsA (Thunk (exact y)) (Thunk (exact_listA ys)).

#[global]
Instance Exact_list {a b} `{Exact a b} : Exact (list a) (listA b) :=
  exact_listA.

Lemma exact_list_unfold_nil {a b} `{Exact a b}
  : exact (@nil a) = (@NilA b).
Proof.
  unfold exact; simp exact_listA; reflexivity.
Qed.

Lemma exact_list_unfold_cons {a b} `{Exact a b} (x : a) (xs : list a)
  : exact (x :: xs) = ConsA (exact x) (exact xs).
Proof.
  unfold exact; simp exact_listA; reflexivity.
Qed.

Lemma exact_list_unfold_nil_T {a b} `{Exact a b}
  : exact (@nil a) = Thunk (@NilA b).
Proof.
  unfold exact; simp exact_listA; reflexivity.
Qed.

Lemma exact_list_unfold_cons_T {a b} `{Exact a b} (x : a) (xs : list a)
  : exact (x :: xs) = Thunk (ConsA (exact x) (exact xs)).
Proof.
  unfold exact; simp exact_listA; reflexivity.
Qed.

Global
Hint Rewrite @exact_list_unfold_nil @exact_list_unfold_cons
  @exact_list_unfold_nil_T @exact_list_unfold_cons_T : exact.


(* --------------------------------------------------------------- *)

Unset Elimination Schemes.

Inductive LessDefined_list {a : Type} `{LessDefined a} : LessDefined (listA a) :=
| less_defined_list_NilA : NilA `less_defined` NilA
| less_defined_list_ConsA : forall (x y : T a) (xs ys : T (listA a)),
    x `less_defined` y ->
    xs `less_defined` ys ->
    ConsA x xs `less_defined` ConsA y ys.

#[global] Hint Constructors LessDefined_list : core.
#[global] Existing Instance LessDefined_list.

(** We need our own induction principle because of nested inductive types. *)
Lemma LessDefined_list_ind :
  forall (a : Type) (H : LessDefined a) (P : listA a -> listA a -> Prop),
    P NilA NilA ->
    (forall (x y : T a) (ys : T (listA a)),
        x `less_defined` y ->
        P (ConsA x Undefined) (ConsA y ys)) ->
    (forall (x y : T a) (xs ys : listA a),
        x `less_defined` y ->
        xs `less_defined` ys ->
        P xs ys ->
        P (ConsA x (Thunk xs)) (ConsA y (Thunk ys))) ->
    forall l l0 : listA a, LessDefined_list l l0 -> P l l0.
Proof.
  intros a H P Hnil Hundef Hthunk. fix SELF 3.
  intros l l' Hl. destruct Hl.
  - apply Hnil.
  - inversion H1; subst.
    + apply Hundef. assumption.
    + apply Hthunk; try assumption.
      apply SELF. assumption.
Defined.

Set Elimination Schemes.


#[global]
Instance PreOrder_LessDefined_list {a : Type} `{LessDefined a, Ho : !PreOrder (less_defined (a := a))} : PreOrder (A := listA a) less_defined.
Proof.
constructor.
- intros x. induction x.
  + constructor.
  + repeat constructor. reflexivity.
  + constructor. reflexivity. constructor. apply IHx.
- intros x y z Hxy. revert z. induction Hxy.
  + trivial.
  + inversion 1; subst. constructor; [|constructor].
    transitivity y; assumption.
  + inversion 1; subst. constructor.
    * transitivity y; assumption.
    * inversion H7; subst. auto.
Qed.

#[global]
Instance ExactMaximal_listA {a b} `{ExactMaximal a b} : ExactMaximal (listA a) (list b).
Proof.
  intros xA x. revert xA. induction x.
  - inversion 1. reflexivity.
  - unfold exact, Exact_list.
    rewrite exact_listA_equation_2.
    inversion 1; subst. f_equal.
    + inversion H3; subst. f_equal. apply exact_maximal, H2.
    + inversion H5; subst. f_equal.
      apply IHx. assumption.
Qed.

Ltac mgo_list := mgo ltac:(autorewrite with exact).

#[global] Hint Unfold id : core.

#[local] Existing Instance Exact_id | 1.
#[local] Existing Instance LessDefined_id | 100.
#[local] Existing Instance PreOrder_LessDefined_id | 100.
#[local] Existing Instance ExactMaximal_id | 100.

Lemma sizeX'_length {a} : forall (xs : list a) (xsA : listA a),
    xsA `is_approx` xs -> sizeX' 0 xsA <= length xs.
Proof.
  induction xs.
  - cbn. inversion 1; subst. cbn; lia.
  - cbn. inversion 1; subst. inversion H4; subst.
    + cbn. lia.
    + specialize (IHxs x0 H2). cbn.
      cbn in IHxs. lia.
Qed.

Lemma sizeX_length {a} : forall (xs : list a) (xsA : T (listA a)),
    xsA `is_approx` xs -> sizeX 0 xsA <= length xs.
Proof.
  destruct xsA.
  - cbn; intros. apply sizeX'_length.
    apply less_defined_Thunk_inv; assumption.
  - cbn; lia.
Qed.

(* Partial function: we assume that both arguments approximate the same list *)
Fixpoint lub_listA {a} {_ : Lub a} (xs ys : listA a) : listA a :=
  match xs, ys with
  | NilA, NilA => NilA
  | ConsA x xs, ConsA y ys => ConsA (lub x y) (lub_T lub_listA xs ys)
  | _, _ => NilA  (* silly case *)
  end.

#[global] Instance Lub_listA {a} `{Lub a} : Lub (listA a) := lub_listA.

#[global] Instance Reflexive_less_defined_listA {a} `{LessDefined a, !Reflexive (less_defined (a := a))}
  : Reflexive (less_defined (a := listA a)).
Proof.
  intros x; induction x; repeat constructor.
  - apply Reflexive_LessDefined_T.
  - apply Reflexive_LessDefined_T.
  - auto.
Qed.

#[global] Instance LubLaw_listA {a} `{LubLaw a, !Reflexive (less_defined (a := a))} : LubLaw (listA a).
Proof.
  constructor.
  - intros x y z Hx; revert y; induction Hx; intros ?; inversion 1; subst; cbn; constructor; auto.
    + inversion H3; apply lub_least_upper_bound; auto.
    + inversion H3; apply lub_least_upper_bound; auto.
    + inversion H9; constructor; auto.
  - intros x y [z [ Hx Hy] ]; revert y Hy; induction Hx; intros ?; inversion 1; subst; cbn;
      constructor; auto.
    + inversion Hy; subst. apply lub_upper_bound_l. econstructor; eauto.
    + inversion Hy; subst. apply lub_upper_bound_l. econstructor; eauto.
    + inversion Hy; subst. inversion H11; constructor; eauto. reflexivity.
  - intros x y [z [Hx Hy] ]; revert x Hx; induction Hy; intros ?; inversion 1; subst; cbn;
      constructor; auto.
    + inversion Hx; inversion H2; subst; invert_approx; [ constructor | ].
      inversion H6; subst; invert_approx; constructor; auto.
      apply lub_upper_bound_r; econstructor; eauto.
    + inversion Hx; inversion H2; subst; invert_approx; [ constructor | ].
      inversion H9; subst; invert_approx; constructor; auto.
      apply lub_upper_bound_r; econstructor; eauto.
    + inversion H8; subst; constructor; [ reflexivity | ]. auto.
Qed.

Lemma sizeX1_length {a} (x : T (listA a)) (y : list a)
  : x `is_approx` y -> sizeX 1 x <= 1 + length y.
Proof.
Admitted.

#[global] Instance BottomOf_listA {a : Type} {H : BottomOf a} : BottomOf (listA a) :=
  fun xs => match xs with NilA => NilA | ConsA x xs => ConsA Undefined Undefined end.

#[global] Instance BottomIsLeast_listA {a : Type} {H : BottomOf a} {H0 : LessDefined a}
  : BottomIsLeast a -> BottomIsLeast (listA a).
Proof.
  intros ? ? ? HH; inv HH; repeat constructor.
Qed.

(*
#[global] Instance IsAA_listA' {a' a} {_ : IsAA a' a} : IsAA (list a') (listA a).
Proof.
  econstructor; try typeclasses eauto.
Defined.
*)

#[global] Instance IsAA_listA {a' a} {_ : IsAA a' a} : IsAA (list a') (listA a).
Proof.
  econstructor; try typeclasses eauto.
Defined.

#[global] Instance Setoid_list {a} {_ : Setoid a} : Setoid (list a).
Admitted.

Parameter TODO : forall {P : Type}, P.

#[global] Instance IsAS_listA {a' a} {_ : Setoid a'} {_ : IsAA a' a} {_ : IsAS a' a}
  : IsAS (list a') (listA a).
Proof.
  constructor.
  - apply TODO.
  - apply TODO.
Qed.

Canonical AA_listA (a : AA) : AA :=
  {| carrier := list a
  ;  approx := listA (approx a)
  |}.
