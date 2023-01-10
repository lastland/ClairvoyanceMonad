Set Implicit Arguments.
Set Maximal Implicit Insertion.
Set Contextual Implicit.

From Coq Require Import Arith List Psatz Morphisms Relations.
From Equations Require Import Equations.
From Clairvoyance Require Import Core Approx.

(* ---------------------- Section 2: Motivating Example ---------------------- *)

(** * Figure 1. *)

Fixpoint append {a} (xs ys : list a) : list a :=
  match xs with
  | nil => ys
  | cons x xs1 => let zs := append xs1 ys in x :: zs
  end.

(* returns the prefix of xs of length n or xs when n > length xs. *)
Fixpoint take {a} (n : nat) (xs : list a) : list a :=
  match n, xs with
  | O, _ => nil
  | S _, nil => nil
  | S n1, x :: xs1 => let zs := take n1 xs1 in x :: zs
  end.

Definition p {a} (n : nat) (xs ys : list a) : list a :=
  let zs := append xs ys in
  take n zs.

Fixpoint drop {a} (n : nat) (xs : list a) : list a :=
  match n, xs with
  | O, _ => xs
  | S _, nil => nil
  | S n1, x :: xs1 => drop n1 xs1
  end.

(* ---------------------- Section 4: Translation ---------------------- *)

(* Definitions needed for the by-hand translation of the examples from Section 2 *)

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


Section TranslationExample.

(** * Figure 9.

    Definition of the [foldrA] function used in the translation of [foldr]. *)
Fixpoint foldrA' {a b} (n : M b) (c : T a -> T b -> M b) (x' : listA a) : M b :=
  tick >>
  match x' with
  | NilA => n
  | ConsA x1 x2 =>
    let~ y2 := foldrA' n c $! x2 in
    c x1 y2
  end.

Definition foldrA {a b} (n : M b) (c : T a -> T b -> M b) (x : T (listA a)) : M b :=
  foldrA' n c $! x.

(** * Figure 11.

    The translated code of append and take from the pure version of Fig. 1. *)
Fixpoint append_ {a : Type} (xs' : listA a) (ys : T (listA a)) : M (listA a) :=
  tick >>
  match xs' with
  | NilA => force ys
  | ConsA x xs1 =>
    let~ t := (fun xs1' => append_ xs1' ys) $! xs1 in
    ret (ConsA x t)
  end.

Definition appendA {a : Type} (xs ys : T (listA a)) : M (listA a) :=
  (fun xs' => append_ xs' ys) $! xs.

Fixpoint take_ {a : Type} (n : nat) (xs' : listA a) : M (listA a) :=
  tick >>
  match n, xs' with
  | O, _ => ret NilA
  | S _, NilA => ret NilA
  | S n1, ConsA x xs1 =>
    let~ t := take_ n1 $! xs1 in
    ret (ConsA x t)
  end.

Definition takeA {a : Type} (n : nat) (xs : T (listA a)) : M (listA a) :=
  take_ n $! xs.

Definition pA {a} (n : nat) (xs ys : T (listA a)) : M (listA a) :=
  tick >>
  let~ t := appendA xs ys in
  takeA n t.

End TranslationExample.

(* ----------------- Section 5.3 ----------------- *)

(** * Figure 16.

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

(* ----------------- Section 5.4 ----------------- *)

(** * Figure 15.

    The partial functional correctness and pure functional correctness theorems
    and their proofs. *)
Theorem appendA_correct_partial {a} :
  forall (xs ys : list a) (xsA ysA : T (listA a)),
    xsA `is_approx` xs -> ysA `is_approx` ys ->
    (appendA xsA ysA) {{ fun zsA _ => zsA `is_approx` append xs ys }}.
Proof.
  destruct xsA; [| mgo_list].
  intros ysA Hxs. revert ys ysA.
  funelim (exact_listA xs); mgo_list.
  relax_apply H0; try eassumption; mgo_list.
Qed.

Theorem appendA_correct_pure {a} :
  forall (xs ys : list a) (xsA ysA : T (listA a)),
    xsA = exact xs -> ysA = exact ys ->
    (appendA xsA ysA) [[ fun zsA _ => zsA = exact (append xs ys) ]].
Proof.
  destruct xsA; [|mgo_list].
  intros ysA Hxs. revert ys ysA.
  funelim (exact_listA xs); mgo_list.
  apply optimistic_thunk_go.
  relax_apply H0; try eassumption; try reflexivity.
  mgo_list.
Qed.

(* ----------------- Section 5.5 ----------------- *)

(** The pessimistic specification for the cost of [appendA]. *)
Theorem appendA_cost_interval {a} : forall (xsA ysA : T (listA a)),
    (appendA xsA ysA)
    {{ fun zsA cost => 1 <= cost <= sizeX 1 xsA }}.
Proof.
  destruct xsA; [|mgo_list].
  induction x; mgo_list.
  relax_apply IHx. mgo_list.
Qed.

(** The pessimistic specification for the cost + functional correctness of
    [appendA] can be obtained using the conjunction rule. *)
Theorem appendA_spec {a} :
  forall (xs ys : list a) (xsA ysA : T (listA a)),
    xsA `is_approx` xs ->
    ysA `is_approx` ys ->
    (appendA xsA ysA) {{ fun zsA cost => zsA `is_approx` append xs ys /\ 1 <= cost <= sizeX 1 xsA }}.
Proof.
  intros. apply pessimistic_conj.
  - apply appendA_correct_partial; assumption.
  - apply appendA_cost_interval.
Qed.


Theorem appendA_whnf_cost {a} : forall (xsA ysA : T (listA a)),
    (appendA xsA ysA)
    [[ fun zsA cost => cost <= 1 ]].
Proof.
(** This is a naive version of spec in the paper and it is in fact not provable
    because it's wrong (when [xsA] is undefined). The specs we actually use are
    [appendA_prefix_cost] and [appendA_full_cost].  *)
Abort.

(** [appendA_prefix_cost] as described in the paper. This is the case when the
    execution of [appendA] does not reach the end of [xsA]. *)
Theorem appendA_prefix_cost {a} : forall n (xsA ysA : T (listA a)),
    1 <= n <= sizeX 0 xsA ->
    (appendA xsA ysA) [[ fun zsA cost => n = sizeX 0 (Thunk zsA) /\ cost <= n ]].
Proof.
  destruct xsA; [| cbn; intros; lia].
  generalize dependent n.
  induction x; mgo_list.
  - apply optimistic_skip. mgo_list.
  - destruct (dec_eq_nat n 1).
    + apply optimistic_skip; mgo_list.
    + apply optimistic_thunk_go.
      relax. apply IHx with (n:=n-1); lia.
      mgo_list.
Qed.

(** [appendA_full_cost] as described in the paper. This is the case when the
    execution of [appendA] does reach the end of [xsA]. *)
Theorem appendA_full_cost {a} : forall (xs : list a) (xsA := exact xs) ysA,
    is_defined ysA ->
    (appendA xsA ysA) [[ fun zsA cost =>
      length xs + sizeX 1 ysA = sizeX 1 (Thunk zsA) /\ cost <= length xs + 1 ]].
Proof.
  induction xs; mgo_list.
  apply optimistic_thunk_go.
  relax_apply IHxs; mgo_list.
Qed.

(* ----------------------------- Section 6: Tail Recursion ------------------- *)

(** * Tail recursive [take].

    The first case study shown in Section 6. *)
Module TakeCompare.

(** The original [take'_] and [take'] functions shown in the paper.  *)
Fixpoint take'_ {a} (n : nat) (xs : list a) (acc : list a) : list a :=
match n with
| O => rev acc
| S n' => match xs with
          | nil => rev acc
          | cons x xs' => take'_ n' xs' (x :: acc)
          end
end.

Definition take' {a} (n : nat) (xs : list a) : list a := take'_ n xs nil.

(** From here, we study the approximations of [take] and [take']. *)

(** Before studying [takeA]s, we first define the [revA] function that is used
    by [take'A]. Note that we did not insert any [tick]s in this definition. As
    discussed by the paper, this is because we would like to assign a cost of 0
    to [revA]. One way of doing that is axiomatizing the cost---but introducing
    axioms can be dangerous if we don't do it correctly. This is a safer
    alternative that ensures we don't introduce any potential unsoundness. *)
Fixpoint revA_ {a : Type} (xs' : listA a) (ys : T (listA a)) : M (listA a) :=
  match xs' with
  | NilA => force ys
  | ConsA x xs1 =>
    let~ ys1 := ret (ConsA x ys) in
    (fun xs1' => revA_ xs1' ys1) $! xs1
  end.

Definition revA {a : Type} (xs : T (listA a)) : M (listA a) :=
  let~ ys := ret NilA in
  (fun xs' => revA_ xs' ys) $! xs.

Lemma revA_cost : forall {a} (xsA : T (listA a)),
    (revA xsA) {{ fun _ cost => cost = 0 }}.
Proof.
  unfold revA. destruct xsA; [|mgo_list].
  assert (forall y, revA_ x y {{fun (_ : listA a) (m : nat) => m = 0}}).
  { induction x; mgo_list. }
  mgo_list.
Qed.

(** This is the approximation of [take'_]. *)
Fixpoint take'A_ {a : Type} (n : nat) (xs : listA a) (acc : T (listA a)) : M (listA a) :=
  tick >> (match n with
        | O => revA acc
        | S n' => match xs with
                 | NilA => revA acc
                 | ConsA x xs' =>
                   (fun xs'' =>
                      let~ acc' := ret (ConsA x acc) in
                      take'A_ n' xs'' acc') $! xs'
                 end
           end).

(** This is the approximation of [take']. *)
Definition take'A {a : Type} (n : nat) (xs : T (listA a)) : M (listA a) :=
  forcing xs (fun xs' => take'A_ n xs' (Thunk NilA)).

(** The pessimistic specification for [take'A] and the proof that [take'A]
    satisfies the spec, as stated in the paper. *)
Theorem take'A__pessim {a} :
forall (n : nat) (xs : list a) (xsA : listA a) (acc : list a) (accA : T (listA a)),
  xsA `is_approx` xs ->  accA `is_approx` acc ->
  (take'A_ n xsA accA) {{ fun zsA cost => cost = min n (length xs) + 1 }}.
Proof.
  induction n as [ | n IHn].
  - mgo_list. relax_apply @revA_cost. cbn; intros. lia.
  - intros xs. destruct xs as [ | x xs ]; mgo_list.
    + relax_apply @revA_cost. cbn; intros; lia.
    + relax.
      { eapply IHn with (acc:=x :: acc); try eassumption.
        constructor. rewrite exact_list_unfold_cons.
        solve_approx. }
      { cbn; intros. lia. }
    + relax.
      eapply IHn with (acc:=x :: acc); try eassumption. constructor.
      cbn; intros. lia.
Qed.

(** The pessimistic specification for [takeA] and the proof that [takeA]
    satisfies the spec, as stated in the paper. *)
Definition takeA__pessim {a} :
forall (n : nat) (xs : list a) (xsA : T (listA a)),
  xsA `is_approx` xs ->
  (takeA n xsA) {{ fun zsA cost => zsA `is_approx` take n xs /\ 1 <= cost /\ cost <= min n (sizeX 0 xsA) + 1 }}.
Proof.
  (** The proof can be simpler. *)
  unfold takeA. induction n; [mgo_list|].
  - intuition; solve_approx.
  - intros xs. induction xs as [ | x xs IH]; mgo_list.
    + intuition; solve_approx.
    + specialize (IHn xs (Thunk x0)). cbn in IHn.
      relax_apply IHn; [ solve_approx | ].
      mgo_list. intuition; solve_approx.
    + intuition; solve_approx.
Qed.

Definition takeA_cost_interval {a} :
forall (n : nat) (xsA : T (listA a)),
  (takeA n xsA) {{ fun zsA cost => cost <= min n (sizeX 0 xsA) + 1 }}.
Proof.
  unfold takeA. induction n; [mgo_list|].
  destruct xsA; [|mgo_list].
  induction x; mgo_list.
  specialize (IHn (Thunk x)). cbn in IHn.
  relax_apply IHn. mgo_list.
Qed.

(** The optimistic specification for [takeA] and the proof that [takeA]
    satisfies the spec, as stated in the paper. This shows that there _exists_ a
    cost of [takeA] that is indeed smaller. *)
Definition takeA__optim {a} :
forall (n m : nat) (xs : list a) (xsA : T (listA a)),
  1 <= m ->  m <= min (n + 1) (sizeX 1 xsA) ->
  xsA `is_approx` xs ->
  (takeA n xsA) [[ fun zsA cost => cost = m ]].
Proof.
  destruct xsA; [| cbn; intros; lia].
  revert m xs x. induction n.
  - mgo_list. destruct (sizeX' 1 x); lia.
  - mgo_list. funelim (exact_listA xs); mgo_list.
    destruct (dec_eq_nat m 1); subst.
    + apply optimistic_skip. mgo_list.
    + apply optimistic_thunk_go.
      inversion H7; subst; [lia|].
      cbn. relax. eapply IHn with (m:=m-1); try lia; try eassumption.
      mgo_list.
Qed.

End TakeCompare.

(** * List reversal. *)

Module RevCompare.

(** [rev'], as shown in the paper. *)
Definition rev' {a} (xs : list a) : list a :=
  match xs with
  | nil => nil
  | x :: xs' => append (rev' xs') (cons x nil)
  end.

(** Another version of [appendA] that does not cost time. We can also axiomatize
    this but this version makes sure we don't introduce inconsistency. We use
    the same technique as the one we used with [revA] in the [TakeCompare]
    module. Find out more in the comments there. *)
Fixpoint appendA'_ {a : Type} (xs' : listA a) (ys : T (listA a)) : M (listA a) :=
  match xs' with
  | NilA => force ys
  | ConsA x xs1 =>
    let~ t := (fun xs1' => appendA'_ xs1' ys) $! xs1 in
    ret (ConsA x t)
  end.

Definition appendA' {a : Type} (xs ys : T (listA a)) : M (listA a) :=
  (fun xs' => appendA'_ xs' ys) $! xs.

Lemma appendA'_cost {a} : forall (xsA ysA : T (listA a)),
    (appendA' xsA ysA) {{ fun _ cost => cost = 0 }}.
Proof.
  destruct xsA; [|mgo_list].
  induction x; mgo_list.
  relax_apply IHx. mgo_list.
Qed.

(** The approximations of [rev_] and [rev]. *)

Fixpoint revA_ {a : Type} (xs' : listA a) (ys : T (listA a)) : M (listA a) :=
  tick >>
  match xs' with
  | NilA => force ys
  | ConsA x xs1 =>
    let~ ys1 := ret (ConsA x ys) in
    (fun xs1' => revA_ xs1' ys1) $! xs1
  end.

Definition revA {a : Type} (xs : T (listA a)) : M (listA a) :=
  let~ ys := ret NilA in
  (fun xs' => revA_ xs' ys) $! xs.

(** The approximations of [rev']. *)

Fixpoint rev'A_ {a : Type} (xs : listA a) : M (listA a) :=
  tick >>
  match xs with
  | NilA => ret NilA
  | ConsA x xs' => let~ t1 := rev'A_ $! xs' in
                  let t2 := Thunk (ConsA x (Thunk NilA)) in
                  appendA' t1 t2
  end.

Definition rev'A {a} (xs : T (listA a)) : M (listA a) := rev'A_ $! xs.

(** The pessimistic specification about [revA]. *)

Lemma revA_pessim_ {a} :
forall (xs : list a) (xsA : listA a) (ysA : T (listA a)),
  xsA `is_approx` xs ->
  (revA_ xsA ysA) {{ fun zsA cost => cost = length xs + 1 }}.
Proof.
  intros. funelim (exact_listA xs); mgo_list.
  - relax_apply H0. assumption.
    cbn. intros. lia.
  - relax_apply H0. assumption.
    cbn. intros. lia.
Qed.

Theorem revA_pessim {a} :
forall (xs : list a) (xsA : T (listA a)),
  xsA `is_approx` xs ->
  (revA xsA) {{ fun zsA cost => cost = length xs + 1 }}.
Proof.
  unfold revA. destruct xsA; [|mgo_list].
  mgo_list; apply revA_pessim_; assumption.
Qed.

(** The pessimistic specification about [rev'A]. *)

Lemma rev'A_pessim_ {a} :
forall (xs : list a) (xsA : listA a),
  xsA `is_approx` xs ->
  (rev'A_ xsA) {{ fun zsA cost => cost = length xs + 1 }}.
Proof.
  intros. funelim (exact_listA xs); mgo_list.
  relax_apply H0. assumption.
  mgo_list. pose (appendA'_cost (Thunk x1)) as Ha. cbn in Ha.
  relax_apply Ha. cbn; intros; subst. lia.
Qed.

Theorem rev'A_pessim {a} :
forall (xs : list a) (xsA : T (listA a)),
  xsA `is_approx` xs ->
  (rev'A xsA) {{ fun zsA cost => cost = length xs + 1 }}.
Proof.
  unfold rev'A. destruct xsA; [|mgo_list].
  cbn. intros. apply rev'A_pessim_.
  inversion H; subst; assumption.
Qed.

End RevCompare.

(** * Left and right folds. *)

Module CaseStudyFolds.

(** The definitions of [foldl] and [foldr]. *)

Fixpoint foldl {a b} (f : b -> a -> b) (v : b) (xs : list a) : b :=
  match xs with
  | nil => v
  | cons x xs => foldl f (f v x) xs
  end.

Fixpoint foldr {a b} (v : b) (f : a -> b -> b)  (xs : list a) : b :=
  match xs with
  | nil => v
  | cons x xs => f x (foldr v f xs)
  end.

(** The approximations of [foldl] and [foldr]. *)

Fixpoint foldlA_ {a b} (f : T b -> T a -> M b) (v : T b) (xs : listA a) : M b :=
  tick >>
  match xs with
  | NilA => force v
  | ConsA x xs => let~ t := f v x in
                  foldlA_ f t $! xs
  end.

Definition foldlA {a b} (f : T b -> T a -> M b) (v : T b) (xs : T (listA a)) : M b :=
  foldlA_ f v $! xs.

Fixpoint foldrA_ {a b} (f : T a -> T b -> M b) (v : T b) (xs : listA a) : M b :=
  tick >>
  match xs with
  | NilA => force v
  | ConsA x xs => let~ t := foldrA_ f v $! xs in
                 f x t
  end.

Definition foldrA {a b} (f : T a -> T b -> M b) (v : T b) (xs : T (listA a)) : M b :=
  foldrA_ f v $! xs.

Definition foldl_pessim {a b bA} `{LessDefined bA} `{Exact b bA} :
(** The pessimistic specification of [foldlA]. *)
forall f (xs : list a) (xsA : T (listA a)) (v : b) (vA : T bA),
  (forall x y, (f x y) {{ fun bA cost => exists b, bA `is_approx` b /\ cost = 1 }}) ->
  xsA `is_approx` xs ->  vA `is_approx` v ->
  (foldlA f vA xsA)
    {{ fun zsA cost => cost >= length xs + 1 /\ cost <= 2 * length xs + 1 }}.
Proof.
  intros f xs xsA v vA Hf Hxs. revert v vA.
  unfold foldlA. funelim (exact_listA xs); mgo_list.
  - relax_apply Hf. cbn; intros.
    destruct H3 as (? & ? & ?); subst.
    relax. eapply H0 with (v:=x1); try eassumption.
    constructor; assumption.
    cbn. intros. lia.
  - specialize (H0 _ _ _ _ f (Thunk x)).
    cbn in H0. relax; [ apply H0 with (v:=v); auto; solve_approx | ].
    cbn; lia.
Qed.

Definition foldr_pessim {a b bA} `{LessDefined bA} `{LessDefined (T bA)} `{Exact b bA} :
(** The pessimistic specification of [foldrA]. *)
forall f (xs : list a) (xsA : T (listA a)) (v : b) (vA : T bA),
  (forall x y, (f x y) {{ fun bA cost => cost = 1 }}) ->
  xsA `is_approx` xs ->  vA `is_approx` v ->
  (foldrA f vA xsA)
    {{ fun zsA cost => cost >= 1 /\ cost <= 2 * sizeX 0 xsA + 1 }}.
Proof.
  intros f xs xsA v vA Hf Hxs. revert v vA.
  unfold foldrA. funelim (exact_listA xs); mgo_list.
  - specialize (H0 _ _ _ _ _ f (Thunk x)).
    relax; [ eapply H0; auto; solve_approx | ].
    mgo_list. relax_apply Hf. mgo_list.
  - relax_apply Hf. cbn. intros. subst.
    destruct xs; simpl; lia.
Qed.

Definition foldr_optim1 {a b bA} `{LessDefined bA} `{LessDefined (T bA)} `{Exact b bA} :
forall f (xs : list a) (xsA : T (listA a)) (v : b) (vA : T bA) n,
  1 <= n -> n < sizeX 0 xsA ->
  xsA `is_approx` xs ->  vA `is_approx` v ->
  (forall x y, (f x y) [[ fun bA cost => cost = 1 ]]) ->
  (foldrA f vA xsA) [[ fun zsA cost => cost = 2 * n ]].
Proof.
  destruct xsA; [| cbn; intros; lia]. cbn.
  revert x. induction xs; mgo_list.
  destruct (dec_eq_nat n 1); subst.
  - apply optimistic_skip. relax. eapply H6.
    cbn. intros. lia.
  - apply optimistic_thunk_go.
    destruct xs0; [|lia].
    relax. eapply IHxs with (n:=n-1); try eassumption; try lia.
    cbn; intros. relax_apply H6. cbn; intros. lia.
Qed.

Definition foldr_optim2 {a b bA} `{LessDefined bA} `{LessDefined (T bA)} `{Exact b bA}:
(** And a special cost exists when [xs] is fully evaluated. *)
forall f (xs : list a) (xsA : T (listA a)) (v : b) (vA : T bA),
  xsA = exact xs ->  vA `is_approx` v -> is_defined vA ->
  (forall x y, (f x y) [[ fun bA cost => cost = 1 ]]) ->
  (foldrA f vA xsA) [[ fun zsA cost => cost = 2 * length xs + 1 ]].
Proof.
  induction xs; mgo_list.
  apply optimistic_thunk_go.
  specialize (IHxs (Thunk (exact_listA xs)) v (Thunk x)).
  cbn in IHxs. relax_apply IHxs; auto.
  cbn. intros; subst. relax_apply H5. cbn; intros. lia.
Qed.

End CaseStudyFolds.

Section ExampleP.

Variable a : Type.

Theorem pA_pessim :
  forall n (xs ys : list a) (xsA ysA : T (listA a)),
    xsA `is_approx` xs ->
    ysA `is_approx` ys ->
    pA n xsA ysA {{ fun zsA cost =>
                      zsA `is_approx` exact (p n xs ys) /\
                      1 <= cost /\ cost <= sizeX 1 xsA + min n (length (append xs ys)) + 2}}.
Proof.
  destruct xsA; unfold pA; [|mgo_list].
  Opaque appendA. Opaque takeA.
  mgo_list.
  - relax_apply (@appendA_spec a); solve_approx. mgo_list.
    destruct H as [Happrox Hcost].
    relax_apply (@TakeCompare.takeA__pessim a n (append xs ys)); solve_approx.
    cbn; intros. unfold p. intuition.
    pose proof (@sizeX'_length a (append xs ys) x0 Happrox).
    lia.
  - Transparent takeA. mgo_list.
Qed.

End ExampleP.

(* Partial function: we assume that both arguments approximate the same list *)
Fixpoint lub_listA {a} (xs ys : listA a) : listA a :=
  match xs, ys with
  | NilA, NilA => NilA
  | ConsA x xs, ConsA y ys => ConsA (lub_T (fun r _ => r) x y) (lub_T lub_listA xs ys)
  | _, _ => NilA  (* silly case *)
  end.

#[global] Instance Lub_listA {a} : Lub (listA a) := lub_listA.

#[global] Instance LubLaw_listA {a} : LubLaw (listA a).
Proof.
  constructor.
  - intros x y z Hx; revert y; induction Hx; intros ?; inversion 1; subst; cbn; constructor; auto.
    1: inversion H; subst; inversion H4; subst; try constructor; auto.
    1: inversion H; subst; inversion H5; subst; try constructor; auto.
    inversion H6; constructor; auto.
  - intros x y [z [ Hx Hy] ]; revert y Hy; induction Hx; intros ?; inversion 1; subst; cbn;
      constructor; auto.
    1: inversion H; inversion H3; constructor; reflexivity + auto.
    1: inversion H; inversion H4; constructor; reflexivity.
    inversion H5; subst; constructor; [ reflexivity | auto ].
  - intros x y [z [Hx Hy] ]; revert x Hx; induction Hy; intros ?; inversion 1; subst; cbn;
      constructor; auto.
    1: inversion H; inversion H3; subst; invert_approx; constructor; reflexivity + auto; inversion H7; invert_approx; reflexivity.
    1: inversion H; inversion H4; subst; invert_approx; constructor; reflexivity + auto; inversion H8; invert_approx; reflexivity.
    inversion H5; subst; constructor; [ reflexivity | auto ].
Qed.
