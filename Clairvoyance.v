Set Implicit Arguments.
Set Maximal Implicit Insertion.
Set Contextual Implicit.

From Coq Require Import Arith List Psatz.
From Coq Require Import Relations.Relation_Definitions Classes.RelationClasses.

From Equations Require Import Equations.

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

(* ---------------------- Section 3: The Clairvoyance Monad ---------------------- *)

Section ClairvoyanceMonad.

(** * Figure 4. *)

(* A computation that produces a value of type "a" after some number of ticks. *)
Definition M (a : Type) : Type := a -> nat -> Prop.

(* A computation that takes no time and yields a single value. *)
Definition ret {a} (v : a) : M a :=
  fun y n => (y, n) = (v, 0).

(* Sequence two computations and add their time. *)
Definition bind {a b} (u : M a) (k : a -> M b) : M b :=
  fun y n => exists x nx ny, u x nx /\ k x y ny /\ n = nx + ny.

(* A computation with unit cost. *)
Definition tick : M unit :=
  fun _ n => n = 1.

(* A thunk: either a known value or unused. *)
Inductive T (a : Type) : Type :=
| Thunk (x : a)
| Undefined.

(* Store a computation without evaluating it (zero cost). *)
Definition thunk {a} (u : M a) : M (T a) :=
  fun t n => match t with
             | Thunk v => u v n
             | Undefined => n = 0
             end.

(* Either continue computation with the value of a thunk or fail. *) 
Definition forcing {a b} (t : T a) (f : a -> M b) : M b :=
  match t with
  | Thunk v => f v
  | Undefined => fun _ _ => False
  end.

(* Force a thunk. *)
Definition force {a} (t : T a) : M a := forcing t ret.

End ClairvoyanceMonad.

(* Notation for working with the Monad *)

Notation "t >> s" := (bind t (fun _ => s)) (at level 61, left associativity).

Notation "'let!' x' ':=' t 'in' s" := (bind t (fun x' => s)) (x' as pattern, at level 90).
Notation "'let~' x  ':=' t 'in' s" := (bind (thunk t) (fun x => s)) (x as pattern, at level 90).
Notation "f $! x" := (forcing x f) (at level 61, left associativity).

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

(* ---------------------- Section 5: Formal Reasoning ----------------- *)


(** * Figure 12.

    The definitions of the pessimistic and optimistic specifications *)

Definition pessimistic {a} (u : M a) (r : a -> nat -> Prop) : Prop :=
  forall x n, u x n -> r x n.

Definition optimistic {a} (u : M a) (r : a -> nat -> Prop) : Prop :=
  exists x n, u x n /\ r x n.

Notation " u {{ r }} " := (pessimistic u r) (at level 42).
Notation " u [[ r ]] " := (optimistic  u r) (at level 42).


(* ----------------- Section 5.2 ----------------- *)

(** Reasoning rules for pessimistic and optimistic specifications. *)

Section InferenceRules.

(** * Figure 13. *)

Lemma pessimistic_mon {a} (u : M a) (r r' : a -> nat -> Prop)
  : u {{ r }} ->
    (forall x n, r x n -> r' x n) ->
    u {{ r' }}.
Proof.
  intros X F x m H; apply F, X, H.
Qed.

Lemma pessimistic_ret {a} (x : a) (r : a -> nat -> Prop)
  : r x 0 -> (ret x) {{ r }}.
Proof.
  unfold ret. intros H y m. inversion 1. congruence.
Qed.

Lemma pessimistic_bind {a b} (u : M a) (k : a -> M b) (r : b -> nat -> Prop)
  : u {{ fun x n => (k x) {{ fun y m => r y (n + m) }} }} ->
    (bind u k) {{ r }}.
Proof.
  intros H y m0. intros (x & n & m & H1 & H2 & H3).
  specialize (H x _ H1 y _ H2). rewrite H3; apply H.
Qed.

Lemma pessimistic_tick (r : unit -> nat -> Prop)
  : r tt 1 -> tick {{ r }}.
Proof.
  intros H [] n. unfold tick. intros ->; auto.
Qed.

Lemma pessimistic_thunk a (u : M a) r
  : u {{ fun x => r (Thunk x) }} ->
    r Undefined 0 ->
    (thunk u) {{ r }}.
Proof.
  intros. intros x m. destruct x; simpl.
  - apply H.
  - intros ->. assumption.
Qed.

Lemma pessimistic_forcing {a b} (t : T a) (k : a -> M b) (r : b -> nat -> Prop)
  : (forall x, t = Thunk x -> (k x) {{ r }}) ->
    (k $! t) {{ r }}.
Proof.
  intros. destruct t eqn:Ht.
  - cbn. auto.
  - inversion 1.
Qed.

Lemma pessimistic_conj {a} (u : M a) (r p : a -> nat -> Prop)
  : u {{ r }} ->
    u {{ p }} ->
    u {{ fun x n => r x n /\ p x n }}.
Proof.
  intros ? ? ? ? Hu. split.
  - apply H; auto.
  - apply H0; auto.
Qed.

(** This rule is not in Fig. 13. Recall that [force t] is defined as [forcing t
    ret], so this rule can be simply obtained by using the [pessimistic_forcing]
    rule + the [pessimistic_ret] rule. *)
Lemma pessimistic_force {a} (t : T a) (r : a -> nat -> Prop)
  : (forall x, t = Thunk x -> r x 0) ->
    (force t) {{ r }}.
Proof.
  intros. eapply pessimistic_forcing.
  intros. eapply pessimistic_ret. auto.
Qed.

(** * Figure 14. *)

Lemma optimistic_mon {a} (u : M a) (r r' : a -> nat -> Prop)
  : u [[ r ]] ->
    (forall x n, r x n -> r' x n) ->
    u [[ r' ]].
Proof.
  intros X F. destruct X as (x & n & X).
  exists x, n. intuition.
Qed.

Lemma optimistic_ret {a} (x : a) (r : a -> nat -> Prop)
  : r x 0 -> (ret x) [[ r ]].
Proof.
  intros H. exists x, 0. intuition. constructor; reflexivity.
Qed.

Lemma optimistic_bind {a b} (u : M a) (k : a -> M b) (r : b -> nat -> Prop)
  : u [[ fun x n => (k x) [[ fun y m => r y (n + m) ]] ]] ->
    (bind u k) [[ r ]].
Proof.
  intros Hu. destruct Hu as (x & n & ? & Hk).
  destruct Hk as (y & m & ? & ?).
  exists y, (n + m). intuition.
  exists x, n, m. intuition.
Qed.

Lemma optimistic_tick (r : unit -> nat -> Prop)
  : r tt 1 -> tick [[ r ]].
Proof.
  intros H. exists tt, 1. intuition. constructor.
Qed.

(** For proof engineering purposes, we divide the [thunk] rule of Fig. 14 to two
    separate rules: [optimistic_thunk_go] and [optimistic_skip]. *)
Lemma optimistic_thunk_go {a} (u : M a) (r : T a -> nat -> Prop)
  : u [[ fun x => r (Thunk x) ]] ->
    (thunk u) [[ r ]].
Proof.
  intros (x & n & ? & ?).
  exists (Thunk x), n; cbn; auto.
Qed.

Lemma optimistic_skip {a} (u : M a) (r : T a -> nat -> Prop)
  : r Undefined 0 ->
    (thunk u) [[ r ]].
Proof.
  intros H.
  exists Undefined, 0. split; [|assumption]. cbn. reflexivity.
Qed.

Lemma optimistic_forcing {a b} (t : T a) (k : a -> M b) (r : b -> nat -> Prop) x
  : t = Thunk x ->
    k x [[ r ]] ->
    (k $! t) [[ r ]].
Proof.
  intros. destruct t eqn:Ht.
  - cbn. inversion H. auto.
  - congruence.
Qed.

Lemma optimistic_conj {a} (u : M a) (r p : a -> nat -> Prop)
  : u {{ r }} ->
    u [[ p ]] ->
    u [[ fun x n => r x n /\ p x n ]].
Proof.
  intros ? ?. destruct H0 as (? & ? & ? & ?).
  exists x, x0. auto.
Qed.

(** Same as [pessimistic_force], this is a consequence of [optimistic_forcing] +
    [optimistic_bind]. *)
Lemma optimistic_force {a} (t : T a) (r : a -> nat -> Prop) x
  : t = Thunk x ->
    r x 0 ->
    (force t) [[ r ]].
Proof.
  intros. unfold force. eapply optimistic_forcing.
  - eassumption.
  - eapply optimistic_ret; auto.
Qed.

End InferenceRules.

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

Definition is_defined {a} (t : T a) : Prop :=
  match t with
  | Thunk _ => True
  | Undefined => False
  end.

(* --------------------------------------- *)

(** * Approximations.
    
    This part is a reference implementation of the definitions discussed in
    Section 5.3.  *)

(** In the paper, we start by giving an [exact] function defined on lists. We
    mention later in the section that we would also want to be able to overload
    the [exact] function (and the [is_approx] and [less_defined] relations) for
    other types. One way of doing that is using type classes, as we show here. *)

(** * [exact] *)
Class Exact a b : Type := exact : a -> b.

#[global] Hint Unfold exact : core.

Instance Exact_T_Instance {a b} {r: Exact a b } : Exact a (T b) 
  := fun x => Thunk (exact x).

(** The function is defined with the help of the Equations library. Neither our
    methodology nor our definitions have to rely on Equations, but the tactics
    provided by Equations such as [funelim] makes our proofs slightly
    simpler. *)
Equations exact_listA {a b : Type} `{Exact a b} (xs : list a) : listA b :=
exact_listA nil := NilA ;
exact_listA (cons y ys) := ConsA (Thunk (exact y)) (Thunk (exact_listA ys)).

Instance Exact_list_Instance {a b} `{Exact a b} : Exact (list a) (listA b) :=
  exact_listA.

#[global] Hint Unfold Exact_T_Instance : core.
#[global] Hint Unfold Exact_list_Instance : core.

Instance Exact_fun {a1 b1 a2 b2} `{Exact b1 a1} `{Exact a2 b2} 
  : Exact (a1 -> a2) (b1 -> b2) 
  := fun f => fun x => exact (f (exact x)).

(** * [less_defined] *)
Class LessDefined a := less_defined : a -> a -> Prop.
Infix "`less_defined`" := less_defined (at level 42).

#[global] Hint Unfold less_defined : core.

Inductive LessDefined_T {a : Type} `{LessDefined a} : relation (T a) :=
| LessDefined_Undefined :
    forall x, LessDefined_T Undefined x
| LessDefined_Thunk :
    forall x y, x `less_defined` y -> LessDefined_T (Thunk x) (Thunk y).

#[global] Hint Constructors LessDefined_T : core.

Instance Lift_T {a} `{LessDefined a} : LessDefined (T a) := LessDefined_T.

#[global] Hint Unfold Lift_T : core.

(** * This corresponds to the proposition [less_defined_order] in Section 5.3. *)
Class LessDefinedOrder a (H: LessDefined a) :=
  { less_defined_preorder :> PreOrder less_defined ;
    less_defined_partial_order :> PartialOrder eq less_defined }.

(** * This corresponds to the proposition [exact_max] in Section 5.3. *)
Class LessDefinedExact {a b} {Hless : LessDefined a}
      (Horder : LessDefinedOrder Hless) (Hexact : Exact b a) :=
  { exact_max : forall (xA : a) (x : b), exact x `less_defined` xA -> exact x = xA }.

Instance PreOrder_Lift_T {a : Type} `{Ho : LessDefinedOrder a} : PreOrder Lift_T.
Proof.
constructor.
- intros x. destruct x.
  + constructor. apply Ho.
  + constructor.
- intros x y z. inversion 1; subst; intros.
  + constructor.
  + inversion H2; subst. constructor.
    destruct Ho. transitivity y0; assumption.
Qed.

Instance PartialOrder_Lift_T {a : Type} `{Ho : LessDefinedOrder a} : PartialOrder eq Lift_T.
Proof.
constructor.
- intros ->. autounfold. constructor; reflexivity.
- inversion 1. induction H1.
  + inversion H2; reflexivity.
  + inversion H2; subst. f_equal. apply Ho. constructor; assumption.
Qed.

Instance Lift_T_Order {a} {H: LessDefined a} {Ho : LessDefinedOrder H} : LessDefinedOrder Lift_T :=
  {| less_defined_preorder := PreOrder_Lift_T ;
     less_defined_partial_order := @PartialOrder_Lift_T _ H Ho |}.

Lemma exact_max_T {a b} {Hless : LessDefined a}
      (Horder : LessDefinedOrder Hless) (Hexact : Exact b a)
      (Hle : LessDefinedExact Horder Hexact) :
  forall (xA : T a) (x : b), exact x `less_defined` xA -> exact x = xA.
Proof.
  destruct xA; intros.
  - inversion H; subst. unfold exact, Exact_T_Instance.
    f_equal. apply Hle. assumption.
  - inversion H.
Qed.

Instance LessDefinedExact_T {a b} {Hless : LessDefined a} {Horder : LessDefinedOrder Hless}
         {Hexact : Exact b a} {_ : LessDefinedExact Horder Hexact}:
  LessDefinedExact Lift_T_Order Exact_T_Instance :=
  {| exact_max := @exact_max_T a b _ _ _ _ |}.

Unset Elimination Schemes.

Inductive LessDefined_list {a : Type} `{LessDefined a} : listA a -> listA a -> Prop :=
| LessDefined_NilA :
    LessDefined_list NilA NilA
| LessDefined_ConsA : forall (x y : T a) (xs ys : T (listA a)),
    x `less_defined` y ->
    @Lift_T _ LessDefined_list xs ys ->
    LessDefined_list (ConsA x xs) (ConsA y ys).

#[global] Hint Constructors LessDefined_list : core.

(** We need our own induction principle because of nested inductive types. *)
Lemma LessDefined_list_ind :
  forall (a : Type) (H : LessDefined a) (P : listA a -> listA a -> Prop),
    P NilA NilA ->
    (forall (x y : T a) (ys : T (listA a)),
        x `less_defined` y ->
        P (ConsA x Undefined) (ConsA y ys)) ->
    (forall (x y : T a) (xs ys : listA a),
        x `less_defined` y ->
        LessDefined_list xs ys ->
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

Instance Lift_list {a : Type} `{LessDefined a} : LessDefined (listA a) :=
  LessDefined_list.

#[global] Hint Unfold Lift_list : core.

Instance PreOrder_Lift_list {a : Type} `{Ho : LessDefinedOrder a} : PreOrder Lift_list.
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
    * inversion H6; subst. constructor. apply IHHxy. assumption.
Qed.

Instance PartialOrder_Lift_list  {a : Type} `{Ho : LessDefinedOrder a} : PartialOrder eq Lift_list.
Proof.
constructor.
- intros ->. autounfold. constructor; reflexivity.
- inversion 1. clear H0. induction H1.
  + reflexivity.
  + f_equal.
    * apply Lift_T_Order. constructor. assumption.
      inversion H2; subst. assumption.
    * inversion H2; subst. inversion H7; subst. reflexivity.
  + f_equal.
    * apply Lift_T_Order. constructor. assumption.
      inversion H2; subst. assumption.
    * f_equal. apply IHLessDefined_list.
      inversion H2; subst. inversion H8; subst. assumption.
Qed.

Instance Lift_list_Order {a : Type} `{Ho : LessDefinedOrder a} : LessDefinedOrder Lift_list :=
  {| less_defined_preorder := PreOrder_Lift_list ;
     less_defined_partial_order := @PartialOrder_Lift_list _ _ Ho |}.

Lemma exact_max_listA {a b} {Hless : LessDefined a}
      (Horder : LessDefinedOrder Hless) (Hexact : Exact b a)
      (Hle : LessDefinedExact Horder Hexact) :
  forall (xA : listA a) (x : list b), exact x `less_defined` xA -> exact x = xA.
Proof.
  intros xA x. revert xA. induction x.
  - inversion 1. reflexivity.
  - unfold exact, Exact_list_Instance.
    rewrite exact_listA_equation_2.
    inversion 1; subst. f_equal.
    + apply LessDefinedExact_T, H2.
    + inversion H4; subst. f_equal.
      apply IHx. assumption.
Qed.

Instance LessDefinedExact_list {a b} {Hless : LessDefined a} {Horder : LessDefinedOrder Hless}
         {Hexact : Exact b a} {_ : LessDefinedExact Horder Hexact}:
  LessDefinedExact Lift_list_Order Exact_list_Instance :=
  {| exact_max := @exact_max_listA a b _ _ _ _ |}.


Instance LessDefined_Fun {a b} {_ : LessDefined a} {_:LessDefined b} 
  : LessDefined (a -> b) :=
  fun f g => forall x y, x `less_defined` y -> f x `less_defined` g y.

(** * [is_approx]
    
    In our paper, the definition of [is_approx] can be anything as long as it
    satisfies the [approx_exact] proposition. In this file, we choose the most
    direct definition that satisfies the [approx_exact] law. *)
Definition is_approx {a b} { _ : Exact b a} {_:LessDefined a} (xA : a) (x : b) : Prop := 
  xA `less_defined` exact x.
Infix "`is_approx`" := is_approx (at level 42).

(** * This corresponds to the proposition [approx_exact] in Section 5.3.

    And because of our particular definition, this is true by
    definition. However, this cannot be proved generically if the definition of
    [is_approx] can be anything. *)
Theorem approx_exact {a b} `{Exact b a} `{LessDefined a} :
  forall (x : b) (xA : a),
    xA `is_approx` x <-> xA `less_defined` (exact x).
Proof. reflexivity. Qed.
  
#[global] Hint Unfold is_approx : core.

(** * This corresponds to the proposition [approx_down] in Section 5.3.

    Again, because of the particular definition of [is_approx] we use here, this
    can be proved simply by the law of transitivity. *)
Lemma approx_down {a b} `{Hld : LessDefined a} `{Exact b a} {_ : LessDefinedOrder Hld}:
  forall (x : b) (xA yA : a),
    xA `less_defined` yA -> yA `is_approx` x -> xA `is_approx` x.
Proof.
  intros. unfold is_approx. destruct H0.
  transitivity yA; assumption.
Qed.

(** In this part, we prove that any type [a] is also an [exact] of itself. We
    define this instance so that [listA a] would be an approximation of [list
    a]---so that we do not need to consider the approximation of [a]. A useful
    simplification. *)
Instance Exact_id {a} : Exact a a := id.

(** However, if we are not careful, the [LessDefined_id] instance might be used
    everywhere. To prevent that, we give [LessDefined_id] a very low priority
    here.

    Learn more about the priority of Coq's type classes in the [Controlling
    Instantiation] section of
    [https://softwarefoundations.cis.upenn.edu/qc-current/Typeclasses.html]. *)
#[global] Instance LessDefined_id {a} : LessDefined a | 100 := eq.

#[global] Instance LessDefinedOrder_id {a} : @LessDefinedOrder a _.
Proof.
Admitted.

#[global] Instance LessDefinedExact_id {a} : @LessDefinedExact a a _ _ _.
Proof.
Admitted.

#[global] Hint Unfold Exact_id : core.
#[global] Hint Unfold LessDefined_id : core.

(** * Tactics for working with optimistic and pessimistic specs. *)

(** Use the monotonicity laws. *)
Ltac relax :=
  match goal with
  | [ |- _ {{ _ }} ] => eapply pessimistic_mon
  | [ |- _ [[ _ ]] ] => eapply optimistic_mon
  end.
        
Ltac relax_apply lem :=
  match goal with
  | _ => apply lem
  | _ => relax; [apply lem|]
  end.

(** Automatically apply the inference rules. *)
Ltac mforward tac :=
  lazymatch goal with
  | [ |- (ret _) {{ _ }} ] => relax_apply pessimistic_ret
  | [ |- (bind _ _) {{ _ }} ] => relax_apply pessimistic_bind
  | [ |- tick {{ _}} ] => relax_apply pessimistic_tick
  | [ |- (thunk _) {{ _ }} ] => relax_apply pessimistic_thunk
  | [ |- (force _) {{ _ }} ] => relax_apply pessimistic_force
  | [ |- (forcing _ _) {{ _ }} ] => relax_apply pessimistic_forcing
  | [ |- (ret _) [[ _ ]] ] => relax_apply optimistic_ret
  | [ |- (bind _ _) [[ _ ]] ] => relax_apply optimistic_bind
  | [ |- tick [[ _]] ] => relax_apply optimistic_tick
  | [ |- (force _) [[ _ ]] ] => relax_apply optimistic_force
  | [ |- (forcing _ _) [[ _ ]] ] => relax_apply optimistic_forcing
  | [ |- (thunk _) [[ _ ]] ] => fail
  | [ |- (fun _ _ => False) {{ _ }} ] => intros ? ? []
  | [ |- _ {{ _ }} ] => autounfold; tac
  | [ |- _ [[ _ ]] ] => autounfold; tac
  end.

(** Heuristics for dealing with approximations. *)
Ltac invert_approx :=
  match goal with
  | [H : _ `is_approx` _ |- _] =>
    inversion H; let n:= numgoals in guard n=1; subst; clear H
  | [H : _ `less_defined` _ |- _] =>
    inversion H; let n:= numgoals in guard n=1; subst; clear H
  | [H : is_defined ?x |- _] =>
    destruct x; [|contradiction]; clear H
  end.

Ltac invert_eq :=
  subst; try match goal with
             | [H : _ = _ |- _] =>
               inversion H; subst; clear H
             end.

Ltac solve_approx tac :=
  repeat (match goal with
          | _ => solve [auto]
          | [ |- _ `is_approx` _ ] =>
            repeat autounfold; tac
          | [ |- is_defined (Thunk _) ] =>
            reflexivity
          end).

(** Heuristics for reasoning about pessimistic/optimistic specs. *)
Ltac mgo tac := repeat (intros;
                        repeat invert_eq; repeat invert_approx;
                        cbn in *; (mforward tac + solve_approx tac + lia)).
Ltac mgo' := mgo idtac.

Ltac mgo_list := mgo ltac:(simp exact_listA).

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
  - intros xs. induction xs as [ | x xs IH ]; mgo_list.
    + relax_apply @revA_cost. cbn; intros; lia.
    + inversion H5; subst. relax.
      eapply IHn with (acc:=x :: acc); try eassumption.
      constructor. repeat autounfold. simp exact_listA.
      constructor; assumption.
      cbn; intros. lia.
    + inversion H5; subst. relax.
      eapply IHn with (acc:=x :: acc); try eassumption. constructor.
      cbn; intros. lia.
Qed.
  
(** The pessimistic specification for [takeA] and the proof that [takeA]
    satisfies the spec, as stated in the paper. *)
Definition takeA__pessim {a} : 
forall (n : nat) (xs : list a) (xsA : T (listA a)),
  xsA `is_approx` xs ->
  (takeA n xsA) {{ fun zsA cost => cost <= min n (sizeX 0 xsA) + 1 }}.
Proof.
  unfold takeA. induction n; [mgo_list|].
  intros xs. induction xs as [ | x xs IH]; mgo_list.
  inversion H4; subst.
  specialize (IHn xs (Thunk x0)). cbn in IHn.
  relax_apply IHn; try assumption.
  mgo_list.
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
  - relax_apply H0. inversion H5; subst. assumption.
    cbn. intros. lia.
  - relax_apply H0. inversion H5; subst. assumption.
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
  relax_apply H0. inversion H5; subst; assumption.
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
    cbn in H0. relax. apply H0 with (v:=v); try eassumption.
    constructor.
    cbn. intros. lia.
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
    relax. eapply H0; try eassumption.
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

(* ----------------------- Section 4.2 ------------------------- *)

(** * Figure 10. *)
Definition impl3 {a b c} (P P' : a -> b -> c -> Prop) : Prop :=
  forall x y z, P x y z -> P' x y z.

Inductive Fix {a b} (gf : (a -> M b) -> (a -> M b)) x y n : Prop :=
| MkFix (self : a -> M b) : impl3 self (Fix gf) -> gf self x y n -> Fix gf x y n.

Lemma unfold_Fix {a b} (gf : (a -> M b) -> _)
  : (forall P P', impl3 P P' -> impl3 (gf P) (gf P')) ->
    impl3 (Fix gf) (gf (Fix gf)).
Proof.
  intros MON; intros ? ? ? W; induction W.
  eapply MON; [ | eapply H1 ].
  assumption.
Qed.

Lemma fold_Fix {a b} (gf : (a -> M b) -> _)
  : impl3 (gf (Fix gf)) (Fix gf).
Proof.
  intros ? ? ? W. econstructor.
  - intros ? ? ? V; apply V.
  - assumption.
Qed.
