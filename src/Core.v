Set Implicit Arguments.
Set Maximal Implicit Insertion.
Set Contextual Implicit.

From Coq Require Import Arith List Psatz.
From Coq Require Import Relations.Relation_Definitions Classes.RelationClasses.

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
