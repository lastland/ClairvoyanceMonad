(** * Ordering between clairvoyant computations *)

From Coq Require Import Arith Setoid.
From Clairvoyance Require Import Core Approx.

(** A clairvoyant computation [u] is less defined than [v] if, whenever
  [u] produces a result [x] in time [n], [v] can produce a result [y] at least
  as defined as [x] in time at most [n].

  The nondeterministic results of a clairvoyant computation should be thought
  of as underapproximations of the behavior of a corresponding lazy computation
  (understood in the "natural" stateful sense):
  if [u] produces a result [(x,n)], that means that [u] models a lazy computation
  which may produce a result at least as defined as [x] in time at most [n]. *)
Record less_defined_M {a} `{LessDefined a} (u v : M a) : Prop :=
  { less_defined_M_def :
    u {{ fun x n =>
    v [[ fun y m => x `less_defined` y /\ m <= n ]] }} }.

#[global] Instance LessDefined_M {a} `{LessDefined a} : LessDefined (M a) :=
  less_defined_M.

#[global] Instance PreOrder_LessDefined_M {a} `{LessDefined a} `{!PreOrder (less_defined (a := a))}
  : PreOrder (less_defined (a := M a)).
Proof.
  constructor.
  - red. unfold less_defined, LessDefined_M. firstorder.
  - red. unfold less_defined, LessDefined_M. intros * [HH1] [HH2]; constructor.
    unfold pessimistic, optimistic in *. firstorder.
    edestruct HH1 as (? & ? & ? & ? & ?); [ eassumption | ].
    edestruct HH2 as (? & ? & ? & ? & ?); [ eassumption | ].
    eexists _, _; split; [ eassumption | split; etransitivity; eassumption ].
Qed.

(* Upward closed predicates *)
Definition uc {a} `{LessDefined a} (k : a -> nat -> Prop) : Prop :=
  forall x x' n n',
    x `less_defined` x' ->
    n' <= n ->
    k x n -> k x' n'.

(* [uc] lemmas for some common forms of cost specifications *)

Lemma uc_cost {a} `{LessDefined a} `{Transitive _ (less_defined (a := a))}
    (d : a) (n : nat)
  : uc (fun out cost => d `less_defined` out /\ cost <= n).
Proof.
  red; intros * ? ? []; split; etransitivity; try eassumption.
Qed.

(* Amortized cost specfications *)
Lemma uc_acost {a} `{LessDefined a} `{Transitive _ (less_defined (a := a))}
    (d : a) (m n : nat)
  : uc (fun out cost => d `less_defined` out /\ m + cost <= n).
Proof.
  red; intros * ? ? []; split; etransitivity; try eassumption.
  apply Nat.add_le_mono_l; assumption.
Qed.

(** [optimistic u k] is monotonic over [u], when the postcondition [k] is upward-closed. *)
Lemma optimistic_corelax {a} `{LessDefined a} (u u' : M a) (k : a -> nat -> Prop)
  : u `less_defined` u' -> uc k ->
    u [[ k ]] -> u' [[ k ]].
Proof.
  intros H' Hk Hu. hnf in H'. destruct Hu as (x & n & Hx & Hn).
  apply H' in Hx.
  eapply optimistic_mon; [ apply Hx | cbn; intros ? ? HH ].
  revert Hn; apply Hk; apply HH.
Qed.

(** * Monotonicity of the core combinators *)

Lemma ret_mon {a} `{LessDefined a}
  : forall x y : a, x `less_defined` y -> ret x `less_defined` ret y.
Proof.
  intros. constructor.
  apply pessimistic_ret, optimistic_ret.
  split; auto.
Qed.

Lemma bind_mon {a b} `{LessDefined a} `{LessDefined b}
  : forall (u u' : M a), u `less_defined` u' ->
    forall (k k' : a -> M b), (forall x x', x `less_defined` x' -> k x `less_defined` k' x') ->
    bind u k `less_defined` bind u' k'.
Proof.
  repeat lazymatch goal with
  | [ |- context [ less_defined (a := M ?a) ] ] =>
    let ld := eval unfold less_defined, LessDefined_M in (less_defined (a := M a)) in
    change (less_defined (a := M a)) with ld
  end. intros * Hu * Hk. constructor.
  apply pessimistic_bind.
  relax; [ apply Hu | cbn; intros x n [x' [n' [Hu' [Hx' Hn'] ] ] ] ].
  relax; [ apply Hk; eassumption | cbn; intros * Hk' ].
  apply optimistic_bind.
  exists x', n'. split; [ apply Hu' | ].
  relax; [ apply Hk' | cbn; intros * [] ]. split; [ | apply Nat.add_le_mono]; auto.
Qed.

Lemma force_mon {a} `{LessDefined a}
  : forall x y : T a, x `less_defined` y -> force x `less_defined` force y.
Proof.
  intros ? ? []; cbn.
  - constructor. hnf. contradiction.
  - apply ret_mon; auto.
Qed.

Lemma forcing_mon {a b} `{LessDefined a, LessDefined b}
  : forall x y : T a, x `less_defined` y ->
    forall k h : a -> M b, (forall r s, r `less_defined` s -> k r `less_defined` h s) ->
    forcing x k `less_defined` forcing y h.
Proof.
  intros; constructor; mforward idtac; intros ? ->.
  inversion H1; subst. relax_apply H2. assumption.
Qed.

Lemma thunk_mon {a} `{LessDefined a} `{!PreOrder (less_defined (a := a))}
  : forall u v : M a, u `less_defined` v -> thunk u `less_defined` thunk v.
Proof.
  unfold less_defined, LessDefined_M. intros u v Hu.
  constructor; apply pessimistic_thunk.
  - relax; [ apply Hu | cbn; intros * Hv ]. apply optimistic_thunk_go.
    relax; [ apply Hv | cbn; intros * [] ]. split; [ solve_approx | auto ].
  - apply optimistic_skip. split; [ reflexivity | auto ].
Qed.

Lemma bot_M {a} `{LessDefined a} (u : M a)
  : (fun _ _ => False) `less_defined` u.
Proof.
  constructor; hnf; contradiction.
Qed.

(* Monotonicity lemmas *)
Create HintDb mon.

#[global] Hint Resolve ret_mon bind_mon forcing_mon force_mon thunk_mon bot_M : mon.

Ltac solve_mon :=
  repeat
    (eassumption + reflexivity + eauto with mon;
    match goal with
    | [ H : less_defined _ _ |- _ ] =>
      let t := type of H in
      match eval hnf in t with
      | eq ?x ?y => change t with (eq x y) in H; subst x + subst y
      end
    end +
    lazymatch goal with
    | [ |- less_defined (a := M _) _ _ ] =>
      match goal with
      | [ |- less_defined (match ?x with _ => _ end) (match ?y with _ => _ end) ] =>
        tryif constr_eq x y then let Ex := fresh "Ex" in destruct x eqn:Ex else
        match goal with
        | [ H : less_defined x y |- _ ] => inversion H
        end
      | [ |- less_defined (ret _) (ret _) ] => apply ret_mon
      | [ |- less_defined (bind _ _) (bind _ _) ] => apply bind_mon; [ | intros ? ? ? ]
      | [ |- less_defined (forcing _ _) (forcing _ _) ] => apply forcing_mon; [ | intros ? ? ? ]
      | [ |- less_defined (force _) (force _) ] => apply force_mon
      | [ |- less_defined (thunk ?u) (thunk ?v) ] => apply (thunk_mon u v)
      | [ |- less_defined (fun _ _ => False) _ ] => apply bot_M
      end
    | [ |- less_defined _ _ ] => constructor
    end).
