From Coq Require Import Arith Setoid.
From Clairvoyance Require Import Core Approx.

Create HintDb mon.

#[global] Instance LessDefined_M {a} `{LessDefined a} : LessDefined (M a) :=
  fun u v =>
  u {{ fun x n =>
  v [[ fun y m => x `less_defined` y /\ m <= n ]] }}.

#[global] Instance PreOrder_LessDefined_M {a} `{LessDefined a} `{!PreOrder (less_defined (a := a))}
  : PreOrder (less_defined (a := M a)).
Proof.
  constructor.
  - red. unfold less_defined, LessDefined_M, pessimistic, optimistic. firstorder.
  - red. unfold less_defined, LessDefined_M, pessimistic, optimistic. firstorder.
    edestruct H0 as (? & ? & ? & ? & ?); [ eassumption | ].
    edestruct H1 as (? & ? & ? & ? & ?); [ eassumption | ].
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

Lemma optimistic_corelax {a} `{LessDefined a} (u u' : M a) (k : a -> nat -> Prop)
  : u `less_defined` u' -> uc k ->
    u [[ k ]] -> u' [[ k ]].
Proof.
  intros H' Hk Hu. hnf in H'. destruct Hu as (x & n & Hx & Hn).
  apply H' in Hx.
  eapply optimistic_mon; [ apply Hx | cbn; intros ? ? HH ].
  revert Hn; apply Hk; apply HH.
Qed.

Lemma ret_mon {a} `{LessDefined a}
  : forall x y : a, x `less_defined` y -> ret x `less_defined` ret y.
Proof.
  intros. unfold less_defined, LessDefined_M.
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
  end. intros * Hu * Hk.
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
  - hnf. contradiction.
  - apply ret_mon; auto.
Qed.

Lemma thunk_mon {a} `{LessDefined a} `{!PreOrder (less_defined (a := a))}
  : forall u v : M a, u `less_defined` v -> thunk u `less_defined` thunk v.
Proof.
  unfold less_defined, LessDefined_M. intros u v Hu.
  apply pessimistic_thunk.
  - relax; [ apply Hu | cbn; intros * Hv ]. apply optimistic_thunk_go.
    relax; [ apply Hv | cbn; intros * [] ]. split; [ solve_approx idtac | auto ].
  - apply optimistic_skip. split; [ reflexivity | auto ].
Qed.

Ltac solve_mon :=
  repeat
    (eauto with mon;
    match goal with
    | [ H : less_defined _ _ |- _ ] =>
      let t := type of H in
      match eval hnf in t with
      | eq ?x ?y => change t with (eq x y) in H; subst x + subst y
      end
    | [ |- less_defined _ _ ] => eassumption + reflexivity + constructor
    | [ |- less_defined (match ?x with _ => _ end) (match ?x with _ => _ end) ] => let Ex := fresh "Ex" in destruct x eqn:Ex
    | [ |- less_defined (ret _) (ret _) ] => apply ret_mon
    | [ |- less_defined (bind _ _) (bind _ _) ] => apply bind_mon; [ | intros ? ? ? ]
    | [ |- less_defined (force _) (force _) ] => apply force_mon
    | [ |- less_defined (thunk _) (thunk _) ] => apply thunk_mon
    end).