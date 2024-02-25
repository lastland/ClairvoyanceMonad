(** * The tick monad *)

From Clairvoyance Require Import Approx.
From Coq Require Import Morphisms Arith.

Set Primitive Projections.

Module Tick.

Record Tick (a : Type) : Type := MkTick
  { cost : nat
  ; val : a
  }.

Arguments MkTick {a}.
Arguments cost {a}.
Arguments val {a}.

Definition ret {a} : a -> Tick a := MkTick 0.
Definition bind {a b} (u : Tick a) (k : a -> Tick b) : Tick b :=
  {| cost := cost u + cost (k (val u))
  ;  val := val (k (val u))
  |}.

Definition tick : Tick unit := MkTick 1 tt.

Module Notations.
Declare Scope tick_scope.
Delimit Scope tick_scope with tick.
Bind Scope tick_scope with Tick.

Notation "'let+' x := u 'in' k" := (bind u (fun x => k%tick))
  (at level 200, x as pattern) : tick_scope.
Notation "u >> v" := (bind u (fun _ => v%tick)) (at level 61, left associativity) : tick_scope.

End Notations.

Lemma right_ret : forall {A : Type} (m : Tick A),
  (bind m (fun x => ret x)) = m.
Proof.
  intros. unfold bind. destruct m; simpl.
  f_equal. apply plus_0_r.
Qed.

#[global] Instance LessDefined_Tick {a} `{LessDefined a} : LessDefined (Tick a) :=
  fun x y => cost x <= cost y /\ val x `less_defined` val y.

#[global] Instance Reflexive_LessDefined_Tick {a} `{LessDefined a, !Reflexive (less_defined (a := a))}
  : Reflexive (less_defined (a := Tick a)).
Proof.
  constructor; reflexivity.
Qed.

#[global] Instance Transitive_LessDefined_Tick {a} `{LessDefined a}
  `{!Transitive (less_defined (a := a))} : Transitive (less_defined (a := Tick a)).
Proof.
  unfold Transitive, less_defined, LessDefined_Tick; intros * [] []; split; etransitivity; eauto.
Qed.

#[global] Instance Bottom_Tick {a} `{Bottom a} : Bottom (Tick a) := MkTick 0 bottom.

End Tick.
Notation Tick := Tick.Tick.

Lemma less_defined_ret {a} `{LessDefined a}
  : forall (x x' : a), x `less_defined` x' ->
    Tick.ret x `less_defined` Tick.ret x'.
Proof.
  constructor; auto.
Qed.

Lemma less_defined_bind {a b} `{LessDefined a, LessDefined b}
  : forall (u u' : Tick a), u `less_defined` u' ->
    forall (k k' : a -> Tick b), (forall x x', x `less_defined` x' -> k x `less_defined` k' x') ->
    Tick.bind u k `less_defined` Tick.bind u' k'.
Proof.
  intros u u' Hu k k' Hk.
  constructor; cbn.
  - apply Nat.add_le_mono; [ apply Hu | apply Hk, Hu ].
  - apply Hk, Hu.
Qed.


