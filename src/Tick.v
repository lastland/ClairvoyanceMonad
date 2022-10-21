(** * The tick monad *)

From Clairvoyance Require Import Approx.
From Coq Require Import Morphisms.

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

#[global] Instance LessDefined_Tick {a} `{LessDefined a} : LessDefined (Tick a) :=
  fun x y => cost x <= cost y /\ val x `less_defined` val y.

#[global] Instance Transitive_LessDefined_Tick {a} `{LessDefined a}
  `{!Transitive (less_defined (a := a))} : Transitive (less_defined (a := Tick a)).
Proof.
  unfold Transitive, less_defined, LessDefined_Tick; intros * [] []; split; etransitivity; eauto.
Qed.

#[global] Instance Bottom_Tick {a} `{Bottom a} : Bottom (Tick a) := MkTick 0 bottom.

End Tick.
Notation Tick := Tick.Tick.
