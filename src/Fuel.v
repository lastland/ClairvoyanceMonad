From Coq Require Import List Psatz.

Import ListNotations.

(** * The [Fuel] tree and the alternative [Lazy] representation. *)

Unset Elimination Schemes.

(** The same as [Fuel] used by Koen. *)
Inductive Fuel :=
| F (children: list Fuel).

(** Custom induction principles due to nested inductive types. *)
Lemma Fuel_ind : forall (P : Fuel -> Prop),
    (forall l, Forall P l -> P (F l)) ->
    forall f, P f.
Proof.
  intros P Hyp. fix SELF 1.
  intros [f]. apply Hyp.
  induction f; constructor.
  - apply SELF.
  - apply IHf.
Defined.

Set Elimination Schemes.

(** * A few functions regarding [Fuel]. *)

Fixpoint fuel1 (n : nat) : Fuel :=
  match n with
  | O => F []
  | S n' => F [fuel1 n']
  end.

Fixpoint cost (f : Fuel) : nat :=
  match f with
  | F l => S (list_sum (map cost l))
  end.

(** Beware of the [+ 1] on the right hand side! *)
Theorem fuel1_cost :
  forall n, cost (fuel1 n) = n + 1.
Proof.
  induction n; [reflexivity|cbn;lia].
Qed.

(** The other direction: taking a [Fuel], transforming it to a natural number
    using [cost] and back using [fuel1] is not true. *)
