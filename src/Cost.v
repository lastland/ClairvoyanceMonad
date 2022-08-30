From Coq Require Import Arith List Lia Morphisms Relations.
From Clairvoyance Require Import Core Approx.

(** * Cost specifications *)

Definition at_most {a} `{LessDefined a} (u : M a) '((x, n) : a * nat) : Prop :=
  exists y m, u y m /\ x `less_defined` y /\ m <= n.

Definition at_least {a} `{LessDefined a} (u : M a) '((x, n) : a * nat) : Prop :=
  forall y m, u y m -> x `less_defined` y -> n <= m.

Infix "`at_most`" := at_most (at level 80).
Infix "`at_least`" := at_least (at level 80).

Definition costs {a} `{LessDefined a} (u : M a) (xn : a * nat) : Prop :=
  u `at_most` xn /\ u `at_least` xn.

Definition at_most0 {a} (u : M a) (n : nat) : Prop :=
  exists y m, u y m /\ m <= n.

Definition at_least0 {a} (u : M a) (n : nat) : Prop :=
  forall y m, u y m -> n <= m.

Infix "`at_most0`" := at_most0 (at level 80).
Infix "`at_least0`" := at_least0 (at level 80).

Definition costs0 {a} (u : M a) (n : nat) : Prop :=
  u `at_most0` n /\ u `at_least0` n.

(** ** Cost functions *)
(** ... rather than relations *)

Module NAT.
Definition t := nat -> Prop.  (* should be a singleton...? *)

Definition of_nat (n : nat) : t := eq n.

Definition lift_arith (f : nat -> nat -> nat) (x y : t) : t :=
  fun nz => exists nx ny, x nx /\ y ny /\ nz = f nx ny.

Definition add := lift_arith Nat.add.
Definition sub := lift_arith Nat.sub.
Definition mul := lift_arith Nat.mul.

Definition lift_rel (f : nat -> nat -> Prop) (x y : t) : Prop :=
  exists nx ny, x nx /\ y ny /\ f nx ny.
Definition eq := lift_rel eq.
Definition le := lift_rel Nat.le.
End NAT.

Declare Scope natprop_scope.
Delimit Scope natprop_scope with NAT.
Bind Scope natprop_scope with NAT.t.
Infix "+" := NAT.add : natprop_scope.
Infix "-" := NAT.sub : natprop_scope.
Infix "*" := NAT.mul : natprop_scope.
Infix "=" := NAT.eq : natprop_scope.
Infix "<=" := NAT.le : natprop_scope.

Coercion NAT.of_nat : nat >-> NAT.t.

Definition cost_of {a} (u : M a) : NAT.t :=
  costs0 u.
