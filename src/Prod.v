From Clairvoyance Require Import Core Approx.

Inductive prodA (A B : Type) : Type :=
  | pairA : T A -> T B -> prodA A B.
Arguments pairA {A} {B}.

Definition prodD {A B C D} (f : T A -> T C) (g : T B -> T D)
  (p : prodA A B) : prodA C D :=
  match p with
  | pairA a b => pairA (f a) (g b)
  end.

#[global]
Instance LessDefined_prodA {A B}
  `{LessDefined A} `{LessDefined B}: LessDefined (prodA A B) :=
  fun '(pairA a b) '(pairA a' b') => a `less_defined` a' /\ b `less_defined` b'.

#[global]
Instance Exact_prodA {A B C D}
  `{Exact A C} `{Exact B D} : Exact (A * B) (prodA C D) :=
  fun '(a, b) => pairA (exact a) (exact b).
