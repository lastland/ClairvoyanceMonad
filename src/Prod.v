From Clairvoyance Require Import Core.

Inductive prodA (A B : Type) : Type :=
  | pairA : T A -> T B -> prodA A B.
Arguments pairA {A} {B}.

Definition prodD {A B C D} (f : T A -> T C) (g : T B -> T D)
  (p : prodA A B) : prodA C D :=
  match p with
  | pairA a b => pairA (f a) (g b)
  end.
