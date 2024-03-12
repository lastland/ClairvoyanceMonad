From Clairvoyance Require Import Core Approx.

Inductive optionA (A : Type) : Type :=
  | NoneA : optionA A
  | SomeA : T A -> optionA A.
Arguments NoneA {A}.
Arguments SomeA {A}.

#[global]
Instance LessDefined_optionA {A}
  `{LessDefined A} : LessDefined (optionA A) :=
  fun a a' => match a, a' with
          | NoneA, NoneA => True
          | SomeA a, SomeA a' => a `less_defined` a'
          | _, _ => False                      
          end.

#[global]
Instance Exact_prodA {A B}
  `{Exact A B} : Exact (option A) (optionA B) :=
  fun a => match a with
       | None => NoneA
       | Some a => SomeA (exact a)
       end.
