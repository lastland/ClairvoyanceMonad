From Clairvoyance Require Import Misc Core.

(* Implementation of the same interface as the clairvoyance monad [M]
   using the partiality monad [option]. *)
Module Partial.
Notation ret := Option.ret. 
Notation bind := Option.bind.
Definition force {A : Type} (x : T A) : option A :=
  match x with
  | Undefined => None
  | Thunk y => Some y
  end.
Definition thunk {A : Type} (x : option A) : option (T A) :=
  match x with
  | None => None
  | Some y => Some (Thunk y)
  end.
(* [tick] is a noop. The partiality monad lets us model call-by-name,
   which is undistinguishable from call-by-need if we ignore cost. *)
Definition tick : option unit := Some tt.
Module Notation := Option.Notation.
End Partial.
