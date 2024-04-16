(* This module defines a command to translate monadic functions
   (in the clairvoyance monad) into demand functions. *)

(* A function of type [a -> M b] is translated to [a -> option (b * (b -> OTick a))],
   which is mostly equivalent to [(a -> option b) * (a -> b -> OTick a)]. *)

From elpi Require Import elpi.
From Clairvoyance Require Import Misc Core Approx ListA Tick.
Import Option.Notation.
#[local] Open Scope option_scope.
Import OTick.Notation.
#[local] Open Scope otick_scope.

(* * Examples of demand translations *)

(* ** Example: identity *)

(* Monadic function (pure strict ML + lazy) *)
Definition idM (x : listA nat) : M (listA nat) := ret x.

(* Demand translation/semantics *)
Definition idD (x : listA nat) : option (listA nat * (listA nat -> OTick (listA nat))) :=
  Some (x, fun d => OTick.ret d).

(* ** Example: tail *)

Definition tlM (x : listA nat) : M (listA nat) :=
  match x with
  | ConsA y ys => force ys (* expanded form:
                              let! zs := force ys in
                              ret zs *)
  | NilA => ret NilA
  end.

(* TODO: move to a module of primitives for demand translation *)
Definition forceD {A} (x : T A) : option (A * (A -> OTick (T A))) :=
  match x with
  | Undefined => None
  | Thunk y => Some (y, fun d => OTick.ret (Thunk d))
  end.

Definition forceD0 {A} (x : T A) : option A :=
  match x with
  | Undefined => None
  | Thunk y => Some y
  end.

Definition tlD (x : listA nat) : option (listA nat * (listA nat -> OTick (listA nat))) :=
  match x with
  | ConsA y ys =>
    let? (zs, d_zs) := forceD ys in
    Some (zs, fun zsA =>
      let+ ysA := d_zs zsA in
      OTick.ret (ConsA (bottom_of y) ysA))
  | NilA => Some (NilA, fun d => OTick.ret NilA)
  end.

(* ** Example: cons *)

Definition consM (x : T nat) (xs : T (listA nat)) : M (listA nat) :=
  ret (ConsA x xs).

Definition consD (x : T nat) (xs : T (listA nat))
  : option (listA nat * (listA nat -> OTick (T nat * T (listA nat)))) :=
  Some (ConsA x xs, fun d =>
    let+ (d0, d1) := unConsA d in
    OTick.ret (d0, d1)).

(* ** More artificial examples for testing *)

Definition etaM' (x : listA nat) : M (listA nat) :=
  let! x := ret x in ret x.

From Clairvoyance Extra Dependency "translation.elpi" as translate.

Elpi Command Translate.
Elpi Accumulate File translate.

(* Elpi Translate (fun x => ret x). *)

Elpi Translate idM.
Print idD1.

(* Elpi Trace "translate_body" "translate_branch_accum" "lookup_indemand" "add". *)
Elpi Translate tlM.
Print tlD1.

Elpi Translate consM.
Print consD1.
