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

Definition tlD (x : listA nat) : option (listA nat * (listA nat -> OTick (listA nat))) :=
  match x with
  | ConsA y ys =>
    let? (zs, d_zs) := forceD ys in
    Some (zs, fun zsA =>
      let+ ysA := d_zs zsA in
      OTick.ret (ConsA bottom ysA))
  | NilA => Some (NilA, fun d => OTick.ret NilA)
  end.

(* ** Example: cons *)

Definition consM (x : T nat) (xs : T (listA nat)) : M (listA nat) :=
  ret (ConsA x xs).

Definition unConsA (xs : listA nat) : OTick (T nat * T (listA nat)) :=
  match xs with
  | ConsA y ys => OTick.ret (y, ys)
  | NilA => OTick.fail
  end.

Definition consD (x : T nat) (xs : T (listA nat))
  : option (listA nat * (listA nat -> OTick (T nat * T (listA nat)))) :=
  Some (ConsA x xs, fun d =>
    let+ (y, ys) := unConsA d in
    OTick.ret (y, ys)).

Elpi Command Translate.
Elpi Accumulate lp:{{
  % Untyped translation. TODO: can/should we make use of typing information?
  pred translate i:term o:term.
}}.

Elpi Accumulate lp:{{
  pred def_of i:string o:term o:term.
  def_of IDENT M A :-
    coq.locate IDENT CID,
    CID = const ID,
    coq.env.const ID (some M) A.
}}.

Elpi Accumulate lp:{{
  pred translate_const i:string o:term.

  translate_const IDENT R :-
    def_of IDENT M _,
    translate M R.
}}.

Elpi Accumulate lp:{{
  typeabbrev v term.  % terms that should be variables
  typeabbrev indemand (v -> option term -> prop).

  type zerodemand indemand.
  zerodemand V none.

  % The first argument is the list of free variables.
  pred translate_head i:(list v) i:term o:term.

  % The first argument contains a continuation that expects the demand on the free variables.
  pred translate_body i:(indemand -> term -> prop) i:term o:term.
  pred translate_value i:(indemand -> term -> prop) i:v i:term o:term.
}}.

Elpi Accumulate lp:{{
  translate M M' :- translate_head [] M M'.
}}.

Elpi Accumulate lp:{{
  translate_head Vs (fun X A M) (fun X A M') :- !,
    pi x\
      (pi D K R\ (translate_value K D x R :- K (demand_singleton x D) R)) =>
      translate_head (x :: Vs) (M x) (M' x).
  translate_head Vs M M' :-
    not (var M),
    pi d\ translate_body (ret_tuple Vs) M M'.

  pred ret_tuple i:(list v) i:indemand o:term.
  ret_tuple Vs F {{ OTick.ret lp:R }} :- build_tuple Vs F R.

  pred build_tuple i:(list v) i:indemand o:term.
  build_tuple [] _ {{ tt }}.
  build_tuple [V] F R :- !, lookup_indemand V F R.
  build_tuple [V|Vs] F {{ pair lp:R lp:M }} :- lookup_indemand V F M, build_tuple Vs F R.

  % build_product [A,B,C] {{ C * B * A }}
  pred build_product i:(list term) o:term.
  build_product [] {{ unit }}.
  build_product [A] A :- !.
  build_product (A :: As) {{ lp:B * lp:A }} :- build_product As B.

  pred lookup_indemand i:v i:indemand o:term.
  lookup_indemand V F M :- F V none, M = {{ bottom }}.
  lookup_indemand V F M :- F V (some M).

  pred demand_singleton i:v i:term i:v o:(option term).
  demand_singleton X D X (some D).
  demand_singleton X _D Y none :- not (X = Y).
}}.

Elpi Accumulate lp:{{
  % _A = type of M, which we don't have access to because this translation does not keep track of types.
  translate_body K {{ Core.ret lp:M }} {{ Some (pair lp:{{M}} lp:{{fun `d` _A R}}) }} :- !,
    pi d\ translate_value K d M (R d).
  % match should be on a variable
  translate_body K (match V {{fun x : listA _ => _}} [N_nil, N_cons])
                   (match V {{fun x : listA _ => _}} [N_nil', N_cons']) :- !,
    translate_body K N_nil N_nil',
    translate_branch K V (Es\ M\ M = {{ ConsA }}) N_cons N_cons'.
  % force should be on a variable
  translate_body K {{ force lp:V }} R :- !, _.
  translate_body K M R :- std.fatal-error-w-data "No match:" M.
}}.

Elpi Accumulate lp:{{
  translate_value K D {{ NilA }} M' :- K zerodemand M'.
}}.

Elpi Accumulate lp:{{
  pred translate_branch i:(indemand -> term -> prop) i:v i:(indemand -> term -> prop) i:term o:term.
  translate_branch K V H (fun X A M) (fun X A M') :- !,
    pi x\
      translate_branch K V (translate_branch_accum x H) (M x) (M' x).
  translate_branch K V H M M' :-
    K' = (Es\ M\ sigma N\ H Es N, K (add V N Es) M),
    translate_body K' M M'.

  translate_branch_accum V H Es M :-
    H Es M1, lookup_demand x Es M2, M = app [M1, M2].

  pred add i:v i:term i:indemand i:v o:(option term).
  add V M Es V (some N) :- (Es V (some M'), N = {{ lub lp:M lp:M' }}) ; Es V none, N = M.
  add V M Es U N :- not (V = U), Es U N.
}}.

Elpi Accumulate lp:{{
  pred translate_type i:term o:term.
  translate_type T T' :- translate_type.aux [] T T'.
  translate_type.aux As (prod X A T) (prod X A T') :-
    pi x\ translate_type.aux (A :: As) (T x) (T' x).
  translate_type.aux As {{ M lp:T }} {{ option (lp:T * (lp:T -> OTick lp:R)) }} :-
    build_product As R.
}}.

Elpi Accumulate lp:{{
  pred translate_name i:string o:string.
  translate_name NAMEM NAMED :-
    S is NAMEM,
    N is size S,
    ( ("M" is substring NAMEM (N - 1) 1, !, NAMED is substring NAMEM 0 (N - 1) ^ "D")
    ; NAMED is NAMEM ^ "D").
}}.

Elpi Accumulate lp:{{
  main [str IDENT] :- !,
    def_of IDENT M A, !,
    translate M M', !,
    translate_type A A', !,
    std.assert-ok! (coq.typecheck M' A') "Result is ill-typed!",
    coq.env.fresh-global-id {translate_name IDENT} IDENT',
    coq.env.add-const IDENT' M' _ _ _.
  main [str IDENT, str "debug"] :-
    def_of IDENT M _,
    translate M M',
    coq.say M'.
  main [trm M] :-
    translate M M',
    coq.say "Translated:" M'.
  main ARGS :- coq.say "Translation failed. Arguments:" ARGS.
}}.

Elpi Typecheck.

(* Elpi Translate (fun x => ret x). *)

Elpi Translate idM.
Print idD1.

(* WIP
Elpi Trace.
Elpi Translate tlM "debug".
 *)
