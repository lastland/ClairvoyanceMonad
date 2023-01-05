(** * The category of demand functions *)

(** The naive demand functions in BankersQueue have types of the form
    [input -> outputA -> nat * inputA].
    But to be able to define a total translation of the lazy lambda calculus,
    we need a CCC. The definition of exponential objects necessitates
    a more elaborate representation, as [input -> outputA -> M inputA].  *)

From Coq Require Import Setoid SetoidClass Morphisms Lia Arith List.
From Equations Require Import Equations.
From Clairvoyance Require Import Core Approx List ApproxM Relations Setoid Tick.

Import ListNotations.

Import Tick.Notations.
#[local] Open Scope tick_scope.

(** * Approximation algebras *)

Module Export AA.

Class IsApproxSetoid (a' a : Type) `{Setoid a', IsApproxAlgebra a' a} : Prop :=
  { Proper_exact : Proper (equiv ==> less_defined) (exact (a := a') (b := a))
    (* TODO: Remove this hack/simplification.
       This is a fishy law; lub is meant only to be defined on cobounded elements.
       But this lets us break down the definition of AAMorphism cleanly
       into a setoid morphism and a DFun, with a simple monotonicity property for the latter.
       Otherwise, we only have a restricted form of monotonicity. *)
  ; Proper_lub : Proper (less_defined ==> less_defined ==> less_defined) (lub (a := a))
  }.

Notation IsAS := IsApproxSetoid.

Record ApproxAlgebra : Type :=
  { carrier :> Type
  ; AA_Setoid : Setoid carrier
  ; approx : Type
  ; AA_IsAA :> IsApproxAlgebra carrier approx
  ; AA_IsAS :> IsApproxSetoid carrier approx
  }.

End AA.

Notation AA := ApproxAlgebra (only parsing).

#[global] Existing Instance AA_Setoid.
#[global] Existing Instance AA_IsAA.
#[global] Existing Instance AA_IsAS.

#[local]
Instance IsAS_prod {a' a b' b : Type} `{IsApproxSetoid a' a} `{IsApproxSetoid b' b}
  : IsApproxSetoid (a' * b') (a * b).
Proof.
  constructor.
  { unfold Proper, respectful. intros x y xy.
    constructor; apply Proper_exact; apply xy. }
  { unfold Proper, respectful. intros x y xy u v uv. constructor; cbn; apply Proper_lub;
      apply xy + apply uv. }
Qed.

Canonical AAProd (a1 a2 : AA) : AA :=
  {| carrier := a1 * a2
  ;  approx := approx a1 * approx a2
  |}.

Infix "**" := AAProd (at level 40).

(** * Demand functions *)

Module Export DFun.

Notation Monotone := (Proper (equiv ==> less_defined ==> less_defined)).

(* Demand functions must be nondeterministic in general to be able to define [lub] *)
Record DFun (a1 a2 : AA) : Type :=
  { dfun :> a1 -> approx a2 -> Tick (approx a1)
  ; dfun_monotone : Monotone dfun }.

#[global] Existing Instance dfun_monotone.

Arguments dfun {a1 a2}.

#[global] Instance LessDefined_DFun {a1 a2 : AA} : LessDefined (DFun a1 a2) :=
  fun f f' => forall x, dfun f x `less_defined` dfun f' x.

#[global] Instance PreOrder_LessDefined_DFun {a1 a2 : AA} : PreOrder (less_defined (a := DFun a1 a2)).
Proof.
  unfold less_defined, LessDefined_DFun.
  constructor.
  - red. red. red. intros *; apply dfun_monotone, reflexivity.
  - red. red. red. intros.
    etransitivity. eapply H; reflexivity. eapply H0. auto.
Qed.

Definition id_dfun (a : AA) : a -> approx a -> Tick (approx a) :=
  fun x' x => Tick.ret x.

#[local]
Instance monotone_id (a : AA) : Monotone (id_dfun a).
Proof.
  unfold Proper, respectful, id_dfun.
  intros; repeat constructor; assumption. 
Qed.

Definition id (a : AA) : DFun a a :=
  {| dfun := id_dfun a |}.

Definition compose_dfun {a b c : AA} (f : a -> b) (df : DFun a b) (dg : DFun b c)
  : a -> approx c -> Tick (approx a) :=
  fun x' z =>
    let+ y := dg (f x') z in
    df x' y.

#[local]
Instance monotone_compose_dfun {a b c : AA} (f : a ~-> b) (df : DFun a b) (dg : DFun b c)
  : Monotone (compose_dfun f df dg).
Proof.
  unfold Proper, respectful, compose_dfun.
  intros xa' ya' xya' xc yc xyc.
  apply Tick.less_defined_bind.
  - apply dg; [ apply f, xya' | apply xyc ].
  - apply df, xya'.
Qed.

Definition compose {a b c : AA} (f : a ~-> b) (df : DFun a b) (dg : DFun b c)
  : DFun a c :=
  {| dfun := compose_dfun f df dg |}.

End DFun.

Module Export AAM.

(* This is like the GetPut law of lenses.
   For PutGet, we probably need an approximate version of apply. *)
Class FunApprox {a b : AA}
    (apply : a ~-> b) (coapply : DFun a b) : Prop :=
  coapply_approx :
    forall x' y, y `is_approx` apply x' -> Tick.val (coapply x' y) `is_approx` x'.

Record AAMorphism (a b : AA) : Type :=
  { apply :> a ~-> b
  ; coapply : DFun a b
  ; laws : FunApprox apply coapply
  }.

End AAM.

Arguments Build_AAMorphism a b &.
Arguments apply {a b}.
Arguments coapply {a b}.

Infix "~>>" := AAMorphism (at level 90) : type_scope.

#[global] Existing Instance AAM.laws.

Lemma AAMLaws_id (a : AA) : @FunApprox a a (Setoid.id a) (DFun.id a).
Proof.
  unfold FunApprox. exact (fun _ _ H => H).
Qed.

Definition AAMorphism_id (a : AA) : AAMorphism a a :=
  {| apply := Setoid.id a
  ;  coapply := DFun.id a
  ;  laws := AAMLaws_id a
  |}.

Lemma AAMLaws_compose {a b c : AA} (f : AAMorphism a b) (g : AAMorphism b c)
  : FunApprox (Setoid.compose f g) (DFun.compose (apply f) (coapply f) (coapply g)).
Proof.
  unfold FunApprox. intros x' y H. apply f, g, H.
Qed.

Record equiv_AAMorphism {a1 a2 : AA} (f f' : AAMorphism a1 a2) : Prop :=
  { equiv_apply_AAM : equiv (apply f) (apply f')
  ; ld_coapply_AAM : less_defined (coapply f) (coapply f')
  ; ld_coapply_AAM' : less_defined (coapply f') (coapply f)
  }.

#[local] Instance Equivalence_AAMorphism (a1 a2 : AA) : Equivalence (@equiv_AAMorphism a1 a2).
Proof.
  constructor.
  - constructor; reflexivity.
  - constructor.
    + symmetry; apply H.
    + apply H.
    + apply H.
  - constructor; etransitivity; apply H + apply H0.
Qed.

#[global] Instance Setoid_AAMorphism (a1 a2 : AA) : Setoid (AAMorphism a1 a2) := {}.

Record less_defined_AAMorphism {a1 a2 : AA} (f f' : AAMorphism a1 a2) : Prop :=
  { ld_equiv_apply_AAM : equiv (apply f) (apply f')
  ; ld_ld_coapply_AAM : less_defined (coapply f) (coapply f')
  }.

#[global] Instance LessDefined_AAMorphism (a1 a2 : AA) : LessDefined (AAMorphism a1 a2) := @less_defined_AAMorphism a1 a2.

#[local] Instance Reflexive_LessDefined_AAMorphism (a1 a2 : AA)
  : Reflexive (less_defined (a := AAMorphism a1 a2)).
Proof.
  constructor; reflexivity.
Qed.

#[local] Instance Transitive_LessDefined_AAMorphism (a1 a2 : AA)
  : Transitive (less_defined (a := AAMorphism a1 a2)).
Proof.
  constructor; (etransitivity; [apply H | apply H0]).
Qed.

#[global] Instance PreOrder_LessDefined_AAMorphism (a1 a2 : AA)
  : PreOrder (less_defined (a := AAMorphism a1 a2)) := {}.

Section Monoidal.

Context {a b : AA}.

Definition dfun_proj1 : a ** b -> approx a -> Tick (approx (a ** b)) :=
  fun xy' x => Tick.ret (x , bottom_of (exact (snd xy'))).

#[local] Instance monotone_dfun_proj1
  : Proper (equiv ==> less_defined ==> less_defined) dfun_proj1.
Proof.
  unfold Proper, respectful, dfun_proj1. intros x' y' xy' fx fy fxfy.
  apply Tick.less_defined_ret.
  constructor; cbn; [ apply fxfy | apply Proper_bottom, Proper_exact ].
  apply xy'.
Qed.

Definition DFun_proj1 : DFun (a ** b) a :=
  {| dfun := dfun_proj1 |}.

Lemma FunApprox_proj1 : FunApprox Setoid_proj1 DFun_proj1.
Proof.
  unfold FunApprox. intros x' y yx'. constructor; cbn.
  - apply yx'.
  - apply bottom_is_less.
Qed.

Definition AA_proj1 : (a ** b) ~>> a :=
  {| apply := Setoid_proj1
  ;  coapply := DFun_proj1
  ;  laws := FunApprox_proj1
  |}.

Definition dfun_proj2 : a ** b -> approx b -> Tick (approx (a ** b)) :=
  fun xy' y => Tick.ret (bottom_of (exact (fst xy')), y).

#[local] Instance monotone_dfun_proj2
  : Proper (equiv ==> less_defined ==> less_defined) dfun_proj2.
Proof.
  unfold Proper, respectful, dfun_proj2. intros x' y' xy' fx fy fxfy.
  apply Tick.less_defined_ret.
  constructor; cbn; [ apply Proper_bottom, Proper_exact | apply fxfy ].
  apply xy'.
Qed.

Definition DFun_proj2 : DFun (a ** b) b :=
  {| dfun := dfun_proj2 |}.

Lemma FunApprox_proj2 : FunApprox Setoid_proj2 DFun_proj2.
Proof.
  unfold FunApprox. intros x' y yx'. constructor; cbn.
  - apply bottom_is_less.
  - apply yx'.
Qed.

Definition AA_proj2 : (a ** b) ~>> b :=
  {| apply := Setoid_proj2
  ;  coapply := DFun_proj2
  ;  laws := FunApprox_proj2
  |}.

Context {c : AA}.

Definition dfun_pair (f : a -> approx b -> Tick (approx a)) (g : a -> approx c -> Tick (approx a))
  : a -> approx b * approx c -> Tick (approx a) :=
  fun x' yz =>
    let+ x1 := f x' (fst yz) in
    let+ x2 := g x' (snd yz) in
    Tick.ret (lub x1 x2).

#[local] Instance monotone_dfun_pair
    (f : a -> approx b -> Tick (approx a)) (g : a -> approx c -> Tick (approx a))
    (Proper_f : Proper (equiv ==> less_defined ==> less_defined) f)
    (Proper_g : Proper (equiv ==> less_defined ==> less_defined) g)
  : Proper (equiv ==> less_defined ==> less_defined) (dfun_pair f g).
Proof.
  unfold Proper, respectful, dfun_pair. intros x' y' xy' p q pq.
  apply Tick.less_defined_bind.
  - apply Proper_f; [ apply xy' | apply pq ].
  - intros x y xy. apply Tick.less_defined_bind.
    + apply Proper_g; [ apply xy' | apply pq ].
    + intros x2 y2 xy2. apply Tick.less_defined_ret.
      apply Proper_lub; assumption.
Qed.

Definition DFun_pair (f : DFun a b) (g : DFun a c) : DFun a (b ** c) :=
  {| dfun := dfun_pair f g |}.

#[local] Instance FunApprox_pair (f : a ~>> b) (g : a ~>> c)
  : FunApprox (Setoid_pair f g) (DFun_pair (coapply f) (coapply g)).
Proof.
  unfold FunApprox.
  intros x' y yx'. cbn.
  apply lub_least_upper_bound.
  - apply f, yx'.
  - apply g, yx'.
Qed.

Definition AA_pair (f : a ~>> b) (g : a ~>> c) : a ~>> b ** c :=
  {| apply := Setoid_pair f g
  ;  coapply := DFun_pair (coapply f) (coapply g)
  |}.

End Monoidal.

#[global] Instance Setoid_list {a} {_ : Setoid a} : Setoid (list a).
Admitted.

(* Partial function: we assume that both arguments approximate the same list *)
Fixpoint lub_listA {a} {_ : Lub a} (xs ys : listA a) : listA a :=
  match xs, ys with
  | NilA, NilA => NilA
  | ConsA x xs, ConsA y ys => ConsA (lub_T lub x y) (lub_T lub_listA xs ys)
  | _, _ => NilA  (* silly case *)
  end.

#[global] Instance Lub_listA {a} {_ : Lub a} : Lub (listA a) := lub_listA.

#[global] Instance LubLaw_listA {a} `{LubLaw a} : LubLaw (listA a).
Admitted.

#[global] Instance IsAA_listA {a' a} {_ : IsAA a' a} : IsAA (list a') (T (listA a)).
Proof.
  econstructor; try typeclasses eauto.
  eapply @LubLaw_T.
  - eapply @LubLaw_listA.
    typeclasses eauto.
  - typeclasses eauto.
Defined.

Parameter TODO : forall {P : Prop}, P.

#[global] Instance IsAS_listA {a' a} {_ : Setoid a'} {_ : IsAA a' a} {_ : IsAS a' a} : IsAS (list a') (T (listA a)).
Proof.
  constructor.
  - apply TODO.
  - apply TODO.
Qed.

Canonical AA_listA (a : AA) : AA :=
  {| carrier := list a
  ;  approx := T (listA (approx a))
  |}.

(* Values that are always total (no partial approximations). *)
Definition eq_Setoid (a : Type) : Setoid a :=
  {| equiv := eq |}.

Definition exact_IsAA (a : Type) : IsAA a a.
Proof.
  refine
  {| AO_Exact := Exact_id
  ;  AO_LessDefined := eq
  ;  AO_Lub := Lub_id
  ;  AO_BottomOf := fun x => x
  |}.
  apply TODO.
  apply TODO.
Defined.

Definition exact_IsAS (a : Type) : @IsAS a a (eq_Setoid a) (exact_IsAA a).
Proof. apply TODO. Qed.

Definition exact_AA (a : Type) : AA :=
  {| carrier := a
  ;  approx := a
  ;  AA_Setoid := eq_Setoid a
  ;  AA_IsAA := exact_IsAA a
  ;  AA_IsAS := exact_IsAS a
  |}.

Canonical AA_nat : AA := exact_AA nat.

(* Demand functions *)
Definition DF {a b : AA} (x' : a) (y' : b) : Type :=
  { y | y `is_approx` y' } -> Tick { x | x `is_approx` x' }.

(* DF is only the backwards direction.
It's a category but its objects are terms rather than types.

We can pair it with a forward function to construct
a category whose objects are types:

a ~> b = { f : a -> b | forall x, DF x (f x) }
*)

Module DF.

Definition id {a : AA} {x' : a} : DF x' x' := fun x => Tick.ret x.

Definition compose {a b c : AA} {x' : a} {y' : b} {z' : c} (f : DF x' y') (g : DF y' z')
  : DF x' z' := fun z => let+ y := g z in f y.

Module Notations.

Declare Scope df_scope.
Delimit Scope df_scope with df.
Bind Scope df_scope with DF.

Infix ">>>" := compose (left associativity, at level 40) : df_scope.

End Notations.

End DF.

Import DF.Notations.

Definition proj1DF {a b : AA} {xy' : a ** b} : DF xy' (fst xy').
Admitted.

Definition proj2DF {a b : AA} {xy' : a ** b} : DF xy' (snd xy').
Admitted.

Definition proj1DF' {a b : AA} {x' : a} {y' : b} : DF (x', y') x'.
Admitted.

Definition proj2DF' {a b : AA} {x' : a} {y' : b} : DF (x', y') y'.
Admitted.


Definition pairDF {a b c : AA} {x' : a} {y' : b} {z' : c} (f : DF x' y') (g : DF x' z')
  : DF x' (y', z').
Admitted.

Definition tickDF {a b : AA} {x' : a} {y' : b} : DF x' y' -> DF x' y' :=
  fun f y => Tick.tick >> f y.

Definition nilD {a b : AA} {x : a} : DF x (nil (A := b)).
Admitted.

Definition consD {r a : AA} {s : r} {x : a} {xs : list a} (xD : DF s x) (xsD : DF s xs)
  : DF s (x :: xs).
Admitted.

Definition bindD {r a b : AA} {s : r} {x : a} {y : b} (xD : DF s x)
    (k : DF (s, x) y)
  : DF s y :=
  DF.compose (pairDF DF.id xD) k.

Definition force_nil {a b c : AA} {g' : b} {y' : c} (f : DF g' y') : DF (g', nil (A := a)) y' :=
  fun y =>
    let+ (exist _ g gle) := f y in
    Tick.ret (exist  _ (g, Thunk NilA)
      (prod_rel _ _ (_, _) (_, _)
                gle
                (LessDefined_Thunk _ _ less_defined_list_NilA))).

Definition force_cons_lemma {a b : AA} {g' : b} {x' : a} {xs' : list a} {g x xs}
  : g `less_defined` exact g' ->
    x `less_defined` exact x' ->
    xs `less_defined` exact xs' ->
    (g, Thunk (ConsA (Thunk x) xs)) `less_defined` exact (g', x' :: xs').
Proof.
  intros; constructor; cbn; auto.
  constructor. simp exact.
  repeat constructor; assumption.
Qed.

Definition force_cons {a b c : AA} {g' : b} {x' : a} {xs' : list a} {y' : c}
    (f : DF (g', x', xs') y')
  : DF (g', cons x' xs') y' :=
  fun y =>
    let+ (exist _ (g, x, xs) (prod_rel _ _ _ _ (prod_rel _ _ _ _ gle xle) xsle)) := f y in
    Tick.ret (exist _ (g, Thunk (ConsA (Thunk x) xs))
      (force_cons_lemma gle xle xsle)).

Definition match_list {a b c : AA} {g : b} {f : list a -> c} {xs : list a}
    (NIL : DF g (f nil))
    (CONS : forall x xs', DF (g, x, xs') (f (cons x xs')))
  : DF (g, xs) (f xs) :=
  match xs with
  | nil => force_nil NIL
  | cons x xs' => force_cons (CONS x xs')
  end.

Definition swap {a b : AA} {x : a} {y : b} : DF (x, y) (y, x).
Admitted.

Class Project {a b : AA} (x : a) (y : b) : Type :=
  project : DF x y.

Arguments project : clear implicits.
Arguments project {a b x} y {_}.

#[global]
Instance Project_here {a b : AA} (x : a) (y : b) : Project (x, y) y := proj2DF.

#[global]
Instance Project_here1 {a : AA} (x : a) : Project x x := DF.id.

#[global]
Instance Project_there {a b c : AA} (x : a) (y : b) (z : c) `{!Project x z}
  : Project (x, y) z := DF.compose proj1DF (project z).

Class Tuple {a b : AA} (x : a) (y : b) : Type :=
  tuple : DF x y.
Arguments tuple : clear implicits.
Arguments tuple {a b x} y {_}.

#[global]
Instance Tuple_pair {a b c : AA} (x : a) (y : b) (z : c) `{!Tuple x y, !Tuple x z}
  : Tuple x (y, z) := pairDF (tuple y) (tuple z).

#[global]
Instance Tuple_single {a b : AA} (x : a) (y : b) `{!Project x y}
  : Tuple x y := project y.

Fixpoint append {a} (xs ys : list a) : list a :=
  match xs with
  | nil => ys
  | cons x xs1 => let zs := append xs1 ys in x :: zs
  end.

Fixpoint appendDF {a : AA} (xs ys : list a) : DF (xs, ys) (xs ++ ys) :=
  tickDF (
  DF.compose swap (match_list (f := fun xs => xs ++ ys)
    (* nil => ys *)
    DF.id
    (* cons x xs' => x :: xs ++ ys *)
    (fun x xs' => consD (project x) (DF.compose (tuple _) (appendDF xs' ys))))).

Definition predDF {a : AA} {g : a} {n : nat} : DF (g, S n) (g, n).
Admitted.

Definition match_nat {b c : AA} {g : b} {f : nat -> c} {n : nat}
    (ZERO : DF g (f O))
    (SUCC : forall n', DF (g, n') (f (S n')))
  : DF (g, n) (f n) :=
  match n with
  | O => proj1DF' >>> ZERO
  | S n' => predDF >>> SUCC n'
  end.

Fixpoint dropDF {a : AA} (n : nat) (xs : list a) : DF (n, xs) (drop n xs) :=
  tickDF (
  swap >>> match_nat (f := fun n => drop n xs)
    (* 0 => xs *)
    DF.id
    (* S n => ... *)
    (fun n => swap >>> match_list (f := fun xs => drop (S n) xs)
      nilD
      (fun x xs => tuple _ >>> dropDF n xs)
    ))%df.

(* An account stores credits in a data structure.

   Typically, a value [p : account x] associates
   credits to each constructor of [x], which may be thought of
   as the cost of forcing the thunk that produces that
   constructor.

   [credits p x'], given an account [p] and a demand [x']
   (an approximation of [x]), sums the credits of constructors
   in [x'] (a subset of those of [x]).

TODO: should account encode data structure invariants too? Or is it better to track them separately?
    *)
Class Account (a : AA) : Type :=
  { account : a -> Type
  ; credits : forall {x : a}, account x -> approx a -> nat
  }.
(* Morally, the approximation should be less than x,
   but we don't need a proof as an argument because
   we can just return 0 in the bad cases. *)

Declare Scope account_scope.
Bind Scope account_scope with account.

(* We store one [nat] for each constructor, including [nil].
   For simplicity, we do not store credits in [a];
   we could.
 *)
Fixpoint account_list {a : AA} (xs : list a) : Type :=
  match xs with
  | [] => nat
  | x :: xs => nat * account_list xs
  end.

(* Sum of the credits used by an approximation of a list [xs]. *)
Fixpoint credits_list {a : AA} {xs : list a} (cs : account_list xs) (xs' : approx (AA_listA a)) : nat :=
  match xs, cs, xs' with
  | _, _, Undefined => 0
  | [], c, Thunk NilA => c
  | x :: xs, (c, cs), Thunk (ConsA x' xs') => c + credits_list cs xs'
  | _, _, _ => 0
  end.

#[global]
Instance Account_list {a : AA} : Account (AA_listA a) :=
  {| account := account_list
  ;  credits := @credits_list a
  |}.

#[global]
Instance Account_nat : Account AA_nat :=
  {| account := fun _ => unit
  ;  credits := fun _ _ _  => 0
  |}.

Definition zero {n : nat} : account n := tt.

#[global]
Instance Account_pair {a b : AA} `{Account a, Account b} : Account (a ** b) :=
  {| account := fun xy => (account (fst xy) * account (snd xy))%type
  ;  credits := fun xy cd uv => credits (fst cd) (fst uv) + credits (snd cd) (snd uv)
  |}.

Definition cost_with {t} {P : t -> Prop} (p : t -> nat) (u : Tick (sig P)) : nat :=
  p (proj1_sig (Tick.val u)) + Tick.cost u.

Definition is_pure {a b : AA} {x' : a} {y' : b} (f : DF x' y') : Prop :=
  forall y, Tick.cost (f y) = 0.

(* f : DF x y = { y' : b' | ... }  -> Tick { x' : a' | ... }

     p : a' -> nat
     q : b' -> nat

    has_cost f p q = forall y', cost (f y') + p (value (f y')) <= q y'
 *)

Definition has_cost {a b : AA} `{Account a, Account b} {x' : a} {y' : b} (f : DF x' y') (p : account x') (q : account y')
  : Prop :=
  forall y, cost_with (credits p) (f y) <= credits q (proj1_sig y).

Definition map_account_head (f : nat -> nat) {a : AA} {xs : list a} (cs : account xs)
  : account xs :=
  match xs, cs with
  | [], c => f c
  | x :: xs, (c, cs) => (f c, cs)
  end.

Fixpoint append_account {a : AA}
    {xs : list a} (cs : account xs)
    {ys : list a} (ds : account ys)
  : account (xs ++ ys) :=
  match xs, cs, ys, ds with
  | [], c, _, _ => map_account_head S ds
  | x :: xs, (c, cs), ys, ds => (c, append_account cs ds)
  end.

Infix "++" := append_account : account_scope.

Fixpoint map_account (f : nat -> nat) {a : AA} {xs : list a} (cs : account xs)
  : account xs :=
  match xs, cs with
  | [], c => f c
  | x :: xs, (c, cs) => (f c, map_account f cs)
  end.

Theorem append_cost {a : AA} {xs ys : list a} (cs : account xs) (ds : account ys)
  : has_cost (appendDF xs ys)
             (cs, ds)
             (map_account S cs ++ ds).
Proof.
Admitted.

Fixpoint drop_account_ (acc : nat) {a : AA} (n : nat) {xs : list a} (cs : account xs)
  : account (drop n xs) :=
  match n, xs, cs with
  | O, _, _ => map_account_head (Nat.add acc) cs
  | S n, [], c => acc + c + 1
  | S n, x :: xs, (c, cs) => drop_account_ (acc + c + 1) n cs
  end.

Definition drop_account {a : AA} (n : nat) {xs : list a} (cs : account xs)
  : account (drop n xs) :=
  drop_account_ 0 n cs.

Theorem drop_cost {a : AA} {n : nat} {xs : list a} (cs : account_list xs)
  : has_cost (dropDF n xs)
             (zero, cs)
             (drop_account n cs).
Proof.
Admitted.

Definition drop_append {a : AA} (n : nat) (xs ys : list a) : DF (n, xs, ys) (drop n (xs ++ ys)) :=
  (pairDF (project n) (tuple _ >>> appendDF xs ys)) >>> (dropDF n (xs ++ ys)).

Theorem has_cost_compose {a b c : AA} `{Account a, Account b, Account c}
    {x : a} {y : b} {z : c} {f : DF x y} {g : DF y z}
    {p : account x} {q : account y} {r : account z}
  : has_cost f p q -> has_cost g q r -> has_cost (f >>> g) p r.
Proof.
  unfold has_cost, cost_with, DF.compose; intros Hf Hg. cbn.
  etransitivity; [ | apply Hg ].
  rewrite (Nat.add_comm (Tick.cost (g _))), Nat.add_assoc.
  apply Nat.add_le_mono_r.
  apply Hf.
Qed.

Theorem has_cost_pair {a b c : AA} `{Account a, Account b, Account c}
    {x : a} {y : b} {z : c} {f : DF x y} {g : DF x z}
    {p : account x} {q : account y} {r : account z}
  : has_cost f p q -> has_cost g p r -> has_cost (pairDF f g) p (q, r).
Proof.
Admitted.

Arguments append_account : simpl never.

Theorem drop_append_cost {a : AA} (n : nat) (xs ys : list a) (cs : account_list xs) (ds : account_list ys)
  : has_cost (drop_append n xs ys)
             (zero, cs, ds)
             (drop_account n (map_account S cs ++ ds)).
Proof.
  unfold drop_append.
  eapply has_cost_compose; [ | apply drop_cost ].
  eapply has_cost_pair.
  - admit.
  - eapply has_cost_compose; [ | apply append_cost ].
    admit.
Admitted.

(*
Definition lam {a b : AA} (x' : a) (y' : b)
  : (forall (r : AA) (s' : r), DF s' x' -> DF s' y') -> DF x' y' :=
  fun f => f _ _ DF.id.

Definition lam2 {a1 a2 b : AA} (x1' : a1) (x2' : a2) (y' : b)
  : (forall (r : AA) (s' : r), DF s' x1' -> DF s' x2' -> DF s' y') -> DF (x1' , x2') y' :=
  fun f => f _ (x1' , x2') proj1DF proj2DF.

Definition unconsOf {r a : AA} {s : r} (xs : list a) : Type :=
  match xs return Type with
  | nil => unit
  | x :: xs => (DF s x * DF s xs)%type
  end.

Definition unconsD {r a : AA} {s : r} {xs : list a} (xsD : DF s xs) : unconsOf (s := s) xs.
Admitted.

Definition match_list {r a b : AA} {s : r} {f : list a -> b} {xs : list a} (xsD : DF s xs)
    (NIL : DF s (f nil))
    (CONS : forall x ys, DF s x -> DF s ys -> DF s (f (x :: ys)))
  : DF s (f xs) :=
  match xs return unconsOf xs -> DF s (f xs) with
  | nil => fun _ => NIL
  | x :: xs => fun '(xD, xsD) => CONS x xs xD xsD
  end (unconsD xsD).

Definition credit_thunk {a} (f : a -> nat) : T a -> nat :=
  fun t =>
    match t with
    | Thunk x => f x
    | Undefined => 0
    end.

Definition credit_nil {a : AA} (n : nat) : Credits (AA_listA a) :=
  credit_thunk (fun l =>
    match l with
    | NilA => n
    | ConsA _ _ => 0
    end).

(** Either listA should have T only in the tail, or AA structures should be
    redefined to not include the toplevel T.
 *)
Definition credit_cons {a : AA} (n : nat) (ft : Credits (AA_listA a)) : Credits (AA_listA a) :=
  credit_thunk (fun l =>
    match l with
    | NilA => 0
    | ConsA h t => n + ft t
    end).

(*
CoInductive credit_list : Type :=
  { credit_nil : nat
  ; credit_cons : nat * credit_list
  }.

Definition apply_Tlist {a : Type} (al : credit_list -> listA a -> nat) (q : credit_list) (xs : T (listA a)) : nat :=
  match xs with
  | Undefined => 0
  | Thunk ys => al q ys
  end.

Fixpoint apply_list_ {a : Type} (q : credit_list) (xs : listA a) : nat :=
  match xs with
  | NilA => credit_nil q
  | ConsA _ ys =>
    fst (credit_cons q) + apply_Tlist apply_list_ (snd (credit_cons q)) ys
  end.

Definition apply_list {a : Type} (q : credit_list) (xs : T (listA a)) : nat :=
  apply_Tlist apply_list_ q xs.

Inductive cred_list {a b : AA} {x' : a} {ys' : list b}
  (f : DF x' ys') (p : Credits a) (q : credit_list) : Prop :=
| cred_nil : ys' = nil -> has_cost f 0 p (apply_list q) -> cred_list f p q
| cred_cons y' y2' : ys' = y' :: y2' -> cred_list f p q
.
*)

Class Value (a : AA) : Type :=
  { value : forall {s : AA} {x : s} {y : a}, DF x y -> Credits s -> Credits a -> Prop
  ; value_has_cost : forall {s : AA} {x : s} {y : a} (f : DF x y) (p : Credits s) (q : Credits a),
      value f p q -> has_cost f 0 p q
  }.

#[global]
Instance Value_pair {a b : AA} `{Value a, Value b} : Value (a ** b).
Admitted.

(* p +++ 0  |-  p *)
Lemma value_proj1DF {a b : AA} `{Value a, Value b} {xy' : a ** b} (p : Credits a)
  : value (proj1DF (xy' := xy')) (fun xy : approx (a ** b) => p (fst xy)) p.
Proof.
Admitted.

(* 0 +++ p  |-  p *)
Lemma value_proj2DF {a b : AA} `{Value a, Value b} {xy' : a ** b} (q : Credits b)
  : value (proj2DF (xy' := xy')) (fun xy : approx (a ** b) => q (snd xy)) q.
Proof.
Admitted.

(* p1 |- q      p2 |- r
   --------------------
   p1 + p2  |-  q +++ r *)
Lemma has_cost_pairDF {a b c : AA} {x' : a} {y' : b} {z' : c} (f : DF x' y') (g : DF x' z')
    (n m : nat) (p1 p2 : Credits a) (q : Credits b) (r : Credits c)
  : has_cost f n p1 q -> has_cost g m p2 r -> has_cost (pairDF f g) (n + m) (p1 + p2) (q +++ r).
Proof.
Admitted.

Lemma has_cost_lam2 {a1 a2 b : AA} `{Value a1, Value a2} (x1' : a1) (x2' : a2) (y' : b)
  (f : forall (r : AA) (s' : r), DF s' x1' -> DF s' x2' -> DF s' y')
  (n : nat)
  (p1 : Credits a1) (p2 : Credits a2) (q : Credits b)
  : (forall (r : AA) (s' : r) (x1D : DF s' x1') (x2D : DF s' x2') (pr1 pr2 : Credits r),
      value x1D pr1 p1 -> value x2D pr2 p2 -> has_cost (f r s' x1D x2D) n (pr1 + pr2) q) ->
   has_cost (lam2 x1' x2' y' f) n (p1 +++ p2) q.
Proof.
  intros Hf; unfold lam2. apply Hf.
  - apply (value_proj1DF (xy' := (x1', x2'))).
  - apply (value_proj2DF (xy' := (x1', x2'))).
Qed.

Definition null {a} (xs : list a) : bool :=
  match xs with
  | nil => true
  | _ => false
  end.

Definition zero {a} : Credits a := fun _ => 0.
*)

(*
Definition listCred {a} (x : Credits a) (xs : Credits (AA_listA a)) : Credits (AA_listA a).
Admitted.

Lemma has_cost_match_list {r a b : AA} `{Value a} {s : r} {f : list a -> b} {xs : list a} (xsD : DF s xs)
    (NIL : DF s (f nil))
    (CONS : forall x ys, DF s x -> DF s ys -> DF s (f (x :: ys)))
    (n : nat)
    (prNIL prHEAD prTAIL prCONS : Credits r)
    (pHEAD : Credits a) (pTAIL : Credits (AA_listA a))
    (q : Credits b)
    (has_cost_xsD : value xsD (if null xs then zero else prHEAD + prTAIL) (listCred pHEAD pTAIL))
    (has_cost_NIL : has_cost NIL n prNIL q)
    (has_cost_CONS : forall x ys (xD : DF s x) (ysD : DF s ys),
      value xD prHEAD pHEAD ->
      value ysD prTAIL pTAIL ->
      has_cost (CONS _ _ xD ysD) n prCONS q)
  : has_cost (match_list (f := f) xsD NIL CONS) n ((if null xs then prNIL else prCONS)) q.
Proof.
  destruct xs; cbn.
  - apply has_cost_NIL.
  - destruct (unconsD _) as [? ?] eqn:W.
    apply has_cost_CONS.
    + (* TODO: I need another predicate for variables to assert that they actually cost 0
         to be able to split them *)
Admitted.
*)

(* Attempt to define an ApproxAlgebra of functions (exponential object) *)

(*
#[global] Instance Laws_AAExp (a1 a2 : AA) : AA.Laws (a1 ~-> a2) (DFun a1 a2).
Proof.
  constructor.
  - exact _.
Qed.

Definition AAExp (a1 a2 : AA) : AA :=
  {| carrier := a1 ~-> a2
  ; approx := DFun a1 a2
  |}.
*)

(*
#[global] Instance Laws_AAProd (a1 a2 : AA) : AA.Laws (a1 * a2) (approx a1 * approx a2).
Proof.
  constructor.
  - exact _.
Qed.
*)

(*
Definition curry_Setoid {a1 a2 a3} `{Setoid a1, Setoid a2, Setoid a3} (f : a1 ~-> (a2 ~-> a3))
  : (a1 * a2) ~-> a3.
Admitted.

Definition curry_DFun {a1 a2 a3 : AA} (f : DFun a1 (AAExp a2 a3)) : DFun (AAProd a1 a2) a3.
Admitted.

#[global] Instance Laws_curry_AA {a1 a2 a3 : AA} (f : AAMorphism a1 (AAExp a2 a3))
  : AAM.Laws (a1 := AAProd a1 a2) (curry_Setoid (apply f)) (curry_DFun (coapply f)).
Proof.
Admitted.

Definition curry_AA {a1 a2 a3 : AA} (f : AAMorphism a1 (AAExp a2 a3))
  : AAMorphism (AAProd a1 a2) a3 :=
  {| apply := curry_Setoid (apply f) |}.
*)
