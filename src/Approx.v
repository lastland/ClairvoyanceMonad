(** * Approximations *)

(** Concepts for reasoning about approximations.

  "Approximations" are the values used in clairvoyant programs (functions
  with explicit cost semantics in the clairvoyance monad). "Pure values" are those
  used in non-monadic functions.

  - [less_defined]: an order relation between approximations (technically, just a preorder).
  - [lub]: least upper bound function on approximations.
  - [exact]: an embedding of pure values into approximations.
  - [is_approx]: a relation between approximations and pure values.

  Remarks:
  - [x `is_approx` y] is equivalent to [x `less_defined` exact y],
    and is now defined as such.
  - However, [exact] is not always definable, while [is_approx] might still
    have a reasonable definition. For instance, this is the case for functions.
    That's why our paper introduces [is_approx] as a separate concept.
    We haven't run into a use case of [is_approx] for functions or infinite data
    types so far though, so we reverted to defining [is_approx] as a notation using
    [less_defined] and [exact] for simplicity.
 *)

(** This part is a reference implementation of the definitions discussed in
    Section 5.3. *)

(** In the paper, we start by giving an [exact] function defined on lists. We
  mention later in the section that we would also want to be able to overload
  the [exact] function (and the [is_approx] and [less_defined] relations) for
  other types. One way of doing that is using type classes, as we show here. *)

From Coq Require Import Arith List Lia Morphisms Relations.
From Clairvoyance Require Import Core Relations.

Import ListNotations.

(* Type classes declared under this flag will have less confusing resolution.
  We will exclude [Exact] because in [Exact a b],
  [b] is supposed to be determined by [a], so it's fine to leave it as a flexible metavariable. *)

Definition is_defined {a} (t : T a) : Prop :=
  match t with
  | Thunk _ => True
  | Undefined => False
  end.

(** * [less_defined]: approximation ordering *)

(** [x `less_defined` y] *)

Class LessDefined a := less_defined : a -> a -> Prop.
Infix "`less_defined`" := less_defined (at level 42).

#[global] Hint Mode LessDefined ! : typeclass_instances.

(** [less_defined] should be a preorder (reflexive and transitive).
  (The paper says "order", which is imprecise. That was an oversight.)

  Every instance [LessDefined t] should be accompanied by an instance:
  [[
  #[global] Instance PreOrder_t : PreOrder (less_defined (a := t)).
  ]] *)

(** As a preorder, we expect to be able to do rewriting (in monotonic contexts).
  This instance registers [less_defined] as a relation for rewriting.
  Having [PreOrder] instances lying around is technically sufficient,
  but this helps automation in some cases. *)
#[global] Instance RewriteRelation_less_defined {a} `{LessDefined a}
  : RewriteRelation (less_defined (a := a)) := {}.

(** ** [less_defined] instance for [T]. *)

Inductive LessDefined_T {a : Type} `{LessDefined a} : LessDefined (T a) :=
| LessDefined_Undefined x : Undefined `less_defined` x
| LessDefined_Thunk x y :
    x `less_defined` y -> Thunk x `less_defined` Thunk y.

#[global] Hint Constructors LessDefined_T : core.
#[global] Existing Instance LessDefined_T.

(** An inversion lemma *)
Lemma less_defined_Thunk_inv {a} `{LessDefined a}
  : forall x y : a, Thunk x `less_defined` Thunk y -> x `less_defined` y.
Proof. inversion 1; auto. Qed.

#[local]
Instance Reflexive_LessDefined_T {a} `{LessDefined a} `{!Reflexive (less_defined (a := a))}
  : Reflexive (less_defined (a := T a)).
Proof. intros []; constructor; auto. Qed.

#[local]
Instance Transitive_LessDefined_T {a} `{LessDefined a} `{!Transitive (less_defined (a := a))}
  : Transitive (less_defined (a := T a)).
Proof.
  intros ? ? ? []; [ constructor | inversion 1; subst; constructor; etransitivity; eassumption ].
Qed.

(** [PreOrder] instance for [less_defined] at [T]. *)
#[global]
Instance PreOrder_LessDefined_T {a : Type} `{LessDefined a} `{Ho : !PreOrder (less_defined (a := a))}
  : PreOrder (less_defined (a := T a)).
Proof.
  constructor; exact _.
Qed.

(* Not sure we will ever need this, but it doesn't hurt to leave it here. *)
#[global]
Instance PartialOrder_LessDefined_T {a : Type} `{LessDefined a}
    `{Ho : PartialOrder _ eq (less_defined (a := a))}
  : PartialOrder eq (less_defined (a := T a)).
Proof.
constructor.
- intros ->. autounfold. constructor; reflexivity.
- inversion 1. induction H1.
  + inversion H2; reflexivity.
  + inversion H2; subst. f_equal. apply Ho. constructor; assumption.
Qed.

(** * [exact]: embedding pure values as approximations *)
Class Exact a b : Type := exact : a -> b.

(** This corresponds to the [exact_max] in Section 5.3: [exact] embeddings should be
  maximal elements. *)
Class ExactMaximal a b {Hless : LessDefined a} (Hexact : Exact b a) :=
  exact_maximal : forall (xA : a) (x : b), exact x `less_defined` xA -> exact x = xA.

Arguments ExactMaximal : clear implicits.
Arguments ExactMaximal a b {Hless Hexact}.

(** I don't think we've actually needed this fact so far. *)

(** ** [exact] instance for [T] *)

(** When [exact] doesn't reduce by [cbn], we may register rewrite lemmas in the
    hint database [exact] for doing simplification by [autorewrite with exact]. *)
Create HintDb exact.

#[global]
Instance Exact_T {a b} {r: Exact a b} : Exact a (T b)
  := fun x => Thunk (exact x).

#[global]
Instance ExactMaximal_T {a b} `{AA : ExactMaximal a b} : ExactMaximal (T a) b.
Proof.
  red. intros xA x H. inversion H; subst.
  unfold exact, Exact_T. f_equal. apply exact_maximal. assumption.
Qed.

(** * [is_approx]: relating approximations and pure values *)

(** In our paper, the definition of [is_approx] can be anything as long as it
    satisfies the [approx_exact] proposition. In this file, we choose the most
    direct definition that satisfies the [approx_exact] law. *)
(** TODO: this should really be its own class, to support functions and infinite data types
    (see remarks at the top). *)
Notation is_approx xA x := (xA `less_defined` exact x) (only parsing).
Infix "`is_approx`" := is_approx (at level 42, only parsing).

(** This corresponds to the proposition [approx_exact] in Section 5.3.

  And because of our particular definition, this is true by
  definition. However, this cannot be proved generically if the definition of
  [is_approx] can be anything. *)
Theorem approx_exact {a b} `{Exact b a} `{LessDefined a} :
  forall (x : b) (xA : a),
    xA `is_approx` x <-> xA `less_defined` (exact x).
Proof. reflexivity. Qed.

(** This corresponds to the proposition [approx_down] in Section 5.3.

  Again, because of the particular definition of [is_approx] we use here, this
  can be proved simply by the law of transitivity. *)
Lemma approx_down {a b} `{Hld : LessDefined a} `{Exact b a} `{PartialOrder _ eq (less_defined (a := a))}:
  forall (x : b) (xA yA : a),
    xA `less_defined` yA -> yA `is_approx` x -> xA `is_approx` x.
Proof.
  intros. etransitivity; eassumption.
Qed.

(**)

(** * [lub]: least upper bound. *)

(** [lub] is defined as a total function for convenience, but it is morally
  only partially defined: [lub x y] only makes sense when [x] and [y] have
  at least one common upper bound (they are [cobounded]). *)
Class Lub (a : Type) : Type :=
  lub : a -> a -> a.

#[global] Hint Mode Lub ! : typeclass_instances.

Create HintDb lub.

Definition lub_T {a} (_lub : a -> a -> a) : T a -> T a -> T a :=
  fun x y =>
    match x, y with
    | Undefined, y => y
    | x, Undefined => x
    | Thunk x, Thunk y => Thunk (_lub x y)
    end.

Definition Lub_T {a} `{Lub a} : Lub (T a) := Eval unfold lub_T in lub_T lub.
#[global] Existing Instance Lub_T.

(** [cobounded x y]: [x] and [y] have a common upper bound. *)
Definition cobounded {a} `{LessDefined a} (x y : a) : Prop :=
  exists z : a, x `less_defined` z /\ y `less_defined` z.

#[global] Hint Unfold cobounded : core.

Class LubLaw a `{Lub a, LessDefined a} : Prop :=
  { lub_least_upper_bound : forall x y z : a,
      x `less_defined` z -> y `less_defined` z -> lub x y `less_defined` z
  ; lub_upper_bound_l : forall x y : a, cobounded x y -> x `less_defined` lub x y
  ; lub_upper_bound_r : forall x y : a, cobounded x y -> y `less_defined` lub x y
  }.

#[global] Hint Mode LubLaw ! - - : typeclass_instances.
#[global] Hint Resolve lub_least_upper_bound lub_upper_bound_l lub_upper_bound_r : lub.

Lemma lub_inv {a} `{LubLaw a} `{!Transitive (less_defined (a := a))}
  : forall x y z : a, cobounded x y -> lub x y `less_defined` z ->
       x `less_defined` z /\ y `less_defined` z.
Proof.
  intros x y z Hxy Hlub; split; (etransitivity; eauto with lub).
Qed.

#[global] Instance LubLaw_T {a} `{LubLaw a} `{!Reflexive (less_defined (a := a))} : LubLaw (T a).
Proof.
  constructor.
  - intros ? ? ? []; inversion 1; subst; cbn; constructor; auto with lub.
  - intros x y [z [ [? | Hx] Hy] ]; cbn; [ constructor | ].
    inversion Hy; subst; constructor; eauto with lub.
  - intros x y [z [ Hx Hy ] ]; destruct Hy as [ | Hy]; cbn; [ constructor | ].
    inversion Hx; subst; constructor; eauto with lub.
Qed.

(** * [bottom] *)

(** Ordered types with a least element. It represents an empty demand.
  It's also convenient as a dummy value in nonsensical cases. *)
Class Bottom (a : Type) : Type :=
  bottom : a.

#[global] Hint Mode Bottom ! : typeclass_instances.

#[global] Instance Bottom_T {a} : Bottom (T a) := Undefined.
#[global] Instance Bottom_prod {a b} `{Bottom a, Bottom b} : Bottom (a * b) := (bottom, bottom).

Class BottomLeast a `{LessDefined a,Bottom a} : Prop :=
  bottom_least : forall x : a, bottom `less_defined` x.

#[global] Instance BottomLeast_t {a} `{LessDefined a} : BottomLeast (T a).
Proof. constructor. Qed.

Class BottomOf (a : Type) : Type :=
  bottom_of : a -> a.

#[global] Hint Mode BottomOf !.

#[global] Instance BottomOf_list {a} `{BottomOf a} : BottomOf (list a) :=
  fix _bottom_of (xs : list a) : list a :=
    match xs with
    | [] => []
    | x :: xs => bottom_of x :: _bottom_of xs
    end.

#[global] Instance BottomOf_T {a} : BottomOf (T a) := fun _ => Undefined.

Class BottomIsLeast a `{BottomOf a, LessDefined a} : Prop :=
  bottom_is_least : forall (x y : a), x `less_defined` y -> bottom_of y `less_defined` x.

#[global] Hint Mode BottomIsLeast ! - - : typeclass_instances.

Lemma bottom_is_less {a} `{BottomOf a, LessDefined a, PreOrder a less_defined, !BottomIsLeast a}
  : forall (x : a), bottom_of x `less_defined` x.
Proof.
  intros; apply bottom_is_least. reflexivity.
Qed.

Lemma Proper_bottom {a} `{BottomOf a, LessDefined a, PreOrder a less_defined, !BottomIsLeast a}
  : Proper (less_defined ==> less_defined) (bottom_of (a := a)).
Proof.
  unfold Proper, respectful. intros x y xy; do 2 apply bottom_is_least; assumption.
Qed.

#[global] Instance BottomIsLeast_T {a} `{LessDefined a} : BottomIsLeast (T a).
Proof. constructor. Qed.


(** Order structure on approximation values [valueA].
    Core operations ([exact], [less_defined], [lub], [bottom_of])
    and their properties. *)
Class IsApproxAlgebra (t tA : Type) : Type :=
  { AO_Exact         :> Exact t     tA
  ; AO_LessDefined   :> LessDefined tA
  ; AO_Lub           :> Lub         tA
  ; AO_BottomOf      :> BottomOf    tA

  ; AO_PreOrder      :> PreOrder (less_defined (a := tA))
  ; AO_LubLaw        :> LubLaw        tA
  ; AO_BottomIsLeast :> BottomIsLeast tA
  }.

#[global] Hint Mode IsApproxAlgebra - - : typeclass_instances.

Notation IsAA := IsApproxAlgebra (only parsing).

(** * Instances for standard types *)

#[global] Instance Exact_prod {a aA b bA} `{Exact a aA, Exact b bA} : Exact (a * b) (aA * bA) :=
  fun xs => (exact (fst xs), exact (snd xs)).

#[global] Instance LessDefined_prod {a b} `{LessDefined a, LessDefined b} : LessDefined (a * b) :=
  pair_rel less_defined less_defined.

#[global] Instance ExactMaximal_prod {a aA b bA} `{ExactMaximal a aA, ExactMaximal b bA}
  : ExactMaximal (a * b) (aA * bA).
Proof.
  intros [] [] [HH1 HH2]; cbn in *. apply exact_maximal in HH1; apply exact_maximal in HH2.
  unfold exact, Exact_prod; cbn. congruence.
Qed.

#[global] Instance Lub_prod {a b} `{Lub a, Lub b} : Lub (a * b) :=
  fun x y => (lub (fst x) (fst y), lub (snd x) (snd y)).

#[global] Instance LubLaw_prod {a b} `{LubLaw a, LubLaw b} : LubLaw (a * b).
Proof.
  constructor.
  - intros * [] []; constructor; cbn; apply lub_least_upper_bound; auto.
  - intros * [? [ [] [] ] ]; constructor; cbn; apply lub_upper_bound_l; eauto.
  - intros * [? [ [] [] ] ]; constructor; cbn; apply lub_upper_bound_r; eauto.
Qed.

#[global] Instance BottomOf_prod {a b} `{BottomOf a, BottomOf b} : BottomOf (a * b) :=
  fun xy => (bottom_of (fst xy), bottom_of (snd xy)).

#[global] Instance BottomIsLeast_prod {a b} `{BottomIsLeast a, BottomIsLeast b}
  : BottomIsLeast (a * b).
Proof.
  intros x y xy. constructor; apply bottom_is_least, xy.
Qed.

#[global] Instance IsAA_prod {a' a b' b} {_ : IsAA a' a} {_ : IsAA b' b} : IsAA (a' * b') (a * b)
  := {}.

#[global] Instance Exact_option {a aA} `{Exact a aA} : Exact (option a) (option aA) := fun ox =>
  match ox with
  | None => None
  | Some x => Some (exact x)
  end.

#[global] Instance LessDefined_option {a} `{LessDefined a} : LessDefined (option a) :=
  option_rel less_defined.

#[global] Instance PreOrder_option {a} `{LessDefined a} `{!PreOrder (less_defined (a := a))}
  : PreOrder (less_defined (a := option a)).
Proof.
  econstructor.
  - intros []; constructor. reflexivity.
  - intros ? ? ? []. auto. inversion 1; subst. constructor; etransitivity; eauto.
Qed.

#[global] Instance ExactMaximal_option {a aA} `{ExactMaximal aA a}
  : ExactMaximal (option aA) (option a).
Proof.
  intros [] []; inversion 1; subst; cbn; f_equal. apply exact_maximal. auto.
Qed.

#[global] Instance Exact_list {a aA} `{Exact a aA} : Exact (list a) (list aA) :=
  map exact.

Inductive list_rel {a b} (r : a -> b -> Prop) : list a -> list b -> Prop :=
| list_rel_nil : list_rel r nil nil
| list_rel_cons x y xs ys : r x y -> list_rel r xs ys -> list_rel r (x :: xs) (y :: ys)
.

#[global] Instance LessDefined_list {a} `{LessDefined a} : LessDefined (list a) :=
  list_rel less_defined.

Lemma cobounded_cons {a} `{LessDefined a} (x : a) xs y ys
  : cobounded x y -> cobounded xs ys -> cobounded (x :: xs) (y :: ys).
Proof.
  intros (z & Hx & Hy) (zs & Hxs & Hys). exists (z :: zs).
  split; constructor; eauto.
Qed.

Lemma cobounded_list_ind a `(LessDefined a) (P : list a -> list a -> Prop)
  : P nil nil ->
    (forall x xs y ys,
      cobounded x y -> cobounded xs ys -> P xs ys -> P (x :: xs) (y :: ys)) ->
    forall xs ys, cobounded xs ys -> P xs ys.
Proof.
  intros Hnil Hcons xs ys (zs & Hxs & Hys).
  revert ys Hys; induction Hxs as [ | ? ? ? ? ? ? IH ]; intros.
  - inversion Hys; apply Hnil.
  - inversion Hys; clear Hys; subst. apply Hcons; eauto.
Qed.

#[global] Instance PreOrder_list {a} `{LessDefined a} `{!PreOrder (less_defined (a := a))}
  : PreOrder (less_defined (a := list a)).
Proof.
  constructor.
  - intros xs; induction xs; constructor; reflexivity + auto.
  - intros xs ys zs Hxs; revert zs; induction Hxs as [ | ? ? ? ? ? ? IH ]; intros zs Hys; inversion Hys; clear Hys; subst.
    + constructor.
    + constructor; [ etransitivity; eauto | apply IH; auto ].
Qed.

#[global] Instance ExactMaximal_list {a aA} `{ExactMaximal aA a}
  : ExactMaximal (list aA) (list a).
Proof.
  intros xs ys; revert xs; induction ys; intros xs Hxs; inversion Hxs; clear Hxs.
  - constructor.
  - cbn; f_equal. { apply exact_maximal; auto. } { auto. }
Qed.

Fixpoint zip_with {a b c} (f : a -> b -> c) (xs : list a) (ys : list b) : list c :=
  match xs, ys with
  | x :: xs, y :: ys => f x y :: zip_with f xs ys
  | _, _ => nil
  end.

#[global] Instance Lub_list {a} `{Lub a} : Lub (list a) :=
  zip_with lub.

#[global] Instance LubLaw_list {a} `{LubLaw a} : LubLaw (list a).
Proof.
  constructor.
  - intros x y z Hxz; revert y; induction Hxz as [ | ? ? ? ? ? ? IH ]; cbn.
    + constructor.
    + intros ? Hy; inversion Hy; clear Hy; subst.
      constructor; [ apply lub_least_upper_bound; auto | ].
      apply IH; auto.
  - intros x y (z & Hx & Hy). revert y Hy; induction Hx as [ | ? ? ? ? ? ? IH ]; cbn.
    + constructor.
    + intros ? Hy; inversion Hy; clear Hy; subst.
      constructor; [ apply lub_upper_bound_l; eauto | ].
      apply IH; auto.
  - intros x y (z & Hx & Hy). revert x Hx; induction Hy as [ | ? ? ? ? ? ? IH ]; cbn.
    + destruct x; constructor.
    + intros ? Hx; inversion Hx; clear Hx; subst.
      constructor; [ apply lub_upper_bound_r; eauto | ].
      apply IH; auto.
Qed.

#[global] Instance BottomIsLeast_list {a} `{BottomIsLeast a} : BottomIsLeast (list a).
Proof.
  intros xs ys Hxsys. induction Hxsys; [ constructor | constructor; [ apply bottom_is_least; auto | auto ] ].
Qed.

Lemma less_defined_app {a} {LD : LessDefined a} (xs1 xs2 ys1 ys2 : list a)
  : xs1 `less_defined` ys1 -> xs2 `less_defined` ys2 ->
    (xs1 ++ xs2) `less_defined` (ys1 ++ ys2).
Proof.
  intros H J; induction H; cbn; [ auto | constructor; auto ].
Qed.

Lemma less_defined_app_inv {a} {LD : LessDefined a} (xs0 xs1 xs2 : list a)
  : xs0 `less_defined` (xs1 ++ xs2) ->
    exists xs01 xs02, xs0 = xs01 ++ xs02 /\
      xs01 `less_defined` xs1 /\ xs02 `less_defined` xs2.
Proof.
  revert xs0. induction xs1 as [ | x xs1 IH]; intros xs0 Hxs0; cbn.
  - exists [], xs0. split; [reflexivity | split; [ constructor | assumption ] ].
  - cbn in Hxs0. inversion Hxs0; clear Hxs0; subst.
    specialize (IH _ H3). destruct IH as (xs01 & xs02 & Hxs0 & Hxs1 & Hxs2).
    exists (x0 :: xs01), xs02.
    split; [ cbn; f_equal; auto | ].
    split; [ constructor; auto | auto ].
Qed.

Lemma exact_list_app {a aA} {EE : Exact a aA} (xs1 xs2 : list a)
  : exact (xs1 ++ xs2) = exact xs1 ++ exact xs2.
Proof. apply map_app. Qed.

Notation resp r1 r2 f f' := (forall x x', r1 x x' -> r2 (f x) (f' x')) (only parsing).

#[global] Instance LessDefined_fun {a b} `{LessDefined a, LessDefined b}
  : LessDefined (a -> b) :=
  fun f f' => resp less_defined less_defined f f'.

#[global] Instance Lub_fun {a b} `{Lub b} : Lub (a -> b) :=
  fun f f' x => lub (f x) (f' x).

#[global] Instance Bottom_fun {a b} `{Bottom b} : Bottom (a -> b) := fun _ => bottom.

(** In this part, we prove that any type [a] is also an [exact] of itself. We
    define this instance so that [listA a] would be an approximation of [list
    a]---so that we do not need to consider the approximation of [a]. A useful
    simplification. *)
#[local] Instance Exact_id {a} : Exact a a := id.

(** However, if we are not careful, the [LessDefined_id] instance might be used
    everywhere. To prevent that, we give [LessDefined_id] a very low priority
    here.

    Learn more about the priority of Coq's type classes in the [Controlling
    Instantiation] section of
    [https://softwarefoundations.cis.upenn.edu/qc-current/Typeclasses.html]. *)
#[local] Instance LessDefined_id {a} : LessDefined a | 100 := eq.

#[local] Instance PreOrder_LessDefined_id {a} : PreOrder (less_defined (a := a)).
Proof. exact _. Qed.

#[local] Instance ExactMaximal_id {a} : ExactMaximal a a.
Proof. cbv; easy. Qed.

#[local] Instance Lub_id {a} : Lub a := fun n _ => n.
#[local] Instance LubLaw_id {a} : LubLaw a.
Proof.
  constructor;cbv;firstorder (subst; auto).
Qed.

#[global] Hint Unfold Exact_id : core.
#[global] Hint Unfold LessDefined_id : core.

#[global] Instance Exact_nat : Exact nat nat := id.
#[global] Instance LessDefined_nat : LessDefined nat := eq.
#[global] Instance PreOrder_LessDefined_nat : PreOrder (less_defined (a := nat)) := PreOrder_LessDefined_id.
#[global] Instance ExactMaximal_nat : ExactMaximal nat nat := ExactMaximal_id.
#[global] Instance Lub_nat : Lub nat := fun n _ => n.
#[global] Instance LubLaw_nat : LubLaw nat := LubLaw_id.

#[global] Instance Exact_unit : Exact unit unit := id.
#[global] Instance LessDefined_unit : LessDefined unit := eq.
#[global] Instance PreOrder_LessDefined_unit : PreOrder (less_defined (a := unit)) := PreOrder_LessDefined_id.
#[global] Instance ExactMaximal_unit : ExactMaximal unit unit := ExactMaximal_id.
#[global] Instance Lub_unit : Lub unit := fun n _ => n.
#[global] Instance LubLaw_unit : LubLaw unit := LubLaw_id.

(** * Deriving instances via isomorphisms *)

(** Bijection between [a] and [b]. *)
Class Rep (a b : Type) : Type :=
  { to_rep : a -> b
  ; from_rep : b -> a
  }.

(** Laws of a bijection *)
Class RepLaw (a b : Type) `{Rep a b} : Prop :=
  { to_from : forall x, to_rep (from_rep x) = x
  ; from_to : forall x, from_rep (to_rep x) = x
  }.

Class LessDefinedRep a b `{REP : Rep a b, LessDefined a, LessDefined b} : Prop :=
  to_rep_less_defined : forall x y : a, less_defined x y <-> less_defined (a := b) (to_rep x) (to_rep y).

Lemma Reflexive_Rep {a b} `{LessDefinedRep a b} `{!Reflexive (less_defined (a := b))}
  : Reflexive (less_defined (a := a)).
Proof.
  unfold Reflexive. intros ?. apply to_rep_less_defined. reflexivity.
Qed.

Lemma Transitive_Rep {a b} `{LessDefinedRep a b} `{!Transitive (less_defined (a := b))}
  : Transitive (less_defined (a := a)).
Proof.
  unfold Transitive; intros *. rewrite 3 to_rep_less_defined. apply transitivity.
Qed.

Lemma PreOrder_Rep {a b} `{LessDefinedRep a b} `{!PreOrder (less_defined (a := b))}
  : PreOrder (less_defined (a := a)).
Proof.
  constructor; auto using Reflexive_Rep, Transitive_Rep.
Qed.

Class LubRep a b `{Rep a b,Lub a,Lub b} : Prop :=
  to_rep_lub : forall x y : a, to_rep (lub x y) = lub (to_rep x) (to_rep y).

Lemma to_rep_cobounded {a b} `{LessDefinedRep a b}
  : forall x y : a, Basics.impl (cobounded x y) (cobounded (a := b) (to_rep x) (to_rep y)).
Proof.
  intros x y [z [Hx Hy] ]; exists (to_rep z); rewrite <- 2 to_rep_less_defined; auto.
Qed.

Lemma LubLaw_LubRep {a b} `{LubRep a b,LessDefinedRep a b (REP := _),LL: !LubLaw b} : LubLaw a.
Proof.
  constructor; intros *; rewrite ?to_rep_cobounded, 3? to_rep_less_defined, to_rep_lub; apply LL.
Qed.

(** * Tactics for working with optimistic and pessimistic specs. *)

(** Use the monotonicity laws. *)
Ltac relax :=
  match goal with
  | [ |- _ {{ _ }} ] => eapply pessimistic_mon
  | [ |- _ [[ _ ]] ] => eapply optimistic_mon
  end.
        
Ltac relax_apply lem :=
  match goal with
  | _ => apply lem
  | _ => relax; [apply lem|]
  end.

(** Automatically apply the inference rules. *)
Ltac mforward tac :=
  lazymatch goal with
  | [ |- (ret _) {{ _ }} ] => relax_apply pessimistic_ret
  | [ |- (bind _ _) {{ _ }} ] => relax_apply pessimistic_bind
  | [ |- tick {{ _}} ] => relax_apply pessimistic_tick
  | [ |- (thunk _) {{ _ }} ] => relax_apply pessimistic_thunk
  | [ |- (force _) {{ _ }} ] => relax_apply pessimistic_force
  | [ |- (forcing _ _) {{ _ }} ] => relax_apply pessimistic_forcing
  | [ |- (ret _) [[ _ ]] ] => relax_apply optimistic_ret
  | [ |- (bind _ _) [[ _ ]] ] => relax_apply optimistic_bind
  | [ |- tick [[ _]] ] => relax_apply optimistic_tick
  | [ |- (force _) [[ _ ]] ] => relax_apply optimistic_force
  | [ |- (forcing _ _) [[ _ ]] ] => relax_apply optimistic_forcing
  | [ |- (thunk _) [[ _ ]] ] => fail
  | [ |- (fun _ _ => False) {{ _ }} ] => intros ? ? []
  | [ |- _ {{ _ }} ] => autounfold; tac
  | [ |- _ [[ _ ]] ] => autounfold; tac
  end.

(** Heuristics for dealing with approximations. *)
Ltac invert_approx :=
  match goal with
  | [H : _ `less_defined` _ |- _] =>
    inversion H; let n:= numgoals in guard n=1; subst; clear H
  | [H : is_defined ?x |- _] =>
    destruct x; [|contradiction]; clear H
  end.

Ltac invert_eq :=
  subst; try match goal with
             | [H : _ = _ |- _] =>
               inversion H; subst; clear H
             end.

Ltac solve_approx :=
  repeat (match goal with
          | _ => solve [reflexivity | eauto]
          | [ |- _ `less_defined` _ ] => progress (autorewrite with exact) + (constructor; cbn)
          | [ |- is_defined (Thunk _) ] =>
            reflexivity
          end).

(** Heuristics for reasoning about pessimistic/optimistic specs. *)
Ltac mgo tac := repeat (intros;
                        repeat invert_eq; repeat invert_approx;
                        cbn in *; (mforward tac + solve_approx + lia)).
Ltac mgo' := mgo idtac.
Ltac mgo_ := repeat (intros; cbn in *; (mforward idtac + solve_approx + lia)).

(** Right now is_approx x y is defined as x `less_defined` exact y.
  Having is_approx as a separate primitive may be necessary to generalize
  ApproxAlgebra to infinite values (streams and functions). *)
Module IsApprox.

Class IsApprox (a e : Type) : Type :=
  is_approx : a -> e -> Prop.

Declare Scope approx_scope.
Delimit Scope approx_scope with approx.
#[local] Open Scope approx_scope.

Infix "`is_approx`" := is_approx : approx_scope.

#[global] Instance IsApprox_prod {a ea b eb} `{IsApprox a ea, IsApprox b eb}
  : IsApprox (a * b) (ea * eb) :=
  pair_rel is_approx is_approx.

#[global] Instance IsApprox_fun {a ea b eb} `{IsApprox a ea, IsApprox b eb}
  : IsApprox (a -> b) (ea -> eb) :=
  fun f ef => resp is_approx is_approx f ef.

#[global] Instance IsApprox_M {a e : Type} `{IsApprox a e} : IsApprox (M a) e :=
  fun u ex => u {{ fun x _ => x `is_approx` ex }}.

#[global] Instance Lub_M {a} `{Lub a} : Lub (M a) :=
  fun u u' => fun x n => u x n \/ u' x n.

#[global] Instance Bottom_M {a} : Bottom (M a) := fun _ _ => False.

End IsApprox.

