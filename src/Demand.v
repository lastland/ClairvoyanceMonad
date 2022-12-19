(** * The category of demand functions *)

(** The naive demand functions in BankersQueue have types of the form
    [input -> outputA -> nat * inputA].
    But to be able to define a total translation of the lazy lambda calculus,
    we need a CCC. The definition of exponential objects necessitates
    a more elaborate representation, as [input -> outputA -> M inputA].  *)

From Coq Require Import Setoid SetoidClass Morphisms Lia Arith.
From Clairvoyance Require Import Core Approx ApproxM Relations Setoid Tick.

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

Section Cartesian.

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

End Cartesian.

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
