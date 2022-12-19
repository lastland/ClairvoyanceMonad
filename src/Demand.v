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

Record ApproxAlgebra : Type :=
  { carrier :> Type
  ; AA_Setoid : Setoid carrier
  ; approx : Type
  ; AA_IsAA :> IsApproxAlgebra carrier approx
  }.

End AA.

Notation AA := ApproxAlgebra (only parsing).

#[global] Existing Instance AA_Setoid.
#[global] Existing Instance AA_IsAA.

Definition AAProd (a1 a2 : AA) : AA :=
  {| carrier := a1 * a2
  ;  approx := approx a1 * approx a2
  |}.


(** * Demand functions *)

Module Export DFun.

Class Laws {a' a b : Type} `{Setoid a', LessDefined a, LessDefined b}
    (df : a' -> b -> Tick a) : Prop :=
  { dfun_monotone : Proper (equiv ==> less_defined ==> less_defined) df }.

#[global] Existing Instance dfun_monotone.

(* Demand functions must be nondeterministic in general to be able to define [lub] *)
Record DFun (a1 a2 : AA) : Type :=
  { dfun :> a1 -> approx a2 -> Tick (approx a1)
  ; laws : Laws dfun }.

#[global] Existing Instance laws.

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
Instance Laws_id (a : AA) : Laws (id_dfun a).
Proof.
  constructor. unfold Proper, respectful, id_dfun.
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
Instance Laws_compose_dfun {a b c : AA} (f : a ~-> b) (df : DFun a b) (dg : DFun b c)
  : DFun.Laws (compose_dfun f df dg).
Proof.
  constructor. unfold Proper, respectful, compose_dfun.
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
