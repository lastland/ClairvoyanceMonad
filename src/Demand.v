(** * The category of demand functions *)

(** The naive demand functions in LazyQueue have types of the form
    [input -> outputA -> nat * inputA].
    But to be able to define a total translation of the lazy lambda calculus,
    we need a CCC. The definition of exponential objects necessitates
    a more elaborate representation, as [input -> outputA -> M inputA].  *)

From Coq Require Import Setoid SetoidClass Morphisms Lia Arith.
From Clairvoyance Require Import Core Approx ApproxM.

Class IsApprox (a e : Type) : Type :=
  is_approx : a -> e -> Prop.

Declare Scope approx_scope.
Delimit Scope approx_scope with approx.
#[local] Open Scope approx_scope.

Infix "`is_approx`" := is_approx : approx_scope.

#[global] Instance IsApprox_prod {a ea b eb} `{IsApprox a ea, IsApprox b eb}
  : IsApprox (a * b) (ea * eb) :=
  pair_rel is_approx is_approx.

Notation resp r1 r2 f f' := (forall x x', r1 x x' -> r2 (f x) (f' x')) (only parsing).

#[global] Instance IsApprox_fun {a ea b eb} `{IsApprox a ea, IsApprox b eb}
  : IsApprox (a -> b) (ea -> eb) :=
  fun f ef => resp is_approx is_approx f ef.

#[global] Instance LessDefined_fun {a b} `{LessDefined a, LessDefined b}
  : LessDefined (a -> b) :=
  fun f f' => resp less_defined less_defined f f'.

#[global] Instance Lub_fun {a b} `{Lub b} : Lub (a -> b) :=
  fun f f' x => lub (f x) (f' x).

#[global] Instance Bottom_fun {a b} `{Bottom b} : Bottom (a -> b) := fun _ => bottom.

#[global] Instance IsApprox_M {a e : Type} `{IsApprox a e} : IsApprox (M a) e :=
  fun u ex => u {{ fun x _ => x `is_approx` ex }}.

#[global] Instance Lub_M {a} `{Lub a} : Lub (M a) :=
  fun u u' => fun x n => u x n \/ u' x n.

#[global] Instance Bottom_M {a} : Bottom (M a) := fun _ _ => False.

(** * Approximation algebras *)

Module Export AA.

Class Laws e a `{LessDefined a,Lub a,IsApprox a e} : Prop :=
  { PreOrder_less_defined :> PreOrder (less_defined (a := a))
  }.

(* We make the carrier a setoid to get a CCC. Otherwise, function types
   are only exponentials up to functional extensionality. *)
Record ApproximationAlgebra : Type :=
  { carrier :> Type
  ; Setoid_AA : Setoid carrier
  ; approx : Type
  ; LessDefined_AA : LessDefined approx
  ; Lub_AA : Lub approx
  ; Bottom_AA : Bottom approx
  ; IsApprox_AA : IsApprox approx carrier
  ; laws : Laws carrier approx
  }.

End AA.

Notation AA := ApproximationAlgebra (only parsing).

#[global] Existing Instance Setoid_AA.
#[global] Existing Instance LessDefined_AA.
#[global] Existing Instance Lub_AA.
#[global] Existing Instance Bottom_AA.
#[global] Existing Instance IsApprox_AA.
#[global] Existing Instance AA.laws.

(* TODO: Move out *)
Module Export Setoid_.

Record SetoidMorphism (a b : Type) `{Setoid a, Setoid b} : Type :=
  { apply :> a -> b
  ; Proper_SM : Proper (equiv ==> equiv) apply
  }.

Arguments apply {a b _ _}.

#[global,refine] Instance Setoid_SM {a b} `{Setoid a,Setoid b} : Setoid (SetoidMorphism a b) :=
  {| equiv f f' := resp equiv equiv (apply f) (apply f') |}.
Proof.
  1,2: assumption.
  constructor.
  - intros ?. apply Proper_SM.
  - intros ? ?. intros ? * Hx. symmetry. symmetry in Hx. auto.
  - intros ? ? ? Hf Hf2 * Hx. etransitivity; [ apply Hf; reflexivity | apply Hf2; assumption ].
Defined.

Declare Scope setoid_scope.
Delimit Scope setoid_scope with setoid.
#[global] Open Scope setoid_scope.

Infix "~->" := SetoidMorphism (at level 90) : setoid_scope.

Definition id_SM a `{Setoid a} : a ~-> a :=
  {| apply := fun x => x
  ;  Proper_SM _ _ H := H |}.

Definition compose_SM {a b c} `{Setoid a,Setoid b,Setoid c} (f : a ~-> b) (g : b ~-> c) : a ~-> c :=
  {| apply x := g (f x)
  ;  Proper_SM _ _ H := Proper_SM _ _ g _ _ (Proper_SM _ _ f _ _ H) |}.

End Setoid_.

(** * Demand functions *)

(*
Record Tick (a : Type) : Type := MkTick
  { cost : nat
  ; val : a
  }.

Arguments MkTick {a}.
Arguments cost {a}.
Arguments val {a}.

#[global] Instance LessDefined_Tick {a} `{LessDefined a} : LessDefined (Tick a) :=
  fun x y => cost x <= cost y /\ val x `less_defined` val y.

#[global] Instance Transitive_LessDefined_Tick {a} `{LessDefined a}
  `{!Transitive (less_defined (a := a))} : Transitive (less_defined (a := Tick a)).
Proof.
  unfold Transitive, less_defined, LessDefined_Tick; intros * [] []; split; etransitivity; eauto.
Qed.
*)

Module Export DFun.

Class Laws {a1 ea1 a2 : Type} `{LessDefined a1, LessDefined a2}
    (df : ea1 -> a2 -> M a1) : Prop :=
  { dfun_monotone :> Proper (eq ==> less_defined ==> less_defined) df }.

(* Demand functions must be nondeterministic in general to be able to define [lub] *)
Record DFun (a1 a2 : AA) : Type :=
  { dfun :> a1 -> approx a2 -> M (approx a1)
  ; laws : Laws dfun }.

#[global] Existing Instance laws.

Arguments dfun {a1 a2}.

#[global] Instance LessDefined_DFun {a1 a2 : AA} : LessDefined (DFun a1 a2) :=
  fun f f' => forall x, dfun f x `less_defined` dfun f' x.

#[global] Instance PreOrder_LessDefined_DFun {a1 a2 : AA} : PreOrder (less_defined (a := DFun a1 a2)).
Proof.
  unfold less_defined, LessDefined_DFun.
  constructor.
  - red. red. red. intros *; apply dfun_monotone; auto.
  - red. red. red. intros.
    etransitivity. eapply H; reflexivity. eapply H0. auto.
Qed.

Definition is_approx_DFun {a1 ea1 a2 ea2 : Type} `{IsApprox a1 ea1, IsApprox a2 ea2}
    (df : ea1 -> a2 -> M a1) (f : ea1 -> ea2) :=
  forall (x : ea1) (outD : a2),
      outD `is_approx` f x -> df x outD `is_approx` x.

#[global] Instance IsApprox_DFun {a1 a2 : AA} : IsApprox (DFun a1 a2) (a1 ~-> a2) :=
  is_approx_DFun.

#[local] Instance Laws_Lub_DFun {a1 a2 : AA} (f f' : DFun a1 a2) : Laws (lub (dfun f) (dfun f')).
Proof.
Admitted.

#[global] Instance Lub_DFun {a1 a2 : AA} : Lub (DFun a1 a2) :=
  fun f f' => {| dfun := lub (dfun f) (dfun f') |}.

#[local] Instance Laws_Bottom_DFun {a1 a2 : AA}
  : Laws (a1 := approx a1) (ea1 := a1) (a2 := approx a2) bottom.
Proof.
Admitted.

#[global] Instance Bottom_DFun {a1 a2 : AA} : Bottom (DFun a1 a2) :=
  {| dfun := bottom |}.

Definition id_DFun (a : AA) : DFun a a.
Admitted.

Definition compose_dfun {a b c : AA} (f : a -> b) (df : DFun a b) (dg : DFun b c)
  : a -> approx c -> M (approx a) :=
  fun x' z =>
    let! y := dg (f x') z in
    df x' y.

Instance Laws_compose_dfun {a b c : AA} (f : a -> b) (df : DFun a b) (dg : DFun b c)
  : DFun.Laws (compose_dfun f df dg).
Admitted.

Definition compose_DFun {a b c : AA} (f : a -> b) (df : DFun a b) (dg : DFun b c)
  : DFun a c :=
  {| dfun := compose_dfun f df dg |}.

End DFun.

Module Export AAM.

Class Laws {a1 a2 : AA}
    (apply : a1 ~-> a2) (coapply : DFun a1 a2) : Prop :=
  { coapply_approx : is_approx coapply apply
  }.

Record AAMorphism (a1 a2 : AA) : Type :=
  { apply :> a1 ~-> a2
  ; coapply : DFun a1 a2
  ; laws : Laws apply coapply
  }.

End AAM.

Arguments Build_AAMorphism a1 a2 &.
Arguments apply {a1 a2}.
Arguments coapply {a1 a2}.

#[global] Existing Instance AAM.laws.

Lemma AAMLaws_id (a : AA) : @AAM.Laws a a (id_SM a) (id_DFun a).
Proof.
  constructor.
Admitted.

Definition AAMorphism_id (a : AA) : AAMorphism a a :=
  {| apply := id_SM a
  ;  coapply := id_DFun a
  ;  laws := AAMLaws_id a
  |}.

Lemma AAMLaws_compose {a b c : AA} (f : AAMorphism a b) (g : AAMorphism b c)
  : AAM.Laws (compose_SM f g) (compose_DFun (apply f) (coapply f) (coapply g)).
Proof.
  constructor.
Admitted.

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

#[global] Instance Laws_AAExp (a1 a2 : AA) : AA.Laws (a1 ~-> a2) (DFun a1 a2).
Proof.
  constructor.
  - exact _.
Qed.

Definition AAExp (a1 a2 : AA) : AA :=
  {| carrier := a1 ~-> a2
  ; approx := DFun a1 a2
  |}.

#[global] Instance Reflexive_pair_rel {a b} (r1 : relation a) (r2 : relation b)
    `{!Reflexive r1, !Reflexive r2} : Reflexive (pair_rel r1 r2).
Proof. constructor; reflexivity. Qed.

#[global] Instance Symmetric_pair_rel {a b} (r1 : relation a) (r2 : relation b)
    `{!Symmetric r1, !Symmetric r2} : Symmetric (pair_rel r1 r2).
Proof. constructor; symmetry; apply H. Qed.

#[global] Instance Transitive_pair_rel {a b} (r1 : relation a) (r2 : relation b)
    `{!Transitive r1, !Transitive r2} : Transitive (pair_rel r1 r2).
Proof. constructor; etransitivity; apply H + apply H0. Qed.

#[global] Instance Equivalence_pair_rel {a b} (r1 : relation a) (r2 : relation b)
    `{!Equivalence r1, !Equivalence r2}
  : Equivalence (pair_rel r1 r2).
Proof. constructor; exact _. Qed.

#[global] Instance Setoid_prod {a b} `{Setoid a, Setoid b} : Setoid (a * b) :=
  {| equiv := pair_rel equiv equiv |}.

#[global] Instance Laws_AAProd (a1 a2 : AA) : AA.Laws (a1 * a2) (approx a1 * approx a2).
Proof.
  constructor.
  - exact _.
Qed.

Definition AAProd (a1 a2 : AA) : AA :=
  {| carrier := a1 * a2
  ;  approx := approx a1 * approx a2
  |}.

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
