(** * The category of demand functions *)

(** The naive demand functions in BankersQueue have types of the form
    [input -> outputA -> nat * inputA].
    But to be able to define a total translation of the lazy lambda calculus,
    we need a CCC. The definition of exponential objects necessitates
    a more elaborate representation, as [input -> outputA -> M inputA].  *)

From Coq Require Import Setoid SetoidClass Morphisms Lia Arith List.
From Equations Require Import Equations.
From Clairvoyance Require Import Core Approx List ApproxM Relations Setoid Tick Misc ListA.

Set Warnings "-redundant-canonical-projection".

Import ListNotations.

Import Tick.Notations.
#[local] Open Scope tick_scope.

Parameter TODO : forall {P : Type}, P.

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
  ; AA_Setoid :> Setoid carrier
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

#[global] Instance BottomOf_listA {a : Type} {H : BottomOf a} : BottomOf (listA a) :=
  fun xs => match xs with NilA => NilA | ConsA x xs => ConsA Undefined Undefined end.

#[global] Instance BottomIsLeast_listA {a : Type} {H : BottomOf a} {H0 : LessDefined a}
  : BottomIsLeast a -> BottomIsLeast (listA a).
Proof.
  intros ? ? ? HH; inv HH; repeat constructor.
Qed.

(*
#[global] Instance IsAA_listA' {a' a} {_ : IsAA a' a} : IsAA (list a') (listA a).
Proof.
  econstructor; try typeclasses eauto.
Defined.
*)

#[global] Instance IsAA_T {a' a} {_ : IsAA a' a} : IsAA a' (T a).
Proof.
  econstructor; try typeclasses eauto.
Defined.

#[global] Instance IsAA_listA {a' a} {_ : IsAA a' a} : IsAA (list a') (T (listA a)).
Proof.
  econstructor; try typeclasses eauto.
Defined.

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
Canonical AA_bool : AA := exact_AA bool.

Module OTick.
Definition OTick (a : Type) : Type := option (Tick a).

Definition ret {a : Type} (x : a) : OTick a :=
  Some (Tick.ret x).

Definition bind {a b : Type} (ox : OTick a) (k : a -> OTick b) : OTick b :=
  match ox with
  | None => None
  | Some x => match k (Tick.val x) with
              | None => None
              | Some y => Some (Tick.MkTick (Tick.cost x + Tick.cost y) (Tick.val y))
              end
  end.

Definition fail {a : Type} : OTick a := None.

(* Weakest precondition transformer *)
Definition wp {a : Type} (P : nat -> a -> Prop) (ox : OTick a) : Prop :=
  match ox with
  | None => False
  | Some x => P (Tick.cost x) (Tick.val x)
  end.

Definition tick_wp2 {a b : Type} (P : a -> b -> Prop) (ox : Tick a) (oy : Tick b) : Prop :=
  Tick.cost ox <= Tick.cost oy /\ P (Tick.val ox) (Tick.val oy).

Definition wp2 {a b : Type} (P : a -> b -> Prop) (ox : OTick a) (oy : OTick b) : Prop :=
  match ox, oy with
  | Some x, Some y => tick_wp2 P x y
  | _, _ => False
  end.

(* Ordering between OTick computations *)
#[global] Instance LessDefined_OTick {a : Type} `{LessDefined a} : LessDefined (OTick a) :=
  wp2 less_defined.

Theorem wp_ret {a : Type} (P : nat -> a -> Prop) (x : a) : P 0 x -> wp P (ret x).
Proof.
  exact (fun x => x).
Qed.

Definition wp_bind {a b : Type} (P : nat -> b -> Prop) (ox : OTick a) (k : a -> OTick b)
  : wp (fun n x => wp (fun m => P (n + m)) (k x)) ox -> wp P (OTick.bind ox k).
Proof.
  destruct ox; cbn; [ | auto ].
  destruct k; cbn; auto.
Qed.

Definition wp_mono {a : Type} {P Q : nat -> a -> Prop} {ox : OTick a}
  : (forall n x, P n x -> Q n x) -> wp P ox -> wp Q ox.
Proof.
  destruct ox; cbn; auto.
Qed.

Definition wp2_mono {a b : Type} {P Q : a -> b -> Prop} {ox : OTick a} {oy : OTick b}
  : (forall x y, P x y -> Q x y) -> wp2 P ox oy -> wp2 Q ox oy.
Proof.
  destruct ox; cbn; [ | contradiction ].
  destruct oy; cbn; [ | contradiction ].
  intros HPQ HP; constructor; [ | apply HPQ ]; apply HP.
Qed.

(*
Definition wp2_wp_l {a b : Type} {P : a -> Prop} {Q : a -> b -> Prop} {ox : OTick a} {oy : OTick b}
  : wp P ox -> wp2 (fun x y => P x -> Q x y) ox oy -> wp2 Q ox oy.
Proof.
  destruct ox; cbn; [ | contradiction ].
  destruct oy; cbn; [ | contradiction ].
  intros HP HPQ; constructor; apply HPQ; apply HP.
Qed.

Definition wp2_wp_r {a b : Type} {P : b -> Prop} {Q : a -> b -> Prop} {ox : OTick a} {oy : OTick b}
  : wp P oy -> wp2 (fun x y => P y -> Q x y) ox oy -> wp2 Q ox oy.
Proof.
  destruct ox; cbn; [ | contradiction ].
  destruct oy; cbn; [ | contradiction ].
  intros HP HPQ; constructor; apply HPQ; apply HP.
Qed.
*)

Theorem wp2_ret {a b : Type} {P : a -> b -> Prop} {x y}
  : P x y -> wp2 P (ret x) (ret y).
Proof.
  cbn; unfold tick_wp2; cbn. auto.
Qed.

Theorem wp2_bind {a b : Type}
    (P : b -> b -> Prop)
    (ox ox' : OTick a) (k k' : a -> OTick b)
  : wp2 (fun x x' => wp2 P (k x) (k' x')) ox ox' ->
    wp2 P (bind ox k) (bind ox' k').
Proof.
Admitted.

End OTick.

Notation OTick := OTick.OTick.

Definition RawDF (a' b' : Type) : Type := b' -> OTick a'.

Record IsDF {a b : AA} (x : a) (y : b) (f : RawDF (approx a) (approx b)) : Prop :=
  { exact_apply : forall y',
      y' `less_defined` exact y ->
      OTick.wp (fun n x' => x' `less_defined` exact x) (f y')
  ; less_defined_apply : forall y1' y2',
      y1' `less_defined` y2' ->
      y2' `less_defined` exact y ->
      f y1' `less_defined` f y2' }.

(* Demand functions. We make the approximation types explicit because there may be more
   than one (a', b') for each (a, b) (notably IsAA a a' -> Is a (T a')) *)
Record DF {a b : AA} (x : a) (y : b) : Type :=
  { apply :> RawDF (approx a) (approx b)
  ; isDF :> IsDF x y apply }.

Arguments DF {a} {b} x y.
Arguments apply {a b x y} _.
Arguments exact_apply {a b x y f} _.
Arguments less_defined_apply {a b x y f} _.
(* DF is only the backwards direction.
It's a category but its objects are terms rather than types.

We can pair it with a forward function to construct
a category whose objects are types:

a ~> b = { f : a -> b | forall x, DF x (f x) }
*)

Generalizable All Variables.
Implicit Types a b c : AA.

Module DF.

Definition Raw_id {a : Type} : RawDF a a :=
  fun x => OTick.ret x.

Theorem IsDF_id {a : AA} {x : a} : IsDF x x Raw_id.
Proof.
  constructor.
  - cbn. auto.
  - cbn. intros. apply less_defined_ret. assumption.
Qed.

Definition id {a : AA} (x : a) : DF x x :=
  {| isDF := IsDF_id |}.

Definition Raw_compose {a b c : Type} (f : RawDF a b) (g : RawDF b c) : RawDF a c :=
  fun z' => OTick.bind (g z') (fun y' => f y').

Theorem IsDF_compose {a b c : AA} {x : a} {y : b} {z : c}
  `(Hf : IsDF x y f) `(Hg : IsDF y z g) : IsDF x z (Raw_compose f g).
Proof.
  constructor.
  - unfold Raw_compose. intros z' Hz; apply OTick.wp_bind.
    refine (OTick.wp_mono _ (exact_apply Hg _ Hz)).
    intros ny y' Hy. refine (OTick.wp_mono _ (exact_apply Hf _ Hy)).
    auto.
  - unfold Raw_compose. intros y1' y2' H1 H2.
    apply OTick.wp2_bind.
Admitted. (*
    apply (OTick.wp2_wp_r (exact_apply Hg _ H2)).
    refine (OTick.wp2_mono _ (less_defined_apply Hg _ _ H1 H2)).
    apply Hf.
Qed.
*)

Definition compose {a b c : AA} {x : a} {y : b} {z : c}
  (f : DF x y) (g : DF y z) : DF x z :=
  {| isDF := IsDF_compose f g |}.

Module Import Notations.

Declare Scope df_scope.
Delimit Scope df_scope with df.
Bind Scope df_scope with DF.

Infix ">>>" := compose (left associativity, at level 40) : df_scope.

End Notations.

Section Product.

Definition Raw_proj1 {a' b b' : Type} `{BottomOf b', Exact b b'} (y : b) : RawDF (a' * b') a' :=
  fun (x' : a') => OTick.ret (x', bottom_of (exact y)).

Theorem IsDF_proj1 {a b : AA} {x : a} {y : b} : IsDF (x, y) x (Raw_proj1 y).
Proof.
  constructor.
  - apply TODO.
  - apply TODO.
Qed.

Definition proj1 {a b : AA} {x : a} {y : b} : DF (x, y) x :=
  {| isDF := IsDF_proj1 |}.

Definition Raw_proj2 {a a' b' : Type} `{BottomOf a', Exact a a'} (x : a) : RawDF (a' * b') b' :=
  fun (y' : b') => OTick.ret (bottom_of (exact x), y').

Theorem IsDF_proj2 {a b : AA} {x : a} {y : b} : IsDF (x, y) y (Raw_proj2 x).
Proof.
  constructor.
  - apply TODO.
  - apply TODO.
Qed.

Definition proj2 {a b : AA} {x : a} {y : b} : DF (x, y) y :=
  {| isDF := IsDF_proj2 |}.

Definition Raw_pair {a' b' c' : Type} `{Lub a'} (f : RawDF a' b') (g : RawDF a' c') : RawDF a' (b' * c') :=
  fun '(y', z') =>
    OTick.bind (f y') (fun x1 : a' =>
    OTick.bind (g z') (fun x2 : a' =>
    OTick.ret (lub x1 x2))).

Theorem IsDF_pair {a b c : AA} {x : a} {y : b} {z : c}
  `(Hf : IsDF x y f) `(Hg : IsDF x z g) : IsDF x (y, z) (Raw_pair f g).
Proof.
Admitted. (*
  constructor.
  - unfold Raw_pair. intros [y' z'] [Hy Hz]; cbn in Hy, Hz.
    apply OTick.wp_bind.
    refine (OTick.wp_mono _ (exact_apply Hf _ Hy)). intros x1 Hx1.
    apply OTick.wp_bind.
    refine (OTick.wp_mono _ (exact_apply Hg _ Hz)). intros x2 Hx2.
    apply OTick.wp_ret.
    apply lub_least_upper_bound; auto.
  - intros [y1 z1] [y2 z2] [Hy1 Hz1] [Hy2 Hz2]; cbn in Hy1, Hz1, Hy2, Hz2 |- *.
    apply OTick.wp2_bind.
    apply (OTick.wp2_wp_r (exact_apply Hf _ Hy2)).
    refine (OTick.wp2_mono _ (less_defined_apply Hf _ _ Hy1 Hy2)).
    intros x1 x1' Hx1 Hx1'.
    apply OTick.wp2_bind.
    refine (OTick.wp2_mono _ (less_defined_apply Hg _ _ Hz1 Hz2)).
    intros x2 x2' Hx2.
    apply OTick.wp2_ret.
    apply TODO. (* TODO: move Proper_lub to IsAA *)
Defined. *)

Definition pair `{x : a, y : b, z : c} `(f : DF x y) `(g : DF x z) : DF x (y, z) :=
  {| isDF := IsDF_pair f g |}.

End Product.

Section Misc.

Definition Raw_tick {a' b' : Type} (f : RawDF a' b') : RawDF a' b' :=
  fun (y' : b') => option_map (fun o => Tick.tick >> o) (f y').

Theorem IsDF_tick {a b : AA} {x : a} {y : b} `(IsDF x y f) : IsDF x y (Raw_tick f).
Admitted.

Definition tick `{x : a, y : b} `(f : DF x y) : DF x y :=
  {| isDF := IsDF_tick f |}.

Definition bind `{x : a, y : b, z : c} `(f : DF x y) `(g : DF (x, y) z) : DF x z :=
  pair (id x) f >>> g.

End Misc.

Notation let_ := bind.

Definition if_ {G A : AA} {g : G} {b : bool} {P : bool -> A}
    (CASE : DF g b)
    (TRUE : DF g (P true))
    (FALSE : DF g (P false))
  : DF g (P b) :=
  match b with
  | true => TRUE
  | false => FALSE
  end.

End DF.

Import DF.Notations.
#[local] Open Scope df.

(* Auxiliary definition for match_list *)
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

(* Auxiliary definition for match_list *)
Definition force_cons {G A : AA} {g : G} {x : A} {xs : list A}
  : DF (g, cons x xs) (g, cons x xs, x, xs).
Admitted.

(*
  Gamma |- A + B
  Gamma, A |- C
  Gamma, B |- C
  -----
  Gamma |- C
*)

Definition match_list {G A B : AA} {P : list A -> B} {g : G} {xs : list A}
    (CASE : DF g xs)
    (NIL : DF (g, []) (P []))
    (CONS : forall x ys, DF (g, x :: ys, x, ys) (P (x :: ys)))
  : DF g (P xs) :=
  DF.bind CASE
  match xs with
  | [] => NIL
  | x :: xs => force_cons >>> CONS x xs
  end.

Definition nilD {G a : AA} {g : G} : DF g (nil (A := a)).
Admitted.

Definition consD {G A : AA} {g : G} {x : A} {xs : list A}
  : DF g x -> DF g xs -> DF g (x :: xs).
Admitted.

Fixpoint append {a} (xs ys : list a) : list a :=
  match xs with
  | nil => ys
  | cons x xs1 => x :: append xs1 ys
  end.

Class AutoDF {A B : AA} (x : A) (y : B) : Type :=
  autoDF : DF x y.

#[global]
Hint Mode AutoDF ! ! ! ! : typeclass_instances.

#[global] Instance AutoDF_snd {A B : AA} {x : A} {y : B} : AutoDF (x, y) y :=
  DF.proj2.

#[global] Instance AutoDF_fst {A B C : AA} {x : A} {y : B} {z : C}
  `{AutoDF _ _ x z} : AutoDF (x, y) z :=
  DF.proj1 >>> autoDF.

#[global] Instance AutoDF_id {A : AA} {x : A} : AutoDF x x := DF.id _.

#[global] Instance AutoDF_pair {A B C : AA} {x : A} {y : B} {z : C}
  `{AutoDF _ _ x y, AutoDF _ _ x z} : AutoDF x (y, z) | 0 :=
  DF.pair autoDF autoDF.

Definition var {G A : AA} {g : G} (x : A) `{AutoDF _ _ g x} : DF g x := autoDF.
Definition call {G1 G2 A : AA} {g1 : G1} {g2 : G2} {x : A} `{AutoDF _ _ g2 g1} (f : DF g1 x)
  : DF g2 x := autoDF >>> f.

Fixpoint appendDF {a : AA} (xs ys : list a) : DF (xs, ys) (xs ++ ys) :=
  DF.tick
  (match_list (P := fun xs => xs ++ ys) (var xs)
    (var ys)
    (fun x xs1 => consD (var x) (call (appendDF xs1 ys)))
  ).

Definition predDF {a : AA} {g : a} {n : nat} : DF (g, (S n)) (g, n).
Admitted.

Definition match_nat {G a : AA} {g : G} (f : nat -> a) {n : nat}
    (CASE : DF g n)
    (ZERO : DF g (f O))
    (SUCC : forall n', DF (g, n') (f (S n')))
  : DF g (f n) :=
  DF.bind CASE
  match n with
  | O => DF.proj1 >>> ZERO
  | S n' => predDF >>> SUCC n'
  end.

Fixpoint dropDF {a : AA} (n : nat) (xs : list a) : DF (n, xs) (drop n xs) :=
  DF.tick
  (match_nat (fun n => drop n xs) (var n)
    (* 0 => xs *)
    (var xs)
    (* S n => ... *)
    (fun n => match_list (P := fun xs => drop (S n) xs) (var xs)
      nilD
      (fun x xs => call (dropDF n xs))
    )).

(*
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
Class Accountable (a : Type) `{HasAA a} : Type :=
  { account : a -> Type
  ; credits : forall {x : a}, account x -> approx a -> nat
  ; credits_lub : forall {x : a} {x1 x2 : approx a} (p : account x),
      x1 `less_defined` exact x ->
      x2 `less_defined` exact x ->
      credits p (lub x1 x2) <= credits p x1 + credits p x2
  ; credits_bottom : forall {x : a} (p : account x),
      credits p (bottom_of (exact x)) = 0
  }.
(* Morally, the approximation should be less than x,
   but we don't need a proof as an argument because
   we can just return 0 in the bad cases. *)

Declare Scope account_scope.
Delimit Scope account_scope with account.
Bind Scope account_scope with account.

Definition credits_T {a : Type} (c : a -> nat) (x : T a) : nat :=
  match x with
  | Undefined => 0
  | Thunk x => c x
  end.

(* We store one [nat] for each constructor, including [nil].
   For simplicity, we do not store credits in [a];
   we could.
 *)
Fixpoint account_list {a : Type} (xs : list a) : Type :=
  match xs with
  | [] => nat
  | x :: xs => nat * account_list xs
  end.

(* Sum of the credits used by an approximation of a list [xs]. *)
Fixpoint credits_list {a : Type} `{HasAA a}
   {xs : list a} (cs : account_list xs) (xs' : approx (list a)) : nat :=
  match xs, cs, xs' with
  | [], c, NilA => c
  | x :: xs, (c, cs), ConsA x' xs' => c + credits_T (credits_list cs) xs'
  | _, _, _ => 0
  end.

#[global]
Instance Accountable_list {a} `{HasAA a} : Accountable (list a) :=
  {| account := account_list
  ;  credits := fun xs => credits_list (xs := xs)
  ;  credits_lub := TODO
  ;  credits_bottom := TODO
  |}.

Inductive Zero : Type := Z.

#[global]
Instance Accountable_pair {a b : Type} `{Accountable a, Accountable b} : Accountable (a * b) :=
  {| account := fun (xy : a * b) => (account (fst xy) * account (snd xy))%type
  ;  credits := fun xy cd uv => credits (fst cd) (fst uv) + credits (snd cd) (snd uv)
  ;  credits_lub := TODO
  ;  credits_bottom := TODO
  |}.

#[global]
Instance Accountable_lazypair {a b : Type} `{Accountable a, Accountable b} : Accountable (lazyprod a b) :=
  {| account := fun (xy : lazyprod a b) => (account (lazyfst xy) * account (lazysnd xy))%type
  ;  credits := fun (xy : lazyprod a b) cd uv => credits (fst cd) (fst uv) + credits_T (credits (snd cd)) (snd uv)
  ;  credits_lub := TODO
  ;  credits_bottom := TODO
  |}.

#[global]
Instance Accountable_unit : Accountable unit :=
  {| account := fun _ => unit
  ;  credits := fun _ _ _ => 0
  ;  credits_lub := TODO
  ;  credits_bottom := TODO
  |}.

Definition OTick_credits {a : Type} (c : a -> nat) (u : OTick a) : nat :=
  match u with
  | None => 0
  | Some v => c (Tick.val v) + Tick.cost v
  end.

Definition has_cost `{Accountable a, Accountable b} {x : a} {y : b}
    (f : embedDF x y) (n : nat) (p : account x) (q : account y)
  : Prop :=
  forall y', y' `less_defined` exact y ->
    OTick_credits (credits p) (apply f y') <= n + credits q y'.

Definition map_account_head `{HasAA a} (f : nat -> nat) {xs : list a} (cs : account xs)
  : account xs :=
  match xs, cs with
  | [], c => f c
  | x :: xs, (c, cs) => (f c, cs)
  end.

Fixpoint append_account `{HasAA a}
    {xs : list a} (cs : account xs)
    {ys : list a} (ds : account ys)
  : account (xs ++ ys) :=
  match xs, cs, ys, ds with
  | [], c, _, _ => map_account_head (fun d => c + d) ds
  | x :: xs, (c, cs), ys, ds => (c, append_account cs ds)
  end.

Infix "++" := append_account : account_scope.

Fixpoint map_account `{HasAA a} (f : nat -> nat) {xs : list a} (cs : account xs)
  : account xs :=
  match xs, cs with
  | [], c => f c
  | x :: xs, (c, cs) => (f c, map_account f cs)
  end.

Theorem has_cost_tick `{Accountable a, Accountable b} {x : a} {y : b}
    (f : embedDF x y) (n : nat) (p : account x) (q q' : account y)
    (TICKY : forall y', y' `less_defined` exact y -> S (credits q y') = credits q' y')
  : has_cost f n p q -> has_cost (EmbedDF.tick f) n p q'.
Proof.
Admitted.

Lemma account_head_ticky `{Accountable a, HasAA b} {x : a} {ys : list b}
    {f : embedDF x ys} (n : nat) {p : account x} {q : account ys}
  : has_cost f n p q -> has_cost (EmbedDF.tick f) n p (map_account_head S q).
Proof.
  apply has_cost_tick.
  destruct ys; intros y' Hy'.
Admitted.

Theorem has_cost_match_list `{Accountable G, Accountable a, Accountable b}
    {P : list a -> b} {g : G} {xs : list a}
    {CASE : embedDF g xs}
    {NIL : embedDF g (P [])}
    {CONS : forall x ys, embedDF (g, x, ys) (P (x :: ys))}
    {n : nat}
    (aP : forall xs, account xs -> account (P xs))
    {ag ag' : account g} {axs : account xs}
    {zero : forall x : a, account x}  (* TODO *)
    (H_todo : TODO (* ag <= ag' + anil *))
    (cost_match :
      match xs, axs with
      | [], anil => has_cost NIL (n + anil) ag' (aP [] anil)
      | x :: ys, (acons, ays) =>
        has_cost (CONS x ys) (n + acons) (ag', zero x, ays) (aP (x :: ys) (acons, ays))
      end)
  : has_cost (match_list P CASE NIL CONS) n ag (aP xs axs).
Proof.
Admitted.

Theorem has_cost_match_list_nil `{Accountable G, Accountable a, Accountable b}
    {P : list a -> b} {g : G}
    {CASE : embedDF (b := list a) g []}
    {NIL : embedDF g (P [])}
    {CONS : forall x ys, embedDF (g, x, ys) (P (x :: ys))}
    {n : nat}
    {ag : account g} {anil : account []} {q : account (P [])}
    (cost_match : has_cost NIL (n + anil) ag q)
  : has_cost (match_list P CASE NIL CONS) n ag q.
Proof.
Admitted.

Theorem has_cost_match_list_cons `{Accountable G, Accountable a, Accountable b}
    {P : list a -> b} {g : G} {x : a} {xs : list a}
    {CASE : embedDF (b := list a) g (x :: xs)}
    {NIL : embedDF g (P [])}
    {CONS : forall y ys, embedDF (g, y, ys) (P (y :: ys))}
    {n : nat}
    {ag : account g} {m : nat} {axs : account xs} {q : account (P (x :: xs))}
    {zero : forall x : a, account x}
    (cost_match : has_cost (CONS x xs) (n + m) (ag, zero x, axs) q)
  : has_cost (match_list P CASE NIL CONS) n ag q.
Proof.
Admitted.

(*
Theorem append_cost `{Accountable a} {xs ys : list a} (cs : account xs) (ds : account ys)
  : has_cost (appendDF xs ys)
             0
             (tt, cs, ds)
             (map_account S cs ++ ds).
Proof.
  induction xs; cbn.
  - replace (map_account_head (fun d : nat => S (cs + d)) ds)
    with (map_account_head S (map_account_head (fun d : nat => (cs + d)) ds)); [ | admit ].
    apply account_head_ticky.
    unshelve eapply (has_cost_match_list_nil (P := fun xs => xs ++ ys) (g := (tt, [], ys)%embedDF_context) (anil := cs)).
    + exact TODO.
  - destruct cs; cbn.
Admitted.

(* TODO *)

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

Theorem has_cost_id {a : AA} `{Account a} (x : a) (p : account x)
  : has_cost DF.id p p.
Proof.
  unfold has_cost, cost_with; cbn. lia.
Qed.

Theorem has_cost_proj1 {a b : AA} `{Account a, Account b}
    (x : a) (y : b) (p : account x) (q : account y)
   : has_cost (x' := (x, y)) proj1DF' (p, q) p.
Proof.
  intros []; cbn. rewrite credits_bottom. lia.
Qed.

Theorem has_cost_proj2 {a b : AA} `{Account a, Account b}
    (x : a) (y : b) (p : account x) (q : account y)
   : has_cost (x' := (x, y)) proj2DF' (p, q) q.
Proof.
  intros []; cbn. rewrite credits_bottom. lia.
Qed.

Ltac spec HC1 :=
  match type of HC1 with
  | has_cost ?f _ _ => 
    match goal with
    | [ |- context [ f ?x ] ] =>
      let h := fresh HC1 in
      assert (h := HC1 x); unfold cost_with in h; cbn [proj1_sig] in h
    end
  end.

Theorem has_cost_pair {a b c : AA} `{Account a, Account b, Account c}
    {x : a} {y : b} {z : c} {f : DF x y} {g : DF x z}
    {p : account x} {q : account y} {r : account z}
  : has_cost f p q -> has_cost g p r -> has_cost (pairDF f g) p (q, r).
Proof.
  intros HC1 HC2 [ [] [] ]; cbn in *.
  unfold cost_with; cbn.
  destruct (Tick.val (f _)) eqn:Ef; cbn.
  destruct (Tick.val (g _)) eqn:Eg; cbn.
  rewrite credits_lub; [ | assumption .. ].
  spec HC1.
  spec HC2.
  rewrite <- HC0.
  rewrite <- HC3.
  remember (Tick.cost (f _)).
  remember (Tick.cost (g _)).
  rewrite Ef, Eg; cbn.
  lia.
Qed.

Class AutoHasCost {a b : AA} `{Account a, Account b} {x : a} {y : b} (f : DF x y) (p : account x) (q : account y)
  : Prop :=
  auto_has_cost : has_cost f p q.

#[global]
Instance AutoHasCost_Project_here {a b : AA} `{Account a, Account b}
    (x : a) (y : b) (p : account x) (q : account y)
  : AutoHasCost (x := (x, y)) (y := y) (project y) (p, q) q.
Proof.
  unfold project, Project_here. apply has_cost_proj2.
Qed.

#[global]
Instance AutoHasCost_Project_here1 {a : AA} `{Account a}
    (x : a) (p : account x)
  : AutoHasCost (x := x) (project x) p p.
Proof.
  unfold AutoHasCost. apply has_cost_id.
Qed.

#[global]
Instance AutoHasCost_Project_there {a b c : AA} (x : a) (y : b) (z : c)
    `{Account a, Account b, Account c}
    (p : account x) (q : account y) (r : account z)
    `{!Project x z, !AutoHasCost (x := x) (project z) p r}
  : AutoHasCost (x := (x, y)) (project z) (p, q) r.
Proof.
  unfold project, Project_there.
  eapply has_cost_compose.
  - apply has_cost_proj1.
  - apply auto_has_cost.
Qed.

#[global]
Instance AutoHasCost_Tuple_pair {a b c : AA} (x : a) (y : b) (z : c) `{!Tuple x y, !Tuple x z}
    `{Account a, Account b, Account c}
    (p : account x) (q : account y) (r : account z)
    `{!AutoHasCost (x := x) (tuple y) p q, !AutoHasCost (x := x) (tuple z) p r}
  : AutoHasCost (x := x) (tuple (y, z)) p (q, r).
Proof.
  apply has_cost_pair; apply auto_has_cost.
Qed.

#[global]
Instance AutoHasCost_Tuple_single {a b : AA} (x : a) (y : b) `{!Project x y}
    `{Account a, Account b}
    (p : account x) (q : account y)
    `{!AutoHasCost (x := x) (project y) p q}
  : AutoHasCost (x := x) (tuple y) p q.
Proof.
  unfold tuple, Tuple_single.
  apply auto_has_cost.
Qed.

Theorem drop_append_cost {a : AA} (n : nat) (xs ys : list a) (cs : account_list xs) (ds : account_list ys)
  : has_cost (drop_append n xs ys)
             (zero, cs, ds)
             (drop_account n (map_account S cs ++ ds)).
Proof.
  unfold drop_append.
  eapply has_cost_compose; [ | apply drop_cost ].
  eapply has_cost_pair.
  - apply auto_has_cost.
  - eapply has_cost_compose; [ | apply append_cost ].
    apply auto_has_cost.
Qed.
*)

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
*)

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
