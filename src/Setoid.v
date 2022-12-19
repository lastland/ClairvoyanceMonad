From Coq Require Import Setoid SetoidClass Morphisms Lia Arith.
From Clairvoyance Require Import Relations.

Record Morphism (a b : Type) `{Setoid a, Setoid b} : Type :=
  { apply :> a -> b
  ; Proper_SM : Proper (equiv ==> equiv) apply
  }.

Arguments apply {a b _ _}.
Arguments Proper_SM {a b _ _} _ {x y}.
#[global] Existing Instance Proper_SM.

#[global,refine] Instance Setoid_SM {a b} `{Setoid a,Setoid b} : Setoid (Morphism a b) :=
  {| equiv f f' := (equiv ==> equiv)%signature (apply f) (apply f') |}.
Proof.
  1,2: assumption.
  constructor.
  - intros ?. apply Proper_SM.
  - intros ? ?. intros ? ? ? Hx. symmetry. symmetry in Hx. auto.
  - intros ? ? ? Hf Hf2 ? ? Hx. etransitivity; [ apply Hf; reflexivity | apply Hf2; assumption ].
Defined.

Declare Scope setoid_scope.
Delimit Scope setoid_scope with setoid.
#[global] Open Scope setoid_scope.

Infix "~->" := Morphism (at level 90) : setoid_scope.

Definition id a `{Setoid a} : a ~-> a :=
  {| apply := fun x => x
  ;  Proper_SM _ _ H := H |}.

Definition compose {a b c} `{Setoid a,Setoid b,Setoid c} (f : a ~-> b) (g : b ~-> c) : a ~-> c :=
  {| apply x := g (f x)
  ;  Proper_SM _ _ H := Proper_SM g (Proper_SM f H) |}.

#[global] Instance Setoid_prod {a b} `{Setoid a, Setoid b} : Setoid (a * b) :=
  {| equiv := pair_rel equiv equiv |}.

Section Cartesian.

Context {a b} `{Sa : Setoid a, Sb : Setoid b}.

#[local] Instance Proper_fst : Proper (equiv ==> equiv) (@fst a b).
Proof.
  unfold Proper, respectful; intros x y H; apply H.
Qed.

#[local] Instance Proper_snd : Proper (equiv ==> equiv) (@snd a b).
Proof.
  unfold Proper, respectful; intros x y H; apply H.
Qed.

Definition Setoid_proj1 : (a * b) ~-> a := {| apply := fst |}.
Definition Setoid_proj2 : (a * b) ~-> b := {| apply := snd |}.

Context {c} `{Sc : Setoid c}.

Section RawPair.

Context (f : a -> b) (g : a -> c).
Context (Proper_f : Proper (equiv ==> equiv) f).
Context (Proper_g : Proper (equiv ==> equiv) g).

Definition pairf : a -> b * c := fun x => (f x, g x).

Lemma Proper_pairf : Proper (equiv ==> equiv) pairf.
Proof.
  unfold Proper, respectful. intros x y H; constructor; [ apply Proper_f, H | apply Proper_g, H ].
Qed.

End RawPair.

#[local] Existing Instance Proper_pairf.

Definition Setoid_pair (f : a ~-> b) (g : a ~-> c) : a ~-> b * c := {| apply := pairf f g |}.

End Cartesian.
