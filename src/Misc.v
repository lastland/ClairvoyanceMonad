From Coq Require Import Morphisms Arith List.

Import ListNotations.

Definition option_bind {A B} (o : option A) (k : A -> option B) : option B :=
  match o with
  | None => None
  | Some a => k a
  end.

Module Option.
Definition ret {A : Type} : A -> option A := Some.
Notation bind := option_bind.
Module Notation.
Declare Scope option_scope.
Delimit Scope option_scope with option.
Notation "'let?' x := u 'in' v" := (bind u (fun x => v))
  (x pattern, at level 200) : option_scope.
End Notation.
End Option.

#[global] Instance Proper_add_le : Proper (le ==> le ==> le) Nat.add.
Proof.
  unfold Proper, respectful; intros; apply Nat.add_le_mono; assumption.
Qed.

#[global] Instance Proper_mul_le : Proper (le ==> le ==> le) Nat.mul.
Proof.
  unfold Proper, respectful; intros; apply Nat.mul_le_mono; assumption.
Qed.

#[global] Instance Proper_sub_le : Proper (le ==> eq ==> le) Nat.sub.
Proof.
  unfold Proper, respectful; intros; subst; apply Nat.sub_le_mono_r; assumption.
Qed.

Ltac inv H := inversion H; subst; clear H.
