From Coq Require Import Morphisms Arith List.

Import ListNotations.

Definition option_bind {A B} (o : option A) (k : A -> option B) : option B :=
  match o with
  | None => None
  | Some a => k a
  end.

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
