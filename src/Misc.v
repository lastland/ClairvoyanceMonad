From Coq Require Import Morphisms Arith.

#[global] Instance Proper_add_le : Proper (le ==> le ==> le) Nat.add.
Proof.
  unfold Proper, respectful; intros; apply Nat.add_le_mono; assumption.
Qed.
