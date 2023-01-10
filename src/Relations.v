From Coq Require Import Morphisms Relations.

Set Implicit Arguments.

Record pair_rel {a1 b1 a2 b2} (r1 : a1 -> b1 -> Prop) (r2 : a2 -> b2 -> Prop) (xs : a1 * a2) (ys : b1 * b2)
  : Prop := prod_rel
  { fst_rel : r1 (fst xs) (fst ys)
  ; snd_rel : r2 (snd xs) (snd ys)
  }.

Inductive option_rel {a b} (r : a -> b -> Prop) : option a -> option b -> Prop :=
| option_rel_None : option_rel r None None
| option_rel_Some x y : r x y -> option_rel r (Some x) (Some y)
.

#[global]
Instance PreOrder_pair_rel {a b ra rb} `{!@PreOrder a ra,!@PreOrder b rb} : PreOrder (pair_rel ra rb).
Proof.
  constructor; constructor; reflexivity + etransitivity; eapply fst_rel + eapply snd_rel; eassumption.
Qed.


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
