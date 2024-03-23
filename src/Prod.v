From Coq Require Import RelationClasses.
From Clairvoyance Require Import Core Approx.

Inductive prodA (A B : Type) : Type :=
  | pairA : T A -> T B -> prodA A B.
Arguments pairA {A} {B}.

Definition prodD {A B C D} (f : T A -> T C) (g : T B -> T D)
  (p : prodA A B) : prodA C D :=
  match p with
  | pairA a b => pairA (f a) (g b)
  end.

#[global]
Instance LessDefined_prodA {A B}
  `{LessDefined A} `{LessDefined B}: LessDefined (prodA A B) :=
  fun '(pairA a b) '(pairA a' b') => a `less_defined` a' /\ b `less_defined` b'.

#[local] Existing Instance Reflexive_LessDefined_T.
#[global] Instance Reflexive_LessDefined_prodA {A B}
  `{LDA : LessDefined A, LDB : LessDefined B, !Reflexive LDA, !Reflexive LDB} :
  Reflexive (less_defined (a := prodA A B)).
Proof.
  unfold Reflexive. intros [ a b ]. split; reflexivity.
Qed.

#[local] Existing Instance Transitive_LessDefined_T.
#[global] Instance Transitive_LessDefined_prodA {A B}
  `{LDA : LessDefined A, LDB : LessDefined B, !Transitive LDA, !Transitive LDB} :
  Transitive (less_defined (a := prodA A B)).
Proof.
  unfold Transitive. intros [ a1 b1 ] [ a2 b2 ] [ a3 b3 ] [ H1 H2 ] [ H3 H4 ].
  split; etransitivity; eauto.
Qed.

#[global]
Instance Exact_prodA {A B C D}
  `{Exact A C} `{Exact B D} : Exact (A * B) (prodA C D) :=
  fun '(a, b) => pairA (exact a) (exact b).

#[global] Instance Lub_prodA {A B} `{Lub A, Lub B} : Lub (prodA A B) :=
  fun p1 p2 => match p1, p2 with
            | pairA a1 b1, pairA a2 b2 => pairA (lub a1 a2) (lub b1 b2)
            end.

#[global] Instance LubLaw_prodA :
  forall {A B}
    `{LubLaw A, LubLaw B,
      !Reflexive (less_defined (a := A)), !Reflexive (less_defined (a := B))},
    LubLaw (prodA A B).
Proof.
  intros A B LA LDA LLA LB LDB LLB.
  split.
  - intros [ a1 b1 ] [ a2 b2 ] [ a3 b3 ] [ H1 H2 ] [ H3 H4 ].
    split; apply lub_least_upper_bound; auto.
  - intros [ a1 b1 ] [ a2 b2 ] [ [ a3 b3 ] [ [ Ha13 Hb13 ] [ Ha23 Hb23 ] ] ].
    split; apply lub_upper_bound_l; eauto.
  - intros [ a1 b1 ] [ a2 b2 ] [ [ a3 b3 ] [ [ Ha13 Hb13 ] [ Ha23 Hb23 ] ] ].
    split; apply lub_upper_bound_r; eauto.
Qed.
