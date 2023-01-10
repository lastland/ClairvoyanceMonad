From Clairvoyance Require Import Core.

(* ----------------------- Section 4.2 ------------------------- *)

(** * Figure 10. *)
Definition impl3 {a b c} (P P' : a -> b -> c -> Prop) : Prop :=
  forall x y z, P x y z -> P' x y z.

Inductive Fix {a b} (gf : (a -> M b) -> (a -> M b)) x y n : Prop :=
| MkFix (self : a -> M b) : impl3 self (Fix gf) -> gf self x y n -> Fix gf x y n.

Lemma unfold_Fix {a b} (gf : (a -> M b) -> _)
  : (forall P P', impl3 P P' -> impl3 (gf P) (gf P')) ->
    impl3 (Fix gf) (gf (Fix gf)).
Proof.
  intros MON; intros ? ? ? W; induction W.
  eapply MON; [ | eapply H1 ].
  assumption.
Qed.

Lemma fold_Fix {a b} (gf : (a -> M b) -> _)
  : impl3 (gf (Fix gf)) (Fix gf).
Proof.
  intros ? ? ? W. econstructor.
  - intros ? ? ? V; apply V.
  - assumption.
Qed.
