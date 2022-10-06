From Coq Require Import Arith List Lia Morphisms Relations Classical.
From Clairvoyance Require Import Core Approx.

(** * Cost specifications *)

Definition at_most {a} `{LessDefined a} (u : M a) '((x, n) : a * nat) : Prop :=
  exists y m, u y m /\ x `less_defined` y /\ m <= n.

Definition at_least {a} `{LessDefined a} (u : M a) '((x, n) : a * nat) : Prop :=
  forall y m, u y m -> x `less_defined` y -> n <= m.

Infix "`at_most`" := at_most (at level 80).
Infix "`at_least`" := at_least (at level 80).

Definition costs {a} `{LessDefined a} (u : M a) (xn : a * nat) : Prop :=
  u `at_most` xn /\ u `at_least` xn.

Definition at_most0 {a} (u : M a) (n : nat) : Prop :=
  exists y m, u y m /\ m <= n.

Definition at_least0 {a} (u : M a) (n : nat) : Prop :=
  forall y m, u y m -> n <= m.

Infix "`at_most0`" := at_most0 (at level 80).
Infix "`at_least0`" := at_least0 (at level 80).

Definition costs0 {a} (u : M a) (n : nat) : Prop :=
  u `at_most0` n /\ u `at_least0` n.

(** ** Cost functions *)
(** ... rather than relations *)

Module NAT.
Definition t := nat -> Prop.  (* should be a singleton...? *)

Definition of_nat (n : nat) : t := eq n.

Definition lift_arith (f : nat -> nat -> nat) (x y : t) : t :=
  fun nz => exists nx ny, x nx /\ y ny /\ nz = f nx ny.

Definition add := lift_arith Nat.add.
Definition sub := lift_arith Nat.sub.
Definition mul := lift_arith Nat.mul.

Definition lift_rel (f : nat -> nat -> Prop) (x y : t) : Prop :=
  exists nx ny, x nx /\ y ny /\ f nx ny.
Definition eq := lift_rel eq.
Definition le := lift_rel Nat.le.
End NAT.

Declare Scope natprop_scope.
Delimit Scope natprop_scope with NAT.
Bind Scope natprop_scope with NAT.t.
Infix "+" := NAT.add : natprop_scope.
Infix "-" := NAT.sub : natprop_scope.
Infix "*" := NAT.mul : natprop_scope.
Infix "=" := NAT.eq : natprop_scope.
Infix "<=" := NAT.le : natprop_scope.

Coercion NAT.of_nat : nat >-> NAT.t.

Definition cost_of {a} (u : M a) : NAT.t :=
  costs0 u.

Theorem cost_of_bound {a} (u : M a) (bound : nat)
  : (cost_of u <= bound)%NAT -> u [[ fun x n => n <= bound ]].
Proof.
  intros [ n [ ny [ [ [y [m H0] ] H1] [H2 H3] ] ] ].
  exists y, m. split; [ apply H0 | ].
  etransitivity; [ apply H0 | ].
  red in H2. subst. apply H3.
Qed.

Lemma mini' (P : nat -> Prop) (n : nat) : ~~ ((forall m, m <= n -> ~ P m) \/ exists m, P m /\ (forall m', P m' -> m <= m')).
Proof.
  induction n as [ | n IH ].
  - intro contra. apply contra. left. intros m Hm HP; inversion Hm; subst.
    apply contra; right. exists 0. split; auto using Nat.le_0_l.
  - intros contra. apply IH; intros [ H | H].
    + apply contra; left. intros m Hm HP.
      inversion Hm; subst.
      * apply contra; right. exists (S n). split; auto.
        intros m' HP'. apply not_gt. intros contra''. apply gt_S_le in contra''.
        apply (H _ contra'' HP').
      * red in H; eauto.
    + apply contra; right. auto.
Qed.

Lemma not_impl (P Q : Prop) : (Q -> P) -> ~ P -> ~ Q.
Proof. exact (fun f g x => g (f x)). Qed.

Lemma mini (P : nat -> Prop) (n : nat) : P n -> ~~ exists m, P m /\ (forall m', P m' -> m <= m').
Proof.
  intros HP. generalize (mini' P n). do 2 apply not_impl.
  intros [H | H].
  - exfalso; eapply H; eauto.
  - apply H.
Qed.

Theorem cost_of_bound' {a} (u : M a) (bound : nat)
  : u [[ fun x n => n <= bound ]] -> ~~ (cost_of u <= bound)%NAT.
Proof.
  intros [y [n Hn] ].
  generalize (mini (fun n => exists y, u y n) n (ex_intro _ y (proj1 Hn))).
  do 2 apply not_impl.
  intros [m [ [y' Hu] Hm] ].
  exists m, bound.
  split; [ | split; [ reflexivity | ] ].
  - split; red; eauto.
  - etransitivity; [ | apply Hn ]. apply Hm; eexists; apply Hn.
Qed.

(* Those are classically equivalent. *)
Theorem cost_of_bound_iff {a} (u : M a) (bound : nat)
  : (cost_of u <= bound)%NAT <-> u [[ fun x n => n <= bound ]].
Proof.
  split; [ apply cost_of_bound | ].
  intros H. apply NNPP. apply cost_of_bound', H.
Qed.
