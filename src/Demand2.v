From Coq Require Import Arith Setoid Morphisms Lia.
From Equations Require Import Equations.
From Clairvoyance Require Import Core Approx ListA Misc Tick.

Set Implicit Arguments.
Set Contextual Implicit.

Generalizable All Variables.

Import Tick.Notations.

Class Order {A : Type} (r : relation A) : Prop :=
  { Order_Reflexive :> Reflexive r
  ; Order_Transitive :> Transitive r
  ; Order_AntiSymmetric :> Antisymmetric A eq r
  }.

(** Order structure on approximation values [valueA].
    Core operations ([exact], [less_defined], [lub], [bottom_of])
    and their properties. *)
Class IsApproxAlgebra (t tA : Type) : Type :=
  { AO_Exact         :> Exact t     tA
  ; AO_LessDefined   :> LessDefined tA
  ; AO_Lub           :> Lub         tA
  ; AO_BottomOf      :> BottomOf    tA

  ; AO_Order         :> Order (A := tA) less_defined
  ; AO_LubLaw        :> LubLaw        tA
  ; AO_BottomIsLeast :> BottomIsLeast tA
  }.

#[global] Hint Mode IsApproxAlgebra - - : typeclass_instances.

Notation IsAA := IsApproxAlgebra (only parsing).

Lemma order_def {A} {r : relation A} `{!PreOrder r, !Antisymmetric A eq r} : Order r.
Proof.
  constructor; try apply PreOrder0 + apply Antisymmetric0.
Qed.

#[local]
Instance Order_PreOrder {A} {r : relation A} `{!Order r} : PreOrder r.
Proof.
  constructor; apply Order0.
Qed.

Theorem IsAA_def `{Approx.IsAA t tA, !Antisymmetric tA eq less_defined} : IsAA t tA.
Proof.
  econstructor; try apply H. apply @order_def. apply H. apply Antisymmetric0.
Defined.

Theorem IsAA_IsAA `{IsAA t tA} : Approx.IsAA t tA.
Proof.
  econstructor; try apply IsAA0. apply Order_PreOrder.
Defined.

#[local]
Instance Order_less_defined_bool : Order (less_defined (a := bool)).
Proof.
  constructor. 1,2: typeclasses eauto.
  cbv. auto.
Qed.

#[local]
Instance Order_less_defined_T `{!LessDefined a, !Order (less_defined (a := a))}
  : Order (less_defined (a := T a)).
Proof.
  constructor.
  - apply Reflexive_LessDefined_T.
  - apply Transitive_LessDefined_T.
  - cbv. intros _ _ [] Hxy; inv Hxy. reflexivity.
    f_equal. apply antisymmetry; auto.
Qed.

#[local]
Instance Order_less_defined_listA `{!LessDefined a, !Order (less_defined (a := a))}
  : Order (less_defined (a := listA a)).
Proof.
  constructor.
  - apply (@Reflexive_less_defined_listA _ _ _).
  - apply @PreOrder_Transitive. apply @PreOrder_LessDefined_list. apply Order_PreOrder.
  - cbv. intros x y Hxy; induction Hxy; intros Hxy; inv Hxy.
    + reflexivity.
    + f_equal; [ apply antisymmetry; auto | ].
      inv H5; auto.
    + f_equal; [ apply antisymmetry; auto | f_equal ].
      inv H6. apply IHHxy; auto.
Qed.

#[local]
Instance Antisymmetric_pair_rel `{Antisymmetric A eq r, Antisymmetric B eq r'}
  : Antisymmetric (A * B) eq (Relations.pair_rel r r').
Proof.
  cbv. intros [] [] [] []; cbn in *. f_equal; apply antisymmetry; auto.
Qed.

#[local]
Instance Order_pair_rel `{!Order (A := A) r, !Order (A := B) r'} : Order (Relations.pair_rel r r').
Proof.
  constructor.
  - typeclasses eauto.
  - typeclasses eauto.
  - typeclasses eauto.
Qed.

#[local]
Instance Order_less_defined_prod `{!LessDefined a, !Order (less_defined (a := a))}
    `{!LessDefined b, !Order (less_defined (a := b))}
  : Order (less_defined (a := a * b)).
Proof.
  constructor.
  - typeclasses eauto.
  - typeclasses eauto.
  - typeclasses eauto.
Qed.

#[local]
Instance IsAA_bool : IsAA bool bool := {}.

#[local]
Instance IsAA_T `{H : IsAA a a'} : IsAA a (T a') := {}.

#[local]
Instance IsAA_list `{H : IsAA a a'} : IsAA (list a) (listA a') := {}.

#[local]
Instance IsAA_prod `{H : IsAA a a', H2 : IsAA b b'} : IsAA (a * b) (a' * b') := {}.

Record ApproxAlgebra : Type := Build_ApproxAlgebra
  { carrier : Type;
    approx : Type;
    AA_IsAA : IsAA carrier approx }.

#[local]
Existing Instance AA_IsAA.

Notation AA := ApproxAlgebra.

Definition AA_bool : AA := {| carrier := bool ; approx := bool |}.
Definition AA_T (a : AA) : AA := {| carrier := carrier a ; approx := T (approx a) |}.
Definition AA_list (a : AA) : AA := {| carrier := list (carrier a) ; approx := listA (approx a) |}.
Definition AA_prod (a b : AA) : AA := {| carrier := carrier a * carrier b ; approx := approx a * approx b |}.

Inductive ty : Set :=
  | Bool
  | Th : ty -> ty
  | List : ty -> ty
  | Prod : ty -> ty -> ty
  .

Inductive tm (G : ty) : ty -> Set :=
  | Var : tm G G
  | Fst {A B : ty} : tm G (Prod A B) -> tm G A
  | Snd {A B : ty} : tm G (Prod A B) -> tm G B
  | Pair {A B : ty} : tm G A -> tm G B -> tm G (Prod A B)
  | Boo : bool -> tm G Bool
  | Tik (A : ty) : tm G A -> tm G A
  | Lazy {A : ty} : tm G A -> tm G (Th A)
  | Force {A : ty} : tm G (Th A) -> tm G A
  | Nil {A : ty} : tm G (List A)
  | Cons {A : ty} : tm G (Th A) -> tm G (Th (List A)) -> tm G (List A)
  | Foldr {A B : ty} : tm (Prod (Prod G (Th A)) (Th B)) B -> tm G B -> tm G (List A) -> tm G B
.

Record Lens (A A' B B' : Type) : Type := MkLens
  { get : A -> B
  ; put : A -> B' -> Tick A'
  }.

Arguments MkLens {A A' B B'}.
Arguments get {A A' B B'}.
Arguments put {A A' B B'}.

Fixpoint den_ty (A : ty) : AA :=
  match A with
  | Bool => AA_bool
  | Th A => AA_T (den_ty A)
  | List A => AA_list (den_ty A)
  | Prod A B => AA_prod (den_ty A) (den_ty B)
  end.

#[local]
Instance IsAA_den_ty {A} : IsAA (carrier (den_ty A)) (approx (den_ty A)).
Proof.
  typeclasses eauto.
Defined.

Definition lift2_lub `{Lub A} : Tick A -> Tick A -> Tick A :=
  fun u v => Tick.MkTick (Tick.cost u + Tick.cost v) (lub (Tick.val u) (Tick.val v)).

Definition eqle {A} : Tick A -> Tick A -> Prop :=
  fun u v => Tick.cost u <= Tick.cost v /\ Tick.val u = Tick.val v.

#[global]
Instance PreOrder_eqle {A} : PreOrder (eqle (A := A)).
Proof.
  constructor.
  - split; reflexivity.
  - split; etransitivity; apply H + apply H0.
Qed.

Lemma less_defined_bind' {a b} `{LessDefined a, LessDefined b}
  : forall (u u' : Tick a), u `less_defined` u' ->
    forall (k k' : a -> Tick b), k (Tick.val u) `less_defined` k' (Tick.val u') ->
    Tick.bind u k `less_defined` Tick.bind u' k'.
Proof.
  intros u u' Hu k k' Hk.
  constructor; cbn.
  - apply Nat.add_le_mono; [ apply Hu | apply Hk ].
  - apply Hk.
Qed.

Lemma less_defined_lub `{IsAA A A'} {a b a' b' : A'}
  : a `less_defined` b ->
    a' `less_defined` b' ->
    cobounded b b' ->
    lub a a' `less_defined` lub b b'.
Proof.
  intros. apply lub_least_upper_bound.
  - etransitivity; [ | apply lub_upper_bound_l; auto ]; auto.
  - etransitivity; [ | apply lub_upper_bound_r; auto ]; auto.
Qed.

Lemma lub_comm4_le `{IsAA A A'} {a b c d e : A'}
  : a `less_defined` e ->
    b `less_defined` e ->
    c `less_defined` e ->
    d `less_defined` e ->
    lub (lub a b) (lub c d) `less_defined` lub (lub a c) (lub b d).
Proof.
  intros. apply lub_least_upper_bound; apply lub_least_upper_bound.
  - etransitivity; [ | apply lub_upper_bound_l; econstructor; split; apply lub_least_upper_bound; eauto ].
    apply lub_upper_bound_l; eauto.
  - etransitivity; [ | apply lub_upper_bound_r; econstructor; split; apply lub_least_upper_bound; eauto ].
    apply lub_upper_bound_l; eauto.
  - etransitivity; [ | apply lub_upper_bound_l; econstructor; split; apply lub_least_upper_bound; eauto ].
    apply lub_upper_bound_r; eauto.
  - etransitivity; [ | apply lub_upper_bound_r; econstructor; split; apply lub_least_upper_bound; eauto ].
    apply lub_upper_bound_r; eauto.
Qed.

Lemma lub_comm4 `{IsAA A A'} {a b c d e : A'}
  : a `less_defined` e ->
    b `less_defined` e ->
    c `less_defined` e ->
    d `less_defined` e ->
    lub (lub a b) (lub c d) = lub (lub a c) (lub b d).
Proof.
  intros. apply antisymmetry; eapply lub_comm4_le; eassumption.
Qed.

Lemma add_comm4 {a b c d : nat}
  : (a + b) + (c + d) = (a + c) + (b + d).
Proof.
  lia.
Qed.

Lemma less_defined_lift2_lub `{IsAA A A'} {a b c d : Tick A'}
    : a `less_defined` c ->
      b `less_defined` d ->
      cobounded (Tick.val c) (Tick.val d) ->
      lift2_lub a b `less_defined` lift2_lub c d.
Proof.
  constructor; cbn.
  - apply Nat.add_le_mono; apply H + apply H0.
  - apply less_defined_lub; [ apply H | apply H0 | auto ].
Qed.

#[global]
Instance eqle_lift2_lub `{Lub A} : Proper (eqle ==> eqle ==> eqle) (lift2_lub (A := A)).
Proof.
  constructor; cbn.
  - apply Nat.add_le_mono; [ apply H0 | apply H1 ].
  - rewrite (proj2 H0), (proj2 H1). reflexivity.
Qed.

Lemma lub_bind `{Lub A, Lub B, LessDefined A} (u u' u'' : Tick A) (k k' k'' : A -> Tick B) {P : A -> Prop}
  : P (Tick.val u') ->
    P (Tick.val u'') ->
    eqle u (lift2_lub u' u'') ->
    (forall a' a'' (a := lub a' a''), P a' -> P a'' -> eqle (k a) (lift2_lub (k' a') (k'' a''))) ->
    eqle (Tick.bind u k) (lift2_lub (Tick.bind u' k') (Tick.bind u'' k'')).
Proof.
  constructor.
  - cbn. rewrite add_comm4. apply Nat.add_le_mono.
    + apply H4.
    + replace (Tick.val u) with (lub (Tick.val u') (Tick.val u'')) by (symmetry; apply H4).
      apply H5; auto.
  - cbn.
    replace (Tick.val u) with (lub (Tick.val u') (Tick.val u'')) by (symmetry; apply H4).
    apply H5; auto.
Qed.

Lemma lub_ret `{Lub A} (a a' a'' : A)
  : a = lub a' a'' ->
    eqle (Tick.ret a) (lift2_lub (Tick.ret a') (Tick.ret a'')).
Proof.
  constructor; [ reflexivity | auto ].
Qed.

Lemma lub_idempotent' {A} `{LubLaw A, !Reflexive (A := A) less_defined} (a : A) : lub a a `less_defined` a.
Proof.
  apply lub_least_upper_bound; reflexivity.
Qed.

Lemma lub_idempotent'' {A} `{LubLaw A, !Reflexive (A := A) less_defined} (a : A) : a `less_defined` lub a a.
Proof.
  apply lub_upper_bound_l. eauto.
Qed.

Lemma lub_idempotent {A} `{LubLaw A, !Order (A := A) less_defined} (a : A) : lub a a = a.
Proof.
  apply antisymmetry; [ apply lub_idempotent' | apply lub_idempotent'' ].
Qed.

Lemma lift2_lub_idempotent {A} `{LubLaw A, !Order (A := A) less_defined} (u : Tick A)
  : eqle u (lift2_lub u u).
Proof.
  constructor; cbn; [ lia | symmetry; apply lub_idempotent ].
Qed.

Lemma lub_l `{LubLaw A, !Order (A := A) less_defined} (u v : A)
  : v `less_defined` u -> u = lub u v.
Proof.
  intros L. apply antisymmetry.
  - apply lub_upper_bound_l. econstructor; split; eauto. reflexivity.
  - apply lub_least_upper_bound; [ reflexivity | auto ].
Qed.

Lemma lub_r `{LubLaw A, !Order (A := A) less_defined} (u v : A)
  : v `less_defined` u -> u = lub v u.
Proof.
  intros L. apply antisymmetry.
  - apply lub_upper_bound_r. econstructor; split; eauto. reflexivity.
  - apply lub_least_upper_bound; [ auto | reflexivity ].
Qed.


Lemma lub_bottom_of_l `{IsAA A A'} {x y : A'} : y `less_defined` x -> lub (bottom_of x) y = y.
Proof.
  intros; symmetry; apply lub_r. apply bottom_is_least; auto.
Qed.

Lemma lub_bottom_of_r `{IsAA A A'} {x y : A'} : y `less_defined` x -> lub y (bottom_of x) = y.
Proof.
  intros; symmetry; apply lub_l. apply bottom_is_least; auto.
Qed.

Lemma lub_bottom_of `{IsAA A A'} (a : A') : lub (bottom_of a) (bottom_of a) = bottom_of a.
Proof.
  apply lub_bottom_of_l. apply bottom_is_less.
Qed.

Lemma reflexive' {A} {r : relation A} `{!Reflexive r} (a b : A) : a = b -> r a b.
Proof.
  intros []; reflexivity.
Qed.

Lemma lift2_lub_l {A} `{LubLaw A, !Order (A := A) less_defined} (u v : Tick A)
  : Tick.val v `less_defined` Tick.val u ->
    eqle u (lift2_lub u v).
Proof.
  constructor; cbn; [ lia | ].
  apply lub_l; auto.
Qed.

Lemma lift2_lub_r {A} `{LubLaw A, !Order (A := A) less_defined} (u v : Tick A)
  : Tick.val v `less_defined` Tick.val u ->
    eqle u (lift2_lub v u).
Proof.
  constructor; cbn; [ lia | ].
  apply lub_r; auto.
Qed.

Record Good `{IsAA A A', IsAA B B'} (l : Lens A A' B B') : Prop := MkGood
  { complete : forall a b', b' `is_approx` get l a -> Tick.val (put l a b') `is_approx` a
  ; monotone : forall a b' b'',
      b' `less_defined` b'' ->
      b'' `is_approx` get l a ->
      put l a b' `less_defined` put l a b''
  ; homomorphic : forall a b' b'',
      b' `is_approx` get l a ->
      b'' `is_approx` get l a ->
      eqle (put l a (lub b' b'')) (lift2_lub (put l a b') (put l a b''))
  }.

Record Correct `{IsAA A A', IsAA B B'} (l : Lens A A' B B') (cv : A' -> M B') : Prop := MkCorrect
  { Good_correct : Good l
  ; functional_correct : forall a a', a' `is_approx` a -> cv a' {{ fun b' n => b' `is_approx` get l a }}
  ; underapprox : forall a a', a' `is_approx` a -> cv a' {{ fun b' n =>
      put l a b' `less_defined` Tick.MkTick n a' }}
  ; minimal_ex :
      forall a b', b' `is_approx` get l a ->
      forall a', a' `is_approx` a ->
        Tick.val (put l a b') `less_defined` a' ->
        cv a' [[ fun b'' n => n = Tick.cost (put l a b') /\ b' `less_defined` b'' ]]
  ; minimal_univ :
      forall a a', a' `is_approx` a ->
        cv a' {{ fun b'' m =>
          forall b', b' `less_defined` b'' -> put l a b' `less_defined` Tick.MkTick m a' }}
  }.

#[global] Hint Resolve Good_correct : core.

Definition id_fn {A : Type} : A -> A :=
  fun a => a.

Definition id_dem {A A' : Type} : A -> A' -> Tick A' :=
  fun a a' => Tick.ret a'.

Definition id_lens {A A' : Type} : Lens A A' A A' :=
  MkLens id_fn id_dem.

Definition id_cv {A' : Type} : A' -> M A' :=
  ret.

Theorem Good_id `{IsAA A A'} : Good (@id_lens A A').
Proof.
  constructor; cbn; unfold id_fn, id_dem; cbn; auto.
  - constructor; cbn; auto.
  - intros; apply lub_ret; auto.
Qed.

Theorem Correct_id `{IsAA A A'} : Correct (@id_lens A A') id_cv.
Proof.
  constructor; cbn; unfold id_cv.
  - apply Good_id.
  - intros. unfold id_cv. apply pessimistic_ret. auto.
  - intros. unfold id_cv. apply pessimistic_ret. unfold id_dem. constructor; cbn; auto.
    reflexivity.
  - intros. apply optimistic_ret. split; auto.
  - intros. apply pessimistic_ret. intros. constructor; cbn; auto.
Qed.

Definition fst_fn {G A B : Type} : (G -> A * B) -> (G -> A) :=
  fun f g => fst (f g).

Definition snd_fn {G A B : Type} : (G -> A * B) -> (G -> B) :=
  fun f g => snd (f g).

Definition pair_fn {G A B : Type} : (G -> A) -> (G -> B) -> (G -> A * B) :=
  fun fa fb g => (fa g, fb g).

Definition fst_dem `{IsAA G G', IsAA A A', IsAA B B'} : Lens G G' (A * B) (A' * B') -> (G -> A' -> Tick G') :=
  fun l g a' => put l g (a', bottom_of (exact (snd (get l g)))).

Definition fst_lens `{IsAA G G', IsAA A A', IsAA B B'} : Lens G G' (A * B) (A' * B') -> Lens G G' A A' :=
  fun l => MkLens (fst_fn (get l)) (fst_dem l).

Definition fst_cv {G' A' B' : Type} : (G' -> M (A' * B')) -> G' -> M A' :=
  fun h g => let! ab' := h g in ret (fst ab').

Definition snd_dem `{IsAA G G', IsAA A A', IsAA B B'} : Lens G G' (A * B) (A' * B') -> (G -> B' -> Tick G') :=
  fun l g b' => put l g (bottom_of (exact (fst (get l g))), b').

Definition snd_lens `{IsAA G G', IsAA A A', IsAA B B'} : Lens G G' (A * B) (A' * B') -> Lens G G' B B' :=
  fun l => MkLens (snd_fn (get l)) (snd_dem l).

Definition snd_cv {G' A' B' : Type} : (G' -> M (A' * B')) -> G' -> M B' :=
  fun h g => let! ab' := h g in ret (snd ab').


Theorem Good_fst `{IsAA G G', IsAA A A', IsAA B B'} (l : Lens G G' (A * B) (A' * B'))
  : Good l ->
    Good (fst_lens l).
Proof.
  intros Gl. constructor; cbn.
  - intros. unfold fst_dem. apply Gl. constructor; cbn; auto. apply bottom_is_less.
  - intros. unfold fst_dem. apply Gl.
    + constructor; cbn; auto. reflexivity.
    + constructor; cbn; auto. apply bottom_is_less.
  - intros. unfold fst_dem. rewrite <- (homomorphic Gl).
    + apply reflexive'.
      f_equal. apply (f_equal2 pair); [reflexivity |].
      symmetry; apply lub_bottom_of.
    + constructor; cbn; auto. apply bottom_is_less.
    + constructor; cbn; auto. apply bottom_is_less.
Qed.

Theorem Correct_fst `{IsAA G G', IsAA A A', IsAA B B'} (l : Lens G G' (A * B) (A' * B')) (f : _)
  : Correct l f ->
    Correct (fst_lens l) (fst_cv f).
Proof.
  intros Cf. constructor; unfold fst_cv.
  - apply Good_fst; eauto.
  - intros. apply pessimistic_bind.
    apply (pessimistic_mon (functional_correct Cf _ _ H)).
    intros; apply pessimistic_ret. cbn.
    unfold fst_fn.
    apply H0.
  - intros. apply pessimistic_bind.
    apply (pessimistic_mon (pessimistic_conj (functional_correct Cf _ _ H) (underapprox Cf _ H))).
    intros ? ? [H1 H2]; apply pessimistic_ret. cbn. unfold fst_dem.
    rewrite Nat.add_0_r.
    rewrite <- H2.
    apply monotone; [ apply Cf | | auto ].
    constructor; cbn; [ reflexivity | ].
    apply bottom_is_least; apply H1.
  - intros. apply optimistic_bind. cbn in *.
    unfold fst_fn in H.
    refine (optimistic_mon (optimistic_conj (functional_correct Cf _ _ H0) (minimal_ex Cf _ _ _ _ H0 H1)) _).
    { split; cbn; [ auto | apply bottom_is_less ]. }
    intros ? ? [? [-> ?] ].
    apply optimistic_ret; split.
    + rewrite Nat.add_0_r. reflexivity.
    + apply H3.
  - intros. apply pessimistic_bind.
    apply (pessimistic_mon (pessimistic_conj (functional_correct Cf _ _ H) (minimal_univ Cf _ H))).
    intros ? ? [Hx Hu].
    apply pessimistic_ret. intros ? Hy. cbn.
    unfold fst_dem. rewrite Nat.add_0_r. apply Hu.
    split; cbn; [ auto | apply bottom_is_least, Hx ].
Qed.

Theorem Good_snd `{IsAA G G', IsAA A A', IsAA B B'} (l : Lens G G' (A * B) (A' * B'))
  : Good l ->
    Good (snd_lens l).
Proof.
  intros Gl. constructor; cbn.
  - intros. unfold snd_dem. apply Gl. constructor; cbn; auto. apply bottom_is_less.
  - intros. unfold snd_dem. apply Gl.
    + constructor; cbn; auto. reflexivity.
    + constructor; cbn; auto. apply bottom_is_less.
  - intros. unfold snd_dem. rewrite <- (homomorphic Gl).
    + apply reflexive'.
      f_equal. apply (f_equal2 pair); [ |reflexivity ].
      symmetry; apply lub_bottom_of.
    + constructor; cbn; auto. apply bottom_is_less.
    + constructor; cbn; auto. apply bottom_is_less.
Qed.

Theorem Correct_snd `{IsAA G G', IsAA A A', IsAA B B'} (l : Lens G G' (A * B) (A' * B')) (f : _)
  : Correct l f ->
    Correct (snd_lens l) (snd_cv f).
Proof.
  intros Cf. constructor; unfold snd_cv.
  - apply Good_snd; eauto.
  - intros. apply pessimistic_bind.
    apply (pessimistic_mon (functional_correct Cf _ _ H)).
    intros; apply pessimistic_ret. cbn.
    unfold snd_fn.
    apply H0.
  - intros. apply pessimistic_bind.
    apply (pessimistic_mon (pessimistic_conj (functional_correct Cf _ _ H) (underapprox Cf _ H))).
    intros ? ? [H1 H2]; apply pessimistic_ret. cbn. unfold snd_dem.
    rewrite Nat.add_0_r.
    rewrite <- H2.
    apply monotone; [ apply Cf | | auto ].
    constructor; cbn; [ | reflexivity ].
    apply bottom_is_least; apply H1.
  - intros. apply optimistic_bind. cbn in *.
    unfold snd_fn in H.
    refine (optimistic_mon (optimistic_conj (functional_correct Cf _ _ H0) (minimal_ex Cf _ _ _ _ H0 H1)) _).
    { split; cbn; [ apply bottom_is_less | auto ]. }
    intros ? ? [? [-> ?] ].
    apply optimistic_ret; split.
    + rewrite Nat.add_0_r. reflexivity.
    + apply H3.
  - intros. apply pessimistic_bind.
    apply (pessimistic_mon (pessimistic_conj (functional_correct Cf _ _ H) (minimal_univ Cf _ H))).
    intros ? ? [Hx Hu].
    apply pessimistic_ret. intros ? Hy. cbn.
    unfold snd_dem. rewrite Nat.add_0_r. apply Hu.
    split; cbn; [ apply bottom_is_least, Hx | auto ].
Qed.

Definition pair_dem `{IsAA G G', IsAA A A', IsAA B B'}
: (G -> A' -> Tick G') -> (G -> B' -> Tick G') -> (G -> A' * B' -> Tick G') :=
  fun fa fb g ab' => lift2_lub (fa g (fst ab')) (fb g (snd ab')).

Definition pair_lens `{IsAA G G', IsAA A A', IsAA B B'}
  : Lens G G' A A' -> Lens G G' B B' -> Lens G G' (A * B) (A' * B') :=
  fun l1 l2 => MkLens (pair_fn (get l1) (get l2)) (pair_dem (put l1) (put l2)).

Definition cons_fn {G A : Type} : (G -> A) -> (G -> list A) -> (G -> list A) :=
  fun fa fb g => cons (fa g) (fb g).

Definition hdT {A} (xs : listA A) : T A :=
  match xs with
  | NilA => Undefined (* should not happen *)
  | ConsA x _ => x
  end.

Definition tlT {A} (xs : listA A) : T (listA A) :=
  match xs with
  | NilA => Undefined (* should not happen *)
  | ConsA _ ys => ys
  end.

Definition cons_dem `{IsAA G G'} {A' : Type}
  : (G -> T A' -> Tick G') -> (G -> T (listA A') -> Tick G') -> (G -> listA A' -> Tick G') :=
  fun fa fb g ab' => lift2_lub (fa g (hdT ab')) (fb g (tlT ab')).

Definition cons_lens `{IsAA G G'} {A A' : Type}
  : Lens G G' A (T A') -> Lens G G' (list A) (T (listA A')) -> Lens G G' (list A) (listA A') :=
  fun l1 l2 => MkLens (cons_fn (get l1) (get l2)) (cons_dem (put l1) (put l2)).

Definition cons_cv {G A : Type} : (G -> M (T A)) -> (G -> M (T (listA A))) -> G -> M (listA A) :=
  fun fa fb g =>
    let! a := fa g in
    let! b := fb g in
    ret (ConsA a b).

Definition pair_cv {G' A' B' : Type} : (G' -> M A') -> (G' -> M B') -> G' -> M (A' * B') :=
  fun fa fb g =>
    let! a := fa g in
    let! b := fb g in
    ret (a, b).

Theorem Good_pair `{IsAA G G', IsAA A A', IsAA B B'}
  (la : Lens G G' A A') (lb : Lens G G' B B')
  : Good la -> Good lb -> Good (pair_lens la lb).
Proof.
  intros Ga Gb. constructor; unfold pair_lens, pair_dem, pair_fn; cbn; intros.
  - intros. apply lub_least_upper_bound.
    + apply Ga. apply H.
    + apply Gb, H.
  - apply less_defined_lift2_lub.
    { apply Ga; [ apply H | apply H0 ]. }
    { apply Gb; [ apply H | apply H0 ]. }
    econstructor; split;[apply Ga | apply Gb]; apply H0.
  - intros. cbn. rewrite (homomorphic Ga), (homomorphic Gb); [ | apply H + apply H0 .. ].
    constructor; cbn. { apply reflexive'. apply add_comm4. }
    eapply lub_comm4; apply Ga + apply Gb; apply H + apply H0.
Qed.

Theorem Correct_pair `{IsAA G G', IsAA A A', IsAA B B'}
    (la : Lens G G' A A') (lb : Lens G G' B B')
    (fa : G' -> M A') (fb : G' -> M B')
  : Correct la fa -> Correct lb fb -> Correct (pair_lens la lb) (pair_cv fa fb).
Proof.
  intros Ca Cb. unfold pair_cv. constructor.
  - apply Good_pair; [ apply Ca | apply Cb ].
  - intros g g' H. apply pessimistic_bind.
    apply (pessimistic_mon (functional_correct Ca _ _ H)).
    intros a' _ Ha. apply pessimistic_bind.
    apply (pessimistic_mon (functional_correct Cb _ _ H)).
    intros b' _ Hb. apply pessimistic_ret.
    constructor; auto.
  - intros g g' H. apply pessimistic_bind.
    apply (pessimistic_mon (underapprox Ca _ H)).
    intros a' na Ha. apply pessimistic_bind.
    apply (pessimistic_mon (underapprox Cb _ H)).
    intros b' nb Hb. apply pessimistic_ret.
    constructor; cbn.
    + rewrite Nat.add_0_r; apply Nat.add_le_mono; [ apply Ha | apply Hb ].
    + apply lub_least_upper_bound; [ apply Ha | apply Hb ].
  - intros g ab' [Ha Hb] g' Hg Hg'. apply optimistic_bind.
    refine (optimistic_mon (minimal_ex Ca _ _ Ha _ Hg _) _).
    { etransitivity; [ apply lub_upper_bound_l | apply Hg' ].
      econstructor; split; [ apply Ca, Ha | apply Cb, Hb ]. }
    intros a' n [Hn Ha']. apply optimistic_bind.
    refine (optimistic_mon (minimal_ex Cb _ _ Hb _ Hg _) _).
    { etransitivity; [ | apply Hg' ]. apply lub_upper_bound_r.
      econstructor; split; [ apply Ca, Ha | apply Cb, Hb ]. }
    intros b' m [Hm Hb']. apply optimistic_ret.
    split; [ cbn; lia | constructor; auto ].
  - intros g g' Hg'. apply pessimistic_bind.
    apply (pessimistic_mon (minimal_univ Ca _ Hg')).
    intros a'' n' Ha''. apply pessimistic_bind.
    apply (pessimistic_mon (minimal_univ Cb _ Hg')).
    intros b'' m' Hb''. apply pessimistic_ret.
    intros [a' b'] [ Ea Eb]; cbn in *. constructor.
    * cbn. rewrite !Nat.add_0_r.
      apply Nat.add_le_mono; [ apply Ha''; auto | apply Hb''; auto ].
    * cbn. apply lub_least_upper_bound; [ apply Ha''; auto | apply Hb''; auto ].
Qed.

Lemma less_defined_hdT `{IsAA A A'} (a : A) (xs : list A) (a' : listA A')
  : a' `is_approx` (cons a xs) -> hdT a' `is_approx` a.
Proof.
  intros H; inv H; cbn; auto.
Qed.

#[global] Hint Resolve less_defined_hdT : core.

Theorem Good_cons `{IsAA G G', IsAA A A'}
  (la : Lens G G' A (T A')) (lb : Lens G G' (list A) (T (listA A')))
  : Good la -> Good lb -> Good (cons_lens la lb).
Proof.
  intros Ga Gb. constructor; unfold cons_lens, cons_dem, cons_fn; cbn; intros.
  - intros. inv H. apply lub_least_upper_bound; [ apply Ga | apply Gb ]; auto.
  - inv H0; inv H. apply less_defined_lift2_lub; [ apply Ga | apply Gb | ]; auto.
    econstructor; split;[apply Ga | apply Gb]; auto.
  - intros. inv H; inv H0; cbn. change (lub_T (Lub_listA (a := ?a))) with (lub (a := T (listA a))).
    rewrite (homomorphic Ga), (homomorphic Gb); [ | auto .. ].
    constructor; cbn. { apply reflexive'. apply add_comm4. }
    eapply lub_comm4; apply Ga + apply Gb; auto.
Qed.

Theorem Correct_cons `{IsAA G G', IsAA A A'}
  (la : Lens G G' A (T A')) (lb : Lens G G' (list A) (T (listA A'))) fa fb
  : Correct la fa -> Correct lb fb -> Correct (cons_lens la lb) (cons_cv fa fb).
Proof.
  intros Ca Cb; constructor; unfold cons_cv; cbn.
  - apply Good_cons; apply Ca + apply Cb.
  - intros; apply pessimistic_bind.
    apply (pessimistic_mon (functional_correct Ca _ _ H)).
    intros ? _ ?. apply pessimistic_bind.
    apply (pessimistic_mon (functional_correct Cb _ _ H)).
    intros ? _ ?. apply pessimistic_ret.
    unfold cons_fn. simp exact_listA.
    constructor; auto.
  - intros; apply pessimistic_bind.
    apply (pessimistic_mon (underapprox Ca _ H)).
    intros ? ? ?. apply pessimistic_bind.
    apply (pessimistic_mon (underapprox Cb _ H)).
    intros ? ? ?. apply pessimistic_ret.
    unfold cons_dem.
    constructor; cbn; auto.
    + rewrite Nat.add_0_r. apply Nat.add_le_mono; apply H0 + apply H1.
    + apply lub_least_upper_bound; apply H0 + apply H1.
  - intros; apply optimistic_bind. inv H.
    assert (Tick.val (put la a x) `is_approx` a) by apply Ca, H5.
    assert (Tick.val (put lb a xs) `is_approx` a) by apply Cb, H6.
    cbn in H1; apply lub_inv in H1; [ destruct H1 | eauto ].
    apply (optimistic_mon (minimal_ex Ca _ _ H5 _ H0 H1)).
    intros ? _ [-> ?]. apply optimistic_bind.
    apply (optimistic_mon (minimal_ex Cb _ _ H6 _ H0 H3)).
    intros ? _ [-> ?]. apply optimistic_ret.
    unfold cons_dem. rewrite Nat.add_0_r.
    repeat constructor; auto.
  - intros; apply pessimistic_bind.
    apply (pessimistic_mon (minimal_univ Ca _ H)).
    intros ? ? ?. apply pessimistic_bind.
    apply (pessimistic_mon (minimal_univ Cb _ H)).
    intros ? ? ?. apply pessimistic_ret; intros. inv H2.
    specialize (H0 _ H6). specialize (H1 _ H7).
    unfold cons_dem. cbn. rewrite Nat.add_0_r.
    etransitivity; [ eapply less_defined_lift2_lub; eauto | ].
    repeat constructor; cbn; auto.
    rewrite lub_idempotent. reflexivity.
Qed.

(**)

Definition boo_fn {G : Type} (b : bool) : G -> bool :=
  fun _ => b.

Definition boo_dem `{IsAA G G'} : G -> bool -> Tick G' :=
  fun g _ => Tick.ret (bottom_of (exact g)).

Definition boo_lens `{IsAA G G'} (b : bool) : Lens G G' bool bool :=
  MkLens (boo_fn b) boo_dem.

Definition boo_cv {G : Type} (b : bool) : G -> M bool := fun g => ret b.

Theorem Good_boo `{IsAA G G'} (b : bool) : Good (boo_lens (G := G) b).
Proof.
  constructor; intros.
  - apply bottom_is_less.
  - reflexivity.
  - cbn. unfold boo_dem. constructor; [ reflexivity | ]; cbn. symmetry; apply lub_bottom_of.
Qed.

Theorem Correct_boo `{IsAA G G'} (b : bool) : Correct (boo_lens (G := G) b) (boo_cv b).
Proof.
  constructor; intros.
  - apply Good_boo.
  - apply pessimistic_ret. reflexivity.
  - apply pessimistic_ret. constructor.
    { reflexivity. }
    cbn. apply bottom_is_least. auto.
  - apply optimistic_ret. split; [ reflexivity | auto ].
  - apply pessimistic_ret. intros. constructor; [ reflexivity | cbn ].
    apply bottom_is_least; auto.
Qed.


(**)

Definition tick_dem {G G' A' : Type} (f : G -> A' -> Tick G') : G -> A' -> Tick G' :=
  fun g a => (Tick.tick >> f g a)%tick.

Definition tick_lens {G G' A A' : Type} (l : Lens G G' A A') : Lens G G' A A' :=
  MkLens (get l) (tick_dem (put l)).

Definition tick_cv {G' A' : Type} (f : G' -> M A') : G' -> M A' :=
  fun g => tick >> f g.

Theorem Good_tick `{IsAA G G', IsAA A A'} (l : Lens G G' A A')
  : Good l -> Good (tick_lens l).
Proof.
  constructor; intros; cbn.
  - apply complete; auto.
  - apply less_defined_bind. reflexivity.
    intros _ _ _. apply monotone; auto.
  - constructor. cbn.
    + apply le_n_S. rewrite <- Nat.le_succ_diag_r. apply (homomorphic H); auto.
    + apply (homomorphic H); auto.
Qed.

Theorem Correct_tick `{IsAA G G', IsAA A A'} (l : Lens G G' A A') (f : G' -> M A')
  : Correct l f -> Correct (tick_lens l) (tick_cv f).
Proof.
  intros Cl. constructor; intros; cbn; unfold tick_cv.
  - apply Good_tick; apply Cl.
  - apply pessimistic_bind, pessimistic_tick.
    apply (pessimistic_mon (functional_correct Cl _ _ H)); auto.
  - apply pessimistic_bind, pessimistic_tick.
    apply (pessimistic_mon (underapprox Cl _ H)); auto.
    intros; cbn. constructor; try apply H0.
    cbn. apply le_n_S. apply H0.
  - apply optimistic_bind, optimistic_tick.
    apply (optimistic_mon (minimal_ex Cl _ _ H _ H0 H1)).
    intros * []; split; auto.
  - apply pessimistic_bind, pessimistic_tick.
    apply (pessimistic_mon (minimal_univ Cl _ H)); intros; constructor; [ apply le_n_S | ];
        apply H0; auto.
Qed.

Definition lazy_dem {G G' A' : Type} `{IsAA G G'} (f : G -> A' -> Tick G') : G -> T A' -> Tick G' :=
  fun g ta =>
    match ta with
    | Undefined => Tick.ret (bottom_of (exact g))
    | Thunk a => f g a
    end.

Definition lazy_lens `{IsAA G G', IsAA A A'} (l : Lens G G' A A') : Lens G G' A (T A') :=
  MkLens (get l) (lazy_dem (put l)).

Definition lazy_cv {G' A' : Type} (f : G' -> M A') : G' -> M (T A') :=
    fun g => thunk (f g).

Definition Good_lazy `{IsAA G G', IsAA A A'} (l : Lens G G' A A')
  : Good l -> Good (lazy_lens l).
Proof.
  intros Gl. constructor; intros; cbn; unfold lazy_lens.
  - inv H; cbn; [ apply bottom_is_less | apply Gl; auto ].
  - inv H0; inv H; cbn.
    + reflexivity.
    + constructor. apply Nat.le_0_l. apply bottom_is_least. apply Gl. auto.
    + apply Gl; auto.
  - inv H; inv H0; cbn.
    + constructor; [ reflexivity | ]. symmetry; apply lub_bottom_of.
    + constructor; [ reflexivity | ]. symmetry; apply lub_bottom_of_l. apply Gl. auto.
    + constructor; [ cbn; rewrite Nat.add_0_r; reflexivity | ].
      symmetry; apply lub_bottom_of_r. apply Gl. auto.
    + apply homomorphic; auto.
Qed.

Definition Correct_lazy `{IsAA G G', IsAA A A'} (l : Lens G G' A A') (f : G' -> M A')
  : Correct l f -> Correct (lazy_lens l) (lazy_cv f).
Proof.
  intros Cl. constructor; intros; unfold lazy_cv; cbn.
  - apply Good_lazy, Cl.
  - apply pessimistic_thunk; [ | constructor ].
    apply (pessimistic_mon (functional_correct Cl _ _ H)).
    intros x _ Hx. constructor. auto.
  - apply pessimistic_thunk; [ | constructor; cbn; [ auto | apply bottom_is_least; auto ] ].
    apply (pessimistic_mon (underapprox Cl _ H)).
    intros x n Hx. cbn; auto.
  - intros. inv H.
    * apply optimistic_skip. split; constructor.
    * apply optimistic_thunk_go.
      apply (optimistic_mon (minimal_ex Cl _ _ H4 _ H0 H1)).
      intros ? ? []; cbn. split; [ auto | constructor; auto ].
  - intros. apply pessimistic_thunk.
    * (* pose (b_ := match b' with Undefined => bottom_of (exact (get l a)) | Thunk b_ => b_ end). *)
      refine (pessimistic_mon (minimal_univ Cl _ H) _).
      intros. unfold lazy_dem. inv H1; [ | auto ].
      constructor; cbn; [ lia |  apply bottom_is_least; auto].
    * intros ? HH; inv HH; cbn.
      constructor; cbn; [ apply Nat.le_0_l | apply bottom_is_least; auto ].
Qed.

Definition force_dem {G G' A' : Type} (f : G -> T A' -> Tick G') : G -> A' -> Tick G' :=
  fun g a => f g (Thunk a).

Definition force_lens {G G' A A'} (l : Lens G G' A (T A')) : Lens G G' A A' :=
  MkLens (get l) (force_dem (put l)).

Definition force_cv {G' A' : Type} (f : G' -> M (T A')) : G' -> M A' :=
  fun g =>
    let! x := f g in
    force x.

Definition Good_force `{IsAA G G', IsAA A A'} (l : Lens G G' A (T A'))
  : Good l -> Good (force_lens l).
Proof.
  intros Gl. constructor; unfold force_lens, force_dem; cbn.
  - intros. apply Gl; constructor; auto.
  - intros. apply Gl; constructor; auto.
  - intros. change (Thunk (lub b' b'')) with (lub (Thunk b') (Thunk b'')).
    apply Gl; constructor; auto.
Qed.

Definition Correct_force `{IsAA G G', IsAA A A'} (l : Lens G G' A (T A')) f
  : Correct l f -> Correct (force_lens l) (force_cv f).
Proof.
  intros Cf; constructor; unfold force_cv; cbn.
  - apply Good_force, Cf.
  - intros; apply pessimistic_bind.
    apply (pessimistic_mon (functional_correct Cf _ _ H)).
    intros ? _ Hx.
    apply pessimistic_force.
    intros ? ->.
    inv Hx. auto.
  - intros; apply pessimistic_bind.
    apply (pessimistic_mon (underapprox Cf _ H)).
    intros. apply pessimistic_force.
    intros ? ->; cbn. unfold force_dem. rewrite Nat.add_0_r. auto.
  - intros; apply optimistic_bind.
    refine (optimistic_mon (minimal_ex Cf _ _ _ _ H0 H1) _).
    { constructor; auto. }
    intros ? ? [-> Hb]; inv Hb.
    apply (optimistic_force eq_refl).
    split; auto.
  - intros; apply pessimistic_bind.
    apply (pessimistic_mon (minimal_univ Cf _ H)).
    intros. apply pessimistic_force.
    intros ? -> ? ?. unfold force_dem. rewrite Nat.add_0_r.
    apply H0. constructor; auto.
Qed.

Fixpoint foldr_fn' {A B : Type} (fb : A -> B -> B) (b : B) (a : list A) : B :=
  match a with
  | nil => b
  | cons x y => fb x (foldr_fn' fb b y)
  end.

Definition foldr_fn {G A B : Type} (fb : (G * A) * B -> B) (fn : G -> B) (fa : G -> list A)
  : G -> B := fun g => foldr_fn' (fun a b => fb ((g, a), b)) (fn g) (fa g).

Fixpoint foldr_dem' `{IsAA G G', IsAA A A', IsAA B B'}
    (lb : Lens ((G * A) * B) ((G' * T A') * T B') B B') (ln : Lens G G' B B')
    (g : G) (a : list A) (b : B') : Tick (G' * listA A') :=
    match a with
    | nil => let+ g' := put ln g b in Tick.ret (g', NilA)
    | cons a0 a =>
      let+ ((g', a0'), Tb0) := put lb ((g, a0), foldr_fn (get lb) (get ln) (fun _ => a) g) b in
      let+ (g'', a') := match Tb0 with
                         | Undefined => Tick.ret (bottom_of (exact g), Undefined)
                         | Thunk b0 => let+ (g'', a') := foldr_dem' lb ln g a b0 in
                                       Tick.ret (g'', Thunk a')
                         end in
      Tick.ret (lub g' g'', ConsA a0' a')
    end%tick.

Definition foldr_dem `{IsAA G G', IsAA A A', IsAA B B'}
    (lb : Lens ((G * A) * B) ((G' * T A') * T B') B B') (ln : Lens G G' B B')
    (la : Lens G G' (list A) (listA A'))
  : G -> B' -> Tick G' :=
  fun g b => (
    let+ (g', a) := foldr_dem' lb ln g (get la g) b in
    let+ g'' := put la g a in
    Tick.ret (lub g' g''))%tick.

Definition foldr_lens `{IsAA G G', IsAA A A', IsAA B B'}
    (lb : Lens ((G * A) * B) ((G' * T A') * T B') B B') (ln : Lens G G' B B')
    (la : Lens G G' (list A) (listA A'))
  : Lens G G' B B' :=
  MkLens (foldr_fn (get lb) (get ln) (get la)) (foldr_dem lb ln la).

Fixpoint foldr_cv' {A B} (f : T A -> T B -> M B) (n : M B) (a : listA A) : M B :=
  match a with
  | NilA => n
  | ConsA x Ta' =>
    let~ b :=
      forcing Ta' (fun a' =>
      foldr_cv' f n a') in
    f x b
  end.

Definition foldr_cv `{IsAA G G', IsAA A A', IsAA B B'}
    (fb : (G' * T A') * T B' -> M B') (fn : G' -> M B')
    (fa : G' -> M (listA A'))
  : G' -> M B' :=
  fun g =>
    let! xs := fa g in
    foldr_cv' (fun a b => fb (g, a, b)) (fn g) xs.

Lemma complete_foldr' `{IsAA G G', IsAA A A', IsAA B B'}
    (lb : Lens ((G * A) * B) ((G' * T A') * T B') B B') (ln : Lens G G' B B')
  : Good lb -> Good ln ->
    forall g (a : list A) b',
      b' `is_approx` foldr_fn' (fun a b => get lb ((g, a), b)) (get ln g) a ->
      Tick.val (foldr_dem' lb ln g a b') `is_approx` (g, a).
Proof.
  intros Gb Gn g; induction a; cbn; intros.
  - constructor; [ apply Gn; auto | reflexivity ].
  - destruct (Tick.val (put _ _ _)) as [ [g' a0'] Tb0] eqn:E1. cbn.
    destruct (Tick.val (match Tb0 with Thunk _ => _ | Undefined => _ end)) eqn:E2.
    cbn.
    assert (F1 : (g', a0', Tb0) `is_approx` (g, a, foldr_fn' (fun a b => get lb (g, a, b)) (get ln g) a0)).
    { rewrite <- E1; apply Gb. auto. }
    inv F1; cbn in *. inv fst_rel; cbn in *.
    assert (F2 : (g0, t) `is_approx` (g, a0)).
    { rewrite <- E2. destruct Tb0; cbn.
      { inv snd_rel. specialize (IHa _ H2).
        destruct (Tick.val (foldr_dem' lb ln g a0 x)). cbn; constructor; cbn.
        - apply IHa.
        - constructor; apply IHa. }
      { constructor; [ apply bottom_is_less | constructor ]. } }
    inv F2; cbn in *.
    constructor; [ apply lub_least_upper_bound; cbn; auto | cbn ].
    simp exact. constructor; auto.
Qed.

Ltac montac :=
  match goal with
  | [ |- Tick.bind ?u _ `less_defined` Tick.bind ?v _ ] =>
    let H := fresh in
    assert (H : u `less_defined` v); [ | apply (less_defined_bind' H); destruct H; clear H ]
  end.

Lemma monotone_foldr' `{IsAA G G', IsAA A A', IsAA B B'}
    {lb : Lens ((G * A) * B) ((G' * T A') * T B') B B'} {ln : Lens G G' B B'}
  : Good lb -> Good ln ->
    forall g (a : list A) b' b'',
      b'' `is_approx` foldr_fn' (fun a b => get lb ((g, a), b)) (get ln g) a ->
      b' `less_defined` b'' ->
      foldr_dem' lb ln g a b' `less_defined` foldr_dem' lb ln g a b''.
Proof.
  intros Gb Gn g; induction a; cbn; intros.
  - apply less_defined_bind; [ apply Gn; auto | ].
    intros; apply less_defined_ret; constructor; [ auto | reflexivity ].
  - montac. { apply Gb; auto. }
    assert (Tick.val (put lb
          (g, a, foldr_fn' (fun (a : A) (b : B) => get lb (g, a, b)) (get ln g) a0) b'')
          `is_approx` (g, a, foldr_fn' (fun (a : A) (b : B) => get lb (g, a, b)) (get ln g) a0)).
    { apply Gb; auto. }
    destruct (Tick.val (put lb _ _)) as [ [g' a0'] Tb0' ].
    destruct (Tick.val (put lb _ _)) as [ [g1' a01'] Tb01' ].
    destruct H2 as [ [J1 J2] J3 ]; cbn in *.
    destruct H1 as [ [J4 J5] J6 ]; cbn in *.
    montac. { inv J3.
      + constructor; [ apply Nat.le_0_l | ]. constructor; cbn.
        * apply bottom_is_least. inv J6.
          { apply bottom_is_less. }
          assert (H1 : Tick.val (foldr_dem' lb ln g a0 x) `is_approx` (g, a0)); cbn.
          { apply (complete_foldr' Gb Gn). auto. }
          destruct (Tick.val (foldr_dem' _ _ _ _ _)) as [g'' a']; cbn. apply H1.
        * constructor.
      + inv J6. apply less_defined_bind.
        { apply IHa; auto. }
        intros [] [] []; cbn in *.
        apply less_defined_ret. constructor; [ | constructor]; auto. }
    match type of H2 with (_ `less_defined` ?v) => assert (v `is_approx` (g, a0)) end.
    { inv J6.
      + split; [ apply bottom_is_less | constructor ].
      + cbn.
        assert (H1 : Tick.val (foldr_dem' lb ln g a0 x) `is_approx` (g, a0)); cbn.
        { apply (complete_foldr' Gb Gn). auto. }
        destruct H1; cbn in *.
        destruct (Tick.val (foldr_dem' _ _ _ _ _)); cbn; constructor; [ | constructor ]; cbn; auto. }
    destruct (Tick.val (match Tb0' with _ => _ end)) as [g'' a'].
    destruct (Tick.val (match Tb01' with _ => _ end)) as [g1'' a1'].
    inv H2; inv H1; cbn in *.
    apply less_defined_ret. constructor; cbn; [ | constructor; auto ].
    apply less_defined_lub; eauto.
Qed.

Lemma homomorphic_foldr' `{IsAA G G', IsAA A A', IsAA B B'}
    {lb : Lens ((G * A) * B) ((G' * T A') * T B') B B'} {ln : Lens G G' B B'}
  : Good lb -> Good ln ->
    forall g (a : list A) b' b'',
      b'  `is_approx` foldr_fn' (fun a b => get lb ((g, a), b)) (get ln g) a ->
      b'' `is_approx` foldr_fn' (fun a b => get lb ((g, a), b)) (get ln g) a ->
      eqle (foldr_dem' lb ln g a (lub b' b''))
           (lift2_lub (foldr_dem' lb ln g a b') (foldr_dem' lb ln g a b'')).
Proof.
  intros Gb Gn. intros g. induction a; cbn; intros.
  - apply (lub_bind (P := fun g' => g' `is_approx` g)).
    { apply Gn; auto. }
    { apply Gn; auto. }
    { apply (homomorphic Gn); auto. }
    intros. apply lub_ret. apply (f_equal2 pair); cbn; [ auto | reflexivity ].
  - apply (lub_bind (P := fun gab => gab `is_approx` (g, a, foldr_fn' (fun (a1 : A) (b : B) => get lb (g, a1, b)) (get ln g) a0))).
    { apply Gb; auto. }
    { apply Gb; auto. }
    { apply Gb; auto. }
    intros [ [] ? ] [ [] ? ] ? [ [Eg' Ea0'] ETb0 ] [ [Eg1 Ea1] ETb1 ]. cbn in *.
    assert (ETb_ : lub t0 t2 `is_approx` (foldr_fn' (fun a b => get lb (g, a, b)) (get ln g) a0)).
    { apply lub_least_upper_bound; eauto. }
    change (Lub_T t0 t2) with (lub t0 t2).
    pose (p := fun t0 => Tick.val match t0 with
         | Thunk b0 =>
             let+ (g'', a') := foldr_dem' lb ln g a0 b0
             in Tick.ret (g'', Thunk a')
         | Undefined => Tick.ret (bottom_of (exact g), Undefined)
         end%tick).
    assert (Hp : forall t0,
        t0 `is_approx` (foldr_fn' (fun a b => get lb (g, a, b)) (get ln g) a0) ->
        p t0 `is_approx` (g, a0)).
    { intros ? EE; inv EE.
      { cbn. constructor; [ apply bottom_is_less | constructor ]. }
      assert (Tick.val (foldr_dem' lb ln g a0 x) `is_approx` (g, a0)).
      { apply complete_foldr'; auto. }
      cbn. destruct (Tick.val (foldr_dem' lb ln g a0 x)). inv H1. cbn in *.
      constructor; [ auto | constructor; auto ]. }
    apply (lub_bind (P := fun ga => ga `is_approx` (g, a0))).
    { apply Hp; auto. }
    { apply Hp; auto. }
    { assert (W : forall x,
        x `is_approx` foldr_fn' (fun a b => get lb (g, a, b)) (get ln g) a0 ->
        Tick.val (foldr_dem' lb ln g a0 x) `is_approx` (g, a0)).
      { intros x. apply complete_foldr'; auto. }
      inv ETb0; inv ETb1; cbn.
      + apply lift2_lub_idempotent.
      + apply lift2_lub_r. cbn. constructor; [ cbn | constructor ].
        apply bottom_is_least. specialize (W _ H3).
        destruct (Tick.val (foldr_dem' lb ln g a0 x)); apply W.
      + apply lift2_lub_l. cbn. constructor; [ cbn | constructor ].
        apply bottom_is_least. specialize (W _ H3).
        destruct (Tick.val (foldr_dem' lb ln g a0 x)); apply W.
      + apply (lub_bind (P := fun _ => True)).
        { auto. }
        { auto. }
        { apply IHa; auto. }
        intros [] [] ? ? ?. cbn. apply lub_ret.
        reflexivity. }
    intros [g'' a'] [] ? [Eg'' Ea'] []; cbn in *.
    apply lub_ret. apply (f_equal2 pair); cbn.
    { eapply lub_comm4; eauto. }
    change (lub_T lub) with (lub (a := T (listA A'))).
    f_equal.
Qed.

Theorem Good_foldr `{IsAA G G', IsAA A A', IsAA B B'}
    (lb : Lens ((G * A) * B) ((G' * T A') * T B') B B') (ln : Lens G G' B B')
    (la : Lens G G' (list A) (listA A'))
  : Good lb -> Good ln -> Good la -> Good (foldr_lens lb ln la).
Proof.
  intros Gb Gn Ga. unfold foldr_lens; constructor; cbn; intros.
  - destruct (Tick.val (foldr_dem' lb ln a (get la a) b')) as [g' a0] eqn:Ef.
    cbn. assert (F : (g', a0) `is_approx` (a, get la a)).
    { rewrite <- Ef. apply (complete_foldr' Gb Gn). auto. }
    apply lub_least_upper_bound.
    + change g' with (fst (g', a0)). apply F.
    + apply Ga, F.
  - unfold foldr_dem. montac. { apply (monotone_foldr' Gb Gn); auto. }
    apply (complete_foldr' Gb Gn) in H0.
    destruct (Tick.val (foldr_dem' _ _ _ _ b')).
    destruct (Tick.val (foldr_dem' _ _ _ _ b'')).
    destruct H0, H2; cbn in *.
    montac. { apply Ga; auto. }
    assert (Tick.val (put la a l0) `is_approx` a). { apply Ga; auto. }
    apply less_defined_ret. apply less_defined_lub; eauto.
  - unfold foldr_dem.
    apply (lub_bind (P := fun ga => ga `is_approx` (a, get la a))).
    { apply complete_foldr'; auto. }
    { apply complete_foldr'; auto. }
    { apply homomorphic_foldr'; auto. }
    intros [g' a'] [] ? [Eg' Ea'] []. cbn in *.
    apply (lub_bind (P := fun g'' => g'' `is_approx` a)).
    { apply Ga; auto. }
    { apply Ga; auto. }
    { apply (homomorphic Ga); auto. }
    intros g2 g3 ? Eg2 Eg3.
    apply lub_ret. erewrite lub_comm4; eauto.
Qed.

Theorem fcorrect_foldr' `{IsAA G G', IsAA A A', IsAA B B'}
    (lb : Lens ((G * A) * B) ((G' * T A') * T B') B B') (ln : Lens G G' B B')
    (fb : (G' * T A') * T B' -> M B') (fn : G' -> M B')
  : Correct lb fb -> Correct ln fn ->
    forall (g : G) (g' : G'), g' `is_approx` g ->
    forall (a : list A) (a' : listA A'), a' `is_approx` a ->
    foldr_cv' (fun x' b' => fb (g', x', b')) (fn g') a' {{ fun b' n =>
      b' `is_approx` foldr_fn' (fun x b => get lb (g, x, b)) (get ln g) a }}.
Proof.
  intros Cb Cn g g' Eg a. induction a; intros a' Ea; inv Ea; cbn.
  - apply (pessimistic_mon (functional_correct Cn _ _ Eg)).
    intros b _ Eb. auto.
  - apply pessimistic_bind. apply pessimistic_thunk.
    + apply pessimistic_forcing. intros x0 ->. inv H3.
      apply (pessimistic_mon (IHa _ H1)).
      intros b1 _ Eb1.
      apply (functional_correct Cb (g, a, (foldr_fn' (fun a b => get lb (g, a, b)) (get ln g) a0))).
      repeat constructor; auto.
    + apply (functional_correct Cb (g, a, (foldr_fn' (fun a b => get lb (g, a, b)) (get ln g) a0))).
      repeat constructor; auto.
Qed.

Lemma less_defined_bind'' {a b : Type} {H : LessDefined a} {H0 : LessDefined b}
    (P : a -> a -> Prop) :
    forall (u u' : Tick a), u `less_defined` u' ->
    P (Tick.val u) (Tick.val u') ->
    forall k k' : a -> Tick b,
    (forall x x' : a, P x x' -> x `less_defined` x' -> k x `less_defined` k' x') ->
    (let+ x := u in k x)%tick `less_defined` (let+ x := u' in k' x)%tick.
Proof.
  intros. constructor; cbn.
  - apply Nat.add_le_mono; [ apply H1 | apply H3 ]; auto. apply H1.
  - apply H3; [ apply H2 | apply H1 ].
Qed.

Theorem underapprox_foldr' `{IsAA G G', IsAA A A', IsAA B B'}
    (lb : Lens ((G * A) * B) ((G' * T A') * T B') B B') (ln : Lens G G' B B')
    (fb : (G' * T A') * T B' -> M B') (fn : G' -> M B')
  : Correct lb fb -> Correct ln fn ->
    forall (g : G) (g' : G'), g' `is_approx` g ->
    forall (a : list A) (a' : listA A'), a' `is_approx` a ->
    foldr_cv' (fun x' b' => fb (g', x', b')) (fn g') a' {{ fun b' n =>
      foldr_dem' lb ln g a b' `less_defined` Tick.MkTick n (g', a') }}.
Proof.
  intros Cb Cn g g' Eg a. induction a; intros a' Ea; inv Ea; cbn.
  - apply (pessimistic_mon (underapprox Cn _ Eg)).
    intros b' n Eb. constructor; cbn.
    + rewrite Nat.add_0_r. apply Eb.
    + constructor; [ apply Eb | constructor ].
  - apply pessimistic_bind. apply pessimistic_thunk.
    + apply pessimistic_forcing. intros x0 ->. inv H3.
      apply (pessimistic_mon (@pessimistic_conj _ _ _ _ (IHa _ H1) (fcorrect_foldr' Cb Cn g g' Eg a0 H1))).
      intros b1 n [ Eb1 Eb2 ].
      refine (pessimistic_mon (underapprox Cb (g, a, (foldr_fn' (fun a b => get lb (g, a, b)) (get ln g) a0)) _) _).
      { repeat constructor; cbn; try assumption. }
      intros b2 m Hb2. rewrite (Nat.add_comm n m).
      change (Tick.MkTick _ _) with (Tick.bind (Tick.MkTick m (g', x, Thunk b1)) (fun _ =>
        Tick.MkTick n (g', ConsA x (Thunk x0)))).
      apply (less_defined_bind'' (fun _ w => w = (g', x, Thunk b1))); [ auto .. | ].
      intros [ [ g3 x3 ] b3 ] _ -> [ [Eg3 Ex3] Eb3 ] . cbn in *.
      rewrite <- (Nat.add_0_r n).
      change (Tick.MkTick _ _) with (Tick.bind (Tick.MkTick n (g', Thunk x0)) (fun _ => Tick.ret (g', ConsA x (Thunk x0)))).
      apply (less_defined_bind'' (fun _ w => w = (g', Thunk x0))).
      { inv Eb3.
        * constructor; cbn; [ apply Nat.le_0_l | ].
          constructor; [ | constructor ].
          apply bottom_is_least; cbn; auto.
        * rewrite <- (Nat.add_0_r n). change (Tick.MkTick _ _) with (Tick.bind
            (Tick.MkTick n (g', x0)) (fun '(g', x0) => Tick.ret (g', Thunk x0))).
          apply less_defined_bind; [ | ].
          { etransitivity; [ | eassumption ].
            apply monotone_foldr'; eauto. }
          intros [] [] []; repeat constructor; cbn; auto.
      }
      { auto. }
      { intros [] _ -> []. cbn in *. apply less_defined_ret.
        repeat constructor; cbn; auto.
        apply lub_least_upper_bound; auto.
      }
    + refine (pessimistic_mon (underapprox Cb (g, a, (foldr_fn' (fun a b => get lb (g, a, b)) (get ln g) a0)) _) _).
      { repeat constructor; cbn; try assumption. }
      intros b2 m Hb2. rewrite <- (Nat.add_0_r m).
      change (Tick.MkTick _ _) with (Tick.bind (Tick.MkTick m (g', x, Undefined (a := B'))) (fun _ =>
        Tick.MkTick 0 (g', ConsA x xs))).
      apply (less_defined_bind'' (fun _ w => w = (g', x, Undefined))); [ auto .. | ].
      intros [ [ g3 x3 ] b3 ] _ -> [ [Eg3 Ex3] Eb3 ] . cbn in *.
      inv Eb3; cbn.
      repeat constructor; cbn; auto.
      apply lub_least_upper_bound; auto.
      apply bottom_is_least; auto.
Qed.

Theorem minimal_ex_foldr' `{IsAA G G', IsAA A A', IsAA B B'}
    (lb : Lens ((G * A) * B) ((G' * T A') * T B') B B') (ln : Lens G G' B B')
    (fb : (G' * T A') * T B' -> M B') (fn : G' -> M B')
  : Correct lb fb -> Correct ln fn ->
    forall g a b', b' `is_approx` foldr_fn' (fun x b => get lb (g, x, b)) (get ln g) a ->
    forall g', g' `is_approx` g ->
    forall a', a' `is_approx` a ->
    Tick.val (foldr_dem' lb ln g a b') `less_defined` (g', a') ->
    foldr_cv' (fun x' b' => fb (g', x', b')) (fn g') a' [[ fun b'' n =>
      n = Tick.cost (foldr_dem' lb ln g a b') /\ b' `less_defined` b'' ]].
Proof.
  intros Cb Cn g. induction a; intros b' Eb g' Eg a' Ea Efold; inv Ea; cbn in *.
  - destruct Efold as [Eg' _]; cbn in Eg'.
    apply (optimistic_mon (minimal_ex Cn g b' Eb g' Eg Eg')).
    intros *; rewrite Nat.add_0_r; auto.
  - destruct (Tick.val (put lb (g, a, foldr_fn' (fun x b => get lb (g, x, b)) (get ln g) a0) b'))
      as [ [g2 a2] b2] eqn:E2.
    assert (E2' : (g2, a2, b2) `is_approx` (g, a, foldr_fn' (fun x b => get lb (g, x, b)) (get ln g) a0)).
    { rewrite <- E2; apply (complete (Good_correct Cb)); auto. }
    destruct E2' as [ [Eg2 Ea2] Eb2 ]; cbn in *.
    apply optimistic_bind.
    inv Eb2.
    + apply optimistic_skip.
      cbn in Efold. destruct Efold as [Eg' Exs]; cbn in *.
      rewrite lub_bottom_of_r in Eg'; auto.
      inv Exs.
      refine (optimistic_mon
        (minimal_ex Cb (g, a, foldr_fn' (fun x b => get lb (g, x, b)) (get ln g) a0) _ Eb _ _ _) _).
      { repeat constructor; auto. }
      { rewrite E2. repeat constructor; cbn; auto. }
      { intros b3 n. rewrite Nat.add_0_r. auto. }
    + apply optimistic_thunk_go. cbn in Efold.
      destruct (Tick.val (foldr_dem' lb ln g a0 x0)) as [g3 a3] eqn:E3. cbn in *.
      assert (H3' : (g3, a3) `is_approx` (g, a0)).
      { rewrite <- E3. apply complete_foldr'; eauto. }
      destruct H3' as [Eg3 Ea3].
      destruct Efold as [Eg3' Exs]. inv Exs. inv H7. inv H3.
      cbn in *.
      refine (optimistic_mon
        (optimistic_conj (fcorrect_foldr' Cb Cn _ _ Eg _ H6)  (IHa _ H1 _ Eg _ H6 _)) _).
      { rewrite E3. constructor; cbn.
        { etransitivity; [ | apply Eg3' ]. apply lub_upper_bound_r. eauto. }
        { auto. } }
      intros b3 _ [Eb3 [-> Ex] ].
      refine (optimistic_mon
        (minimal_ex Cb (g, a, foldr_fn' (fun x b => get lb (g, x, b)) (get ln g) a0) _ Eb _ _ _) _).
      { repeat constructor; cbn; eauto. }
      { rewrite E2. repeat constructor; cbn; auto.
        etransitivity; [ | apply Eg3' ].
        apply lub_upper_bound_l; eauto. }
      intros b4 _ [ -> Eb4].
      rewrite E3; cbn. split; [ lia | auto ].
Qed.

Lemma Tick_bind_bind {a b c} {u : Tick a} {k : a -> Tick b} {h : b -> Tick c}
  : Tick.bind (Tick.bind u k) h = Tick.bind u (fun x => Tick.bind (k x) h).
Proof.
  cbv [Tick.bind Tick.cost Tick.val]; f_equal. lia.
Qed.

Theorem minimal_univ_foldr' `{IsAA G G', IsAA A A', IsAA B B'}
    (lb : Lens ((G * A) * B) ((G' * T A') * T B') B B') (ln : Lens G G' B B')
    (fb : (G' * T A') * T B' -> M B') (fn : G' -> M B')
  : Correct lb fb -> Correct ln fn ->
    forall g g', g' `is_approx` g ->
    forall a a', a' `is_approx` a ->
    foldr_cv' (fun x' b' => fb (g', x', b')) (fn g') a' {{ fun b'' n =>
      forall  b', b' `less_defined` b'' ->
      foldr_dem' lb ln g a b' `less_defined` Tick.MkTick n (g', a') }}.
Proof.
  intros Cb Cn g g' Eg. induction a; intros a' Ea; inv Ea; cbn in *.
  - apply (pessimistic_mon (minimal_univ Cn g Eg)).
    intros b'' n F b' Hb; specialize (F b' Hb).
    etransitivity; [ apply less_defined_bind with (k := ?[k]) (k' := ?k); [ apply F | ] | ].
    { intros; apply less_defined_ret; constructor; [ auto | constructor ]. }
    constructor; cbn. { lia. } { reflexivity. }
  - apply pessimistic_bind. apply pessimistic_thunk; cycle 1.
    + refine (pessimistic_mon
        (minimal_univ Cb (g, a, foldr_fn' (fun x b => get lb (g, x, b)) (get ln g) a0) _) _).
      { repeat constructor; auto. }
      intros b3 n F b3' Hb3; specialize (F b3' Hb3). cbn.
      rewrite <- (Nat.add_0_r n).
      change (Tick.MkTick (n + 0) _) with (let+ (g'0, a0', Tb0) := Tick.MkTick n (g', x, Undefined (a := B')) in
                                     Tick.MkTick 0 (g', ConsA x xs))%tick.
      apply (less_defined_bind'' (fun _ gxb => gxb = (g', x, Undefined))); auto.
      intros [ [g4 x4] b4] _ -> H4. destruct H4 as [ [Hg4 Hx4] Hb4]; inv Hb4; cbn in *; subst b4.
      repeat (constructor; cbn; auto).
      apply lub_least_upper_bound; auto.
      apply bottom_is_least; auto.
    + apply pessimistic_forcing. intros xs' ->. inv H3.
      apply (pessimistic_mon (pessimistic_conj (fcorrect_foldr' Cb Cn _ _ Eg _ H1) (IHa _ H1))).
      intros b3 n [Eb3 F].
      refine (pessimistic_mon (pessimistic_conj (functional_correct Cb (g, a, _) _ _) (minimal_univ Cb (g, a,  _) _)) _).
      1,2: repeat constructor; eauto.
      intros b4 m [Eb4 F4] b4' E4.
      rewrite (Nat.add_comm n m).
      change (Tick.MkTick (m + n) _) with (let+ _ := Tick.MkTick m (g', x, Thunk b3) in Tick.MkTick n (g', ConsA x (Thunk xs')))%tick.
      apply (less_defined_bind'' (fun _ gab => gab = (g', x, Thunk b3))); [ auto .. | ].
      intros [ [ g5 x5] b5 ] _ -> [ [Eg5 Ex5] Eb5]; cbn in *.
      inv Eb5.
      { constructor; cbn; [ lia | ].
        repeat constructor; cbn; auto.
        apply lub_least_upper_bound; [ auto | apply bottom_is_least; auto ]. }
      rewrite Tick_bind_bind; cbn.
      rewrite <- (Nat.add_0_r n).
      change (Tick.MkTick (n + 0) _) with (let+ x1 := Tick.MkTick n (g', xs') in Tick.MkTick 0 (g', ConsA x (Thunk xs')))%tick.
      apply (less_defined_bind'' (fun _ ga => ga = (g', xs'))); auto.
      intros [g6 x6] _ -> [Eg6 Ex6]; cbn in *.
      repeat (constructor; cbn; auto).
      apply lub_least_upper_bound; eauto.
Qed.

Theorem Correct_foldr `{IsAA G G', IsAA A A', IsAA B B'}
    (lb : Lens ((G * A) * B) ((G' * T A') * T B') B B') (ln : Lens G G' B B')
    (la : Lens G G' (list A) (listA A'))
    (fb : (G' * T A') * T B' -> M B') (fn : G' -> M B')
    (fa : G' -> M (listA A'))
  : Correct lb fb -> Correct ln fn -> Correct la fa -> Correct (foldr_lens lb ln la) (foldr_cv fb fn fa).
Proof.
  intros Cb Cn Ca. constructor; cbn; intros; unfold foldr_cv.
  - apply Good_foldr; eauto using @Good_correct.
  - apply pessimistic_bind.
    apply (pessimistic_mon (functional_correct Ca _ _ H)).
    intros x _ Ex.
    apply (pessimistic_mon (fcorrect_foldr' Cb Cn _ _ H _ Ex)).
    intros b' _ Eb'. apply Eb'.
  - apply pessimistic_bind.
    apply (pessimistic_mon (pessimistic_conj (functional_correct Ca _ _ H) (underapprox Ca _ H))).
    intros x n [Ex Fx].
    apply (pessimistic_mon (underapprox_foldr' Cb Cn _ H _ Ex)).
    intros. unfold foldr_dem.
    rewrite (Nat.add_comm n n0).
    change (Tick.MkTick (n0 + n) _) with (Tick.bind (Tick.MkTick n0 (a', x)) (fun _ => Tick.MkTick n a')).
    apply (less_defined_bind'' (fun _ ax => ax = (a', x))); auto.
    intros [g1 x1] _ -> [Eg1 Ex2]; cbn in *.
    rewrite <- (Nat.add_0_r n).
    change (Tick.MkTick (n + 0) _) with (Tick.MkTick n a' >> Tick.MkTick 0 a')%tick.
    apply (less_defined_bind'' (fun _ a2 => a2 = a')); auto.
    { etransitivity; [ | apply Fx ].
      apply (monotone (Good_correct Ca)); auto. }
    intros g2 _ -> Eg2.
    apply less_defined_ret. apply lub_least_upper_bound; auto.
  - apply optimistic_bind.
    unfold foldr_fn in H.
    destruct (Tick.val (foldr_dem' lb ln a (get la a) b')) as [g' x'] eqn:Ef'.
    assert (Hgx : (g', x') `is_approx` (a, get la a)).
    { rewrite <- Ef'. apply complete_foldr'; eauto. }
    destruct Hgx as [Hg Hx]; cbn in *.
    assert (Hp : Tick.val (put la a x') `less_defined` a').
    { apply lub_inv in H1; [ apply H1 | ].
      eexists; split; [ apply Hg | apply complete; eauto ]. }
    apply (optimistic_mon (optimistic_conj (functional_correct Ca _ _ H0) (minimal_ex Ca _ _ Hx _ H0 Hp))).
    intros x _ [Hg0 [-> Ex] ].
    refine (optimistic_mon (minimal_ex_foldr' Cb Cn _ _ _ H H0 Hg0 _) _).
    { rewrite Ef'. constructor; cbn; auto.
      etransitivity; [ | apply H1 ].
      apply lub_upper_bound_l; eexists; split; [ | etransitivity ]; eauto. }
    intros b _ [-> Eb]. split; [ lia | auto ].
  - apply pessimistic_bind.
    apply (pessimistic_mon (pessimistic_conj (functional_correct Ca _ _ H) (minimal_univ Ca _ H))).
    intros x n [Hx Fx].
    apply (pessimistic_mon (minimal_univ_foldr' Cb Cn _ H _ Hx)).
    intros b m Fb b' Eb'.
    unfold foldr_dem.
    rewrite (Nat.add_comm n m).
    change (Tick.MkTick (m + n) _) with (Tick.MkTick m (a', x) >> Tick.MkTick n a')%tick.
    apply (less_defined_bind'' (fun _ ax => ax = (a', x))); auto.
    intros [g1 x1] _ -> [Eg Ex]; cbn in *.
    rewrite <- (Nat.add_0_r n).
    change (Tick.MkTick (n + 0) _) with (Tick.MkTick n a' >> Tick.MkTick 0 a')%tick.
    apply (less_defined_bind'' (fun _ a'' => a'' = a')); auto.
    intros g2 _ -> Eg2.
    apply less_defined_ret.
    apply lub_least_upper_bound; auto.
Qed.

Definition nil_lens `{IsAA G G'} {A A'} : Lens G G' (list A) (listA A') :=
  MkLens (fun _ => nil) (fun g _ => Tick.ret (bottom_of (exact g))).

Definition nil_cv {G A} : G -> M (listA A) :=
  fun _ => ret NilA.

Theorem Good_nil `{IsAA G G', IsAA A A'} : Good (nil_lens (G := G) (A := A)).
Proof.
  constructor; unfold nil_lens; cbn; auto.
  - intros; apply bottom_is_less.
  - intros; reflexivity.
  - intros; constructor; cbn; auto.
    symmetry; apply lub_idempotent.
Qed.

Theorem Correct_nil `{IsAA G G', IsAA A A'} : Correct (nil_lens (G := G) (A := A)) nil_cv.
Proof.
  constructor; cbn; unfold nil_cv.
  - apply Good_nil.
  - intros; apply pessimistic_ret. constructor.
  - intros; apply pessimistic_ret. apply less_defined_ret. apply bottom_is_least; auto.
  - intros; apply optimistic_ret. split; auto.
  - intros; apply pessimistic_ret; intros.
    apply less_defined_ret. apply bottom_is_least; auto.
Qed.

Fixpoint den_lens {A B} (t : tm A B)
  : Lens (carrier (den_ty A)) (approx (den_ty A)) (carrier (den_ty B)) (approx (den_ty B)) :=
  match t with
  | Var => id_lens
  | Fst t => fst_lens (den_lens t)
  | Snd t => snd_lens (den_lens t)
  | Pair t u => pair_lens (den_lens t) (den_lens u)
  | Foldr t u v => foldr_lens (IsAA1 := AA_IsAA (den_ty _)) (IsAA2 := AA_IsAA (den_ty _)) (den_lens t) (den_lens u) (den_lens v)
  | Tik t => tick_lens (den_lens t)
  | Lazy t => lazy_lens (den_lens t)
  | Force t => force_lens (den_lens t)
  | Nil => nil_lens
  | Cons t u => cons_lens (den_lens t) (den_lens u)
  | Boo b => boo_lens b
  end.

Fixpoint den_cv {A B} (t : tm A B) : approx (den_ty A) -> M (approx (den_ty B)) :=
  match t with
  | Var => id_cv
  | Fst t => fst_cv (den_cv t)
  | Snd t => snd_cv (den_cv t)
  | Pair t u => pair_cv (den_cv t) (den_cv u)
  | Foldr t u v => foldr_cv (den_cv t) (den_cv u) (den_cv v)
  | Tik t => tick_cv (den_cv t)
  | Lazy t => lazy_cv (den_cv t)
  | Force t => force_cv (den_cv t)
  | Nil => nil_cv
  | Cons t u => cons_cv (den_cv t) (den_cv u)
  | Boo b => boo_cv b
  end.

Theorem Good_den {A B} (t : tm A B) : Good (den_lens t).
Proof.
  induction t; cbn.
  - apply Good_id. - apply Good_fst; auto. - apply Good_snd; auto. - apply Good_pair; auto.
  - apply Good_boo. - apply Good_tick; auto. - apply Good_lazy; auto. - apply Good_force; auto.
  - apply Good_nil. - apply Good_cons; auto. - apply Good_foldr; auto.
Qed.

Theorem Correct_den {A B} (t : tm A B) : Correct (den_lens t) (den_cv t).
Proof.
  induction t; cbn.
  - apply Correct_id. - apply Correct_fst; auto. - apply Correct_snd; auto.
  - apply Correct_pair; auto. - apply Correct_boo. - apply Correct_tick; auto.
  - apply Correct_lazy; auto. - apply Correct_force; auto.
  - apply Correct_nil. - apply Correct_cons; auto. - apply Correct_foldr; auto.
Qed.

Print Assumptions Correct_den.
