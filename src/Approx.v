Set Implicit Arguments.
Set Maximal Implicit Insertion.
Set Contextual Implicit.

From Coq Require Import Arith List Psatz Morphisms Relations.
From Clairvoyance Require Import Core.

Definition is_defined {a} (t : T a) : Prop :=
  match t with
  | Thunk _ => True
  | Undefined => False
  end.

(* --------------------------------------- *)

(** * Approximations.
    
    This part is a reference implementation of the definitions discussed in
    Section 5.3.  *)

(** In the paper, we start by giving an [exact] function defined on lists. We
    mention later in the section that we would also want to be able to overload
    the [exact] function (and the [is_approx] and [less_defined] relations) for
    other types. One way of doing that is using type classes, as we show here. *)

(** * [exact] *)
Class Exact a b : Type := exact : a -> b.

#[global] Hint Unfold exact : core.

#[global]
Instance Exact_T {a b} {r: Exact a b} : Exact a (T b) 
  := fun x => Thunk (exact x).

#[global] Hint Unfold Exact_T : core.

(* Type classes declared under this will have less confusing resolution.
   We exclude [Exact] because in [Exact a b],
   [b] is supposed to be determined by [a]. *)
Set Typeclasses Strict Resolution.

(** * [less_defined] *)
Class LessDefined a := less_defined : a -> a -> Prop.
Infix "`less_defined`" := less_defined (at level 42).

#[global] Hint Unfold less_defined : core.

Inductive less_defined_T {a : Type} `{LessDefined a} : relation (T a) :=
| LessDefined_Undefined :
    forall x, less_defined_T Undefined x
| LessDefined_Thunk :
    forall x y, x `less_defined` y -> less_defined_T (Thunk x) (Thunk y).

#[global] Hint Constructors less_defined_T : core.

#[global]
Instance LessDefined_T {a} `{LessDefined a} : LessDefined (T a) := less_defined_T.

#[global] Hint Unfold LessDefined_T : core.

Definition less_defined_M {a} `{LessDefined  a} (u v : M a) : Prop :=
  u {{ fun x n =>
  v [[ fun y m => x `less_defined` y /\ m <= n ]] }}.

#[global] Instance LessDefined_M {a} `{LessDefined a} : LessDefined (M a) := less_defined_M.

(* Upward closed predicates *)
Definition uc {a} `{LessDefined a} (k : a -> nat -> Prop) : Prop :=
  forall x x' n n',
    x `less_defined` x' ->
    n' <= n ->
    k x n -> k x' n'.

Lemma optimistic_corelax {a} `{LessDefined a} (u u' : M a) (k : a -> nat -> Prop)
  : u `less_defined` u' -> uc k ->
    u [[ k ]] -> u' [[ k ]].
Proof.
  intros H' Hk Hu. hnf in H'. destruct Hu as (x & n & Hx & Hn).
  apply H' in Hx.
  eapply optimistic_mon; [ apply Hx | cbn; intros ? ? HH ].
  revert Hn; apply Hk; apply HH.
Qed.

(** * This corresponds to the proposition [less_defined_order] in Section 5.3. *)
Class LessDefinedOrder a (H: LessDefined a) :=
  { less_defined_preorder :> PreOrder (less_defined (a := a))
  ; less_defined_partial_order :> PartialOrder eq (less_defined (a := a)) }.

(** * This corresponds to the proposition [exact_max] in Section 5.3. *)
Class LessDefinedExact {a b} {Hless : LessDefined a}
      (Horder : LessDefinedOrder Hless) (Hexact : Exact b a) :=
  { exact_max : forall (xA : a) (x : b), exact x `less_defined` xA -> exact x = xA }.

#[global]
Instance PreOrder_LessDefined_T {a : Type} `{Ho : LessDefinedOrder a}
  : PreOrder (less_defined_T (a := a)).
Proof.
constructor.
- intros x. destruct x.
  + constructor. apply Ho.
  + constructor.
- intros x y z. inversion 1; subst; intros.
  + constructor.
  + inversion H2; subst. constructor.
    destruct Ho. transitivity y0; assumption.
Qed.

#[global]
Instance PartialOrder_LessDefined_T {a : Type} `{Ho : LessDefinedOrder a}
  : PartialOrder eq (less_defined_T (a := a)).
Proof.
constructor.
- intros ->. autounfold. constructor; reflexivity.
- inversion 1. induction H1.
  + inversion H2; reflexivity.
  + inversion H2; subst. f_equal. apply Ho. constructor; assumption.
Qed.

#[global]
Instance LessDefinedOrder_T {a} {H: LessDefined a} {Ho : LessDefinedOrder H}
  : LessDefinedOrder (less_defined_T (a := a)) :=
  {| less_defined_preorder := PreOrder_LessDefined_T ;
     less_defined_partial_order := @PartialOrder_LessDefined_T _ H Ho |}.

Lemma exact_max_T {a b} {Hless : LessDefined a}
      (Horder : LessDefinedOrder Hless) (Hexact : Exact b a)
      (Hle : LessDefinedExact Horder Hexact) :
  forall (xA : T a) (x : b), exact x `less_defined` xA -> exact x = xA.
Proof.
  destruct xA; intros.
  - inversion H; subst. unfold exact, Exact_T.
    f_equal. apply Hle. assumption.
  - inversion H.
Qed.

#[global]
Instance LessDefinedExact_T {a b} {Hless : LessDefined a} {Horder : LessDefinedOrder Hless}
         {Hexact : Exact b a} {_ : LessDefinedExact Horder Hexact}:
  LessDefinedExact (a := T a) (b := b) LessDefinedOrder_T Exact_T :=
  {| exact_max := @exact_max_T a b _ _ _ _ |}.

(** * [is_approx]
    
    In our paper, the definition of [is_approx] can be anything as long as it
    satisfies the [approx_exact] proposition. In this file, we choose the most
    direct definition that satisfies the [approx_exact] law. *)
Definition is_approx {a b} { _ : Exact b a} {_:LessDefined a} (xA : a) (x : b) : Prop := 
  xA `less_defined` exact x.
Infix "`is_approx`" := is_approx (at level 42).

(** * This corresponds to the proposition [approx_exact] in Section 5.3.

    And because of our particular definition, this is true by
    definition. However, this cannot be proved generically if the definition of
    [is_approx] can be anything. *)
Theorem approx_exact {a b} `{Exact b a} `{LessDefined a} :
  forall (x : b) (xA : a),
    xA `is_approx` x <-> xA `less_defined` (exact x).
Proof. reflexivity. Qed.
  
#[global] Hint Unfold is_approx : core.

(** * This corresponds to the proposition [approx_down] in Section 5.3.

    Again, because of the particular definition of [is_approx] we use here, this
    can be proved simply by the law of transitivity. *)
Lemma approx_down {a b} `{Hld : LessDefined a} `{Exact b a} {_ : LessDefinedOrder Hld}:
  forall (x : b) (xA yA : a),
    xA `less_defined` yA -> yA `is_approx` x -> xA `is_approx` x.
Proof.
  intros. unfold is_approx. destruct H0.
  transitivity yA; assumption.
Qed.

(**)

(* Ordered types with a least element. It represents an empty demand.
   It's also convenient as a dummy value in nonsensical cases. *)
Class Bottom (a : Type) : Type :=
  bottom : a.

#[global] Instance Bottom_T {a} : Bottom (T a) := Undefined.
#[global] Instance Bottom_prod {a b} `{Bottom a, Bottom b} : Bottom (a * b) := (bottom, bottom).

(* Least upper bound operation. *)
Class Lub (a : Type) : Type :=
  lub : a -> a -> a.

Create HintDb lub.

Definition lub_T {a} (_lub : a -> a -> a) : T a -> T a -> T a :=
  fun x y =>
    match x, y with
    | Undefined, y => y
    | x, Undefined => x
    | Thunk x, Thunk y => Thunk (_lub x y)
    end.

#[global] Instance Lub_T {a} `{Lub a} : Lub (T a) := lub_T lub.

Definition cobounded {a} `{LessDefined a} (x y : a) : Prop :=
  exists z : a, x `less_defined` z /\ y `less_defined` z.

#[global] Hint Unfold cobounded : core.

(* [lub] is defined as a total function for convenience, but it is generally partially defined,
   [lub x y] only makes sense when [x] and [y] have at least one common upper bound. *)
Class LubLaw a `{Lub a, LessDefined a} : Prop :=
  { lub_least_upper_bound : forall x y z : a,
      x `less_defined` z -> y `less_defined` z -> lub x y `less_defined` z
  ; lub_upper_bound_l : forall x y : a, cobounded x y -> x `less_defined` lub x y
  ; lub_upper_bound_r : forall x y : a, cobounded x y -> y `less_defined` lub x y
  }.

Arguments LubLaw : clear implicits.
Arguments LubLaw a {_ _}.

#[global] Hint Resolve lub_least_upper_bound lub_upper_bound_l lub_upper_bound_r : lub.

Lemma lub_inv {a} `{LubLaw a} `{!Transitive (less_defined (a := a))}
  : forall x y z : a, cobounded x y -> lub x y `less_defined` z ->
       x `less_defined` z /\ y `less_defined` z.
Proof.
  intros x y z Hxy Hlub; split; (etransitivity; eauto using lub_upper_bound_l, lub_upper_bound_r).
Qed.

#[global] Instance LubLaw_T {a} `{LubLaw a} `{!Reflexive (less_defined (a := a))} : LubLaw (T a).
Proof.
  constructor.
  - intros ? ? ? []; inversion 1; subst; cbn; constructor; auto.
    apply lub_least_upper_bound; auto.
  - intros x y [z [ [? | Hx] Hy] ]; cbn; [ constructor | ].
    inversion Hy; subst; constructor; eauto with lub.
  - intros x y [z [ Hx Hy ] ]; destruct Hy as [ | Hy]; cbn; [ constructor | ].
    inversion Hx; subst; constructor; eauto with lub.
Qed.

(**)

Inductive option_rel {a b} (r : a -> b -> Prop) : option a -> option b -> Prop :=
| option_rel_None : option_rel r None None
| option_rel_Some x y : r x y -> option_rel r (Some x) (Some y)
.

Record pair_rel {a1 b1 a2 b2} (r1 : a1 -> b1 -> Prop) (r2 : a2 -> b2 -> Prop) (xs : a1 * a2) (ys : b1 * b2) : Prop :=
  { fst_rel : r1 (fst xs) (fst ys)
  ; snd_rel : r2 (snd xs) (snd ys)
  }.

#[global] Instance Exact_prod {a aA b bA} `{Exact a aA, Exact b bA} : Exact (a * b) (aA * bA) :=
  fun xs => (exact (fst xs), exact (snd xs)).

#[global] Instance Exact_option {a aA} `{Exact a aA} : Exact (option a) (option aA) := fun ox =>
  match ox with
  | None => None
  | Some x => Some (exact x)
  end.

#[global] Instance LessDefined_option {a} `{LessDefined a} : LessDefined (option a) :=
  option_rel less_defined.

#[global] Instance LessDefinedOrder_option {a} `{LessDefinedOrder a}
  : @LessDefinedOrder (option a) _.
Proof.
Admitted.

#[global] Instance LessDefinedExact_option {a aA} `{LessDefinedExact a aA}
  : @LessDefinedExact (option a) (option aA) _ _ _.
Proof.
Admitted.

#[global] Instance LessDefined_prod {a b} `{LessDefined a, LessDefined b} : LessDefined (a * b) :=
  pair_rel less_defined less_defined.

#[global] Instance LessDefinedOrder_prod {a b} `{LessDefinedOrder a, LessDefinedOrder b}
  : @LessDefinedOrder (a * b) _.
Proof.
Admitted.

#[global] Instance LessDefinedExact_prod {a aA b bA} `{LessDefinedExact a aA, LessDefinedExact b bA}
  : @LessDefinedExact (a * b) (aA * bA) _ _ _.
Proof.
Admitted.

(** In this part, we prove that any type [a] is also an [exact] of itself. We
    define this instance so that [listA a] would be an approximation of [list
    a]---so that we do not need to consider the approximation of [a]. A useful
    simplification. *)
#[local] Instance Exact_id {a} : Exact a a := id.

(** However, if we are not careful, the [LessDefined_id] instance might be used
    everywhere. To prevent that, we give [LessDefined_id] a very low priority
    here.

    Learn more about the priority of Coq's type classes in the [Controlling
    Instantiation] section of
    [https://softwarefoundations.cis.upenn.edu/qc-current/Typeclasses.html]. *)
#[local] Instance LessDefined_id {a} : LessDefined a | 100 := eq.

#[local] Instance LessDefinedOrder_id {a} : @LessDefinedOrder a _.
Proof.
  econstructor. cbv. easy.
Qed.

#[local] Instance LessDefinedExact_id {a} : @LessDefinedExact a a _ _ _.
Proof.
  econstructor. cbv. easy.
Qed.

#[global] Hint Unfold Exact_id : core.
#[global] Hint Unfold LessDefined_id : core.

(** * Tactics for working with optimistic and pessimistic specs. *)

(** Use the monotonicity laws. *)
Ltac relax :=
  match goal with
  | [ |- _ {{ _ }} ] => eapply pessimistic_mon
  | [ |- _ [[ _ ]] ] => eapply optimistic_mon
  end.
        
Ltac relax_apply lem :=
  match goal with
  | _ => apply lem
  | _ => relax; [apply lem|]
  end.

(** Automatically apply the inference rules. *)
Ltac mforward tac :=
  lazymatch goal with
  | [ |- (ret _) {{ _ }} ] => relax_apply pessimistic_ret
  | [ |- (bind _ _) {{ _ }} ] => relax_apply pessimistic_bind
  | [ |- tick {{ _}} ] => relax_apply pessimistic_tick
  | [ |- (thunk _) {{ _ }} ] => relax_apply pessimistic_thunk
  | [ |- (force _) {{ _ }} ] => relax_apply pessimistic_force
  | [ |- (forcing _ _) {{ _ }} ] => relax_apply pessimistic_forcing
  | [ |- (ret _) [[ _ ]] ] => relax_apply optimistic_ret
  | [ |- (bind _ _) [[ _ ]] ] => relax_apply optimistic_bind
  | [ |- tick [[ _]] ] => relax_apply optimistic_tick
  | [ |- (force _) [[ _ ]] ] => relax_apply optimistic_force
  | [ |- (forcing _ _) [[ _ ]] ] => relax_apply optimistic_forcing
  | [ |- (thunk _) [[ _ ]] ] => fail
  | [ |- (fun _ _ => False) {{ _ }} ] => intros ? ? []
  | [ |- _ {{ _ }} ] => autounfold; tac
  | [ |- _ [[ _ ]] ] => autounfold; tac
  end.

(** Heuristics for dealing with approximations. *)
Ltac invert_approx :=
  match goal with
  | [H : _ `is_approx` _ |- _] =>
    inversion H; let n:= numgoals in guard n=1; subst; clear H
  | [H : _ `less_defined` _ |- _] =>
    inversion H; let n:= numgoals in guard n=1; subst; clear H
  | [H : is_defined ?x |- _] =>
    destruct x; [|contradiction]; clear H
  end.

Ltac invert_eq :=
  subst; try match goal with
             | [H : _ = _ |- _] =>
               inversion H; subst; clear H
             end.

Ltac solve_approx tac :=
  repeat (match goal with
          | _ => solve [auto]
          | [ |- _ `is_approx` _ ] =>
            repeat autounfold; tac
          | [ |- is_defined (Thunk _) ] =>
            reflexivity
          end).

(** Heuristics for reasoning about pessimistic/optimistic specs. *)
Ltac mgo tac := repeat (intros;
                        repeat invert_eq; repeat invert_approx;
                        cbn in *; (mforward tac + solve_approx tac + lia)).
Ltac mgo' := mgo idtac.
