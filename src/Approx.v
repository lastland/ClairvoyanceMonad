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

#[global]
Instance Exact_T {a b} {r: Exact a b} : Exact a (T b) 
  := fun x => Thunk (exact x).

(* Type classes declared under this will have less confusing resolution.
   We exclude [Exact] because in [Exact a b],
   [b] is supposed to be determined by [a]. *)
Set Typeclasses Strict Resolution.

(** * [less_defined] *)
Class LessDefined a := less_defined : a -> a -> Prop.
Infix "`less_defined`" := less_defined (at level 42).

Inductive LessDefined_T {a : Type} `{LessDefined a} : LessDefined (T a) :=
| LessDefined_Undefined x : Undefined `less_defined` x
| LessDefined_Thunk x y :
    x `less_defined` y -> Thunk x `less_defined` Thunk y.

#[global] Hint Constructors LessDefined_T : core.
#[global] Existing Instance LessDefined_T.

Unset Typeclasses Strict Resolution.

(** This corresponds to the propositions [less_defined_order] and [exact_max] in Section 5.3.
  We actually need only a preorder (TODO: do we?), and the imprecision of
  "order" in the paper is an oversight.
 *)
Class ApproximationAlgebra a b {Hless : LessDefined a} (Hexact : Exact b a) :=
  { PreOrder_less_defined :> PreOrder (less_defined (a := a))
  ; exact_max : forall (xA : a) (x : b), exact x `less_defined` xA -> exact x = xA }.

Arguments ApproximationAlgebra : clear implicits.
Arguments ApproximationAlgebra a b {Hless Hexact}.

Set Typeclasses Strict Resolution.

#[global]
Instance PreOrder_LessDefined_T {a : Type} `{LessDefined a} `{Ho : !PreOrder (less_defined (a := a))}
  : PreOrder (less_defined (a := T a)).
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
Instance PartialOrder_LessDefined_T {a : Type} `{LessDefined a}
    `{Ho : PartialOrder _ eq (less_defined (a := a))}
  : PartialOrder eq (less_defined (a := T a)).
Proof.
constructor.
- intros ->. autounfold. constructor; reflexivity.
- inversion 1. induction H1.
  + inversion H2; reflexivity.
  + inversion H2; subst. f_equal. apply Ho. constructor; assumption.
Qed.

Lemma exact_max_T {a b} `{AA : ApproximationAlgebra a b}
  : forall (xA : T a) (x : b), exact x `less_defined` xA -> exact x = xA.
Proof.
  intros xA x H. inversion H; subst.
  unfold exact, Exact_T. f_equal. apply exact_max. assumption.
Qed.

#[global]
Instance ApproximationAlgebra_T {a b} `{AA : ApproximationAlgebra a b} : ApproximationAlgebra (T a) b.
Proof.
  constructor.
  - apply @PreOrder_LessDefined_T, AA.
  - apply @exact_max_T, AA.
Qed.

(** * [is_approx]
    
    In our paper, the definition of [is_approx] can be anything as long as it
    satisfies the [approx_exact] proposition. In this file, we choose the most
    direct definition that satisfies the [approx_exact] law. *)
Notation is_approx xA x := (xA `less_defined` exact x) (only parsing).
Infix "`is_approx`" := is_approx (at level 42, only parsing).

Create HintDb exact.

(** * This corresponds to the proposition [approx_exact] in Section 5.3.

    And because of our particular definition, this is true by
    definition. However, this cannot be proved generically if the definition of
    [is_approx] can be anything. *)
Theorem approx_exact {a b} `{Exact b a} `{LessDefined a} :
  forall (x : b) (xA : a),
    xA `is_approx` x <-> xA `less_defined` (exact x).
Proof. reflexivity. Qed.

(** * This corresponds to the proposition [approx_down] in Section 5.3.

    Again, because of the particular definition of [is_approx] we use here, this
    can be proved simply by the law of transitivity. *)
Lemma approx_down {a b} `{Hld : LessDefined a} `{Exact b a} `{PartialOrder _ eq (less_defined (a := a))}:
  forall (x : b) (xA yA : a),
    xA `less_defined` yA -> yA `is_approx` x -> xA `is_approx` x.
Proof.
  intros. etransitivity; eassumption.
Qed.

(**)

(* Ordered types with a least element. It represents an empty demand.
   It's also convenient as a dummy value in nonsensical cases. *)
Class Bottom (a : Type) : Type :=
  bottom : a.

#[global] Instance Bottom_T {a} : Bottom (T a) := Undefined.
#[global] Instance Bottom_prod {a b} `{Bottom a, Bottom b} : Bottom (a * b) := (bottom, bottom).

Class BottomLeast a `{LessDefined a,Bottom a} : Prop :=
  bottom_least : forall x : a, bottom `less_defined` x.

#[global] Instance BottomLeast_t {a} `{LessDefined a} : BottomLeast (T a).
Proof. constructor. Qed.

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

#[global] Instance LessDefined_prod {a b} `{LessDefined a, LessDefined b} : LessDefined (a * b) :=
  pair_rel less_defined less_defined.

Lemma PreOrder_pair_rel {a b ra rb} `{!@PreOrder a ra,!@PreOrder b rb} : PreOrder (pair_rel ra rb).
Proof.
  constructor; constructor; reflexivity + etransitivity; eapply fst_rel + eapply snd_rel; eassumption.
Qed.

#[global] Instance ApproximationAlgebra_prod {a aA b bA} `{ApproximationAlgebra a aA, ApproximationAlgebra b bA}
  : ApproximationAlgebra (a * b) (aA * bA).
Proof.
  constructor.
  - apply PreOrder_pair_rel.
  - intros [] [] [HH1 HH2]; cbn in *. apply exact_max in HH1, HH2.
    unfold exact, Exact_prod; cbn. congruence.
Qed.

#[global] Instance Lub_prod {a b} `{Lub a, Lub b} : Lub (a * b) :=
  fun x y => (lub (fst x) (fst y), lub (snd x) (snd y)).

#[global] Instance LubLaw_prod {a b} `{LubLaw a, LubLaw b} : LubLaw (a * b).
Proof.
Admitted.

#[global] Instance Exact_option {a aA} `{Exact a aA} : Exact (option a) (option aA) := fun ox =>
  match ox with
  | None => None
  | Some x => Some (exact x)
  end.

#[global] Instance LessDefined_option {a} `{LessDefined a} : LessDefined (option a) :=
  option_rel less_defined.

#[global] Instance PreOrder_option {a} `{LessDefined a} `{!PreOrder (less_defined (a := a))}
  : PreOrder (less_defined (a := option a)).
Proof.
  econstructor.
Admitted.

#[global] Instance PartialOrder_option {a} `{LessDefined a} `{PartialOrder _ eq (equ := _) (less_defined (a := a))}
  : PartialOrder eq (less_defined (a := option a)).
Proof.
Admitted.

#[global] Instance ApproximationAlgebra_option {a aA} `{ApproximationAlgebra aA a}
  : ApproximationAlgebra (option aA) (option a).
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

#[local] Instance ApproximationAlgebra_id {a} : ApproximationAlgebra a a.
Proof.
  econstructor.
  - typeclasses eauto.
  - cbv; easy.
Qed.

#[local] Instance Lub_id {a} : Lub a := fun n _ => n.
#[local] Instance LubLaw_id {a} : LubLaw a.
Proof.
  constructor;cbv;firstorder (subst; auto).
Qed.

#[global] Hint Unfold Exact_id : core.
#[global] Hint Unfold LessDefined_id : core.

#[global] Instance Exact_nat : Exact nat nat := id.
#[global] Instance LessDefined_nat : LessDefined nat := eq.
#[global] Instance ApproximationAlgebra_nat : ApproximationAlgebra nat nat := ApproximationAlgebra_id.
#[global] Instance Lub_nat : Lub nat := fun n _ => n.
#[global] Instance LubLaw_nat : LubLaw nat := LubLaw_id.

#[global] Instance Exact_unit : Exact unit unit := id.
#[global] Instance LessDefined_unit : LessDefined unit := eq.
#[global] Instance ApproximationAlgebra_unit : ApproximationAlgebra unit unit := ApproximationAlgebra_id.
#[global] Instance Lub_unit : Lub unit := fun n _ => n.
#[global] Instance LubLaw_unit : LubLaw unit := LubLaw_id.

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

Ltac solve_approx :=
  repeat (match goal with
          | _ => solve [eauto]
          | [ |- _ `less_defined` _ ] => progress (autorewrite with exact) + (constructor; cbn)
          | [ |- is_defined (Thunk _) ] =>
            reflexivity
          end).

(** Heuristics for reasoning about pessimistic/optimistic specs. *)
Ltac mgo tac := repeat (intros;
                        repeat invert_eq; repeat invert_approx;
                        cbn in *; (mforward tac + solve_approx + lia)).
Ltac mgo' := mgo idtac.
