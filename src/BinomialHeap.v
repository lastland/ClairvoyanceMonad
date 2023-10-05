(* Overview

-- Pure implementation of binomial heaps: [Tree], [Heap], [link], [rank],
    [root], [insTree], [insert], [merge], [removeMinTree], [findMin], [deleteMin]
-- Clairvoyant-monadic implementation: [TreeA], [HeapA], [linkA], [rankA],
    [rootA], [insTreeA], [insertA], [mergeA], [removeMinTreeA], [findMinA], [deleteMinA]

NEW
- Demand functions:
- (Physicist's method) Debt/negative potential: [debt]
- Amortized cost specifications:
- "API traces" with sharing:
- Final theorem (statement and proof):
    the cost of executing a trace with [n] operations is ?

*)

From Equations Require Import Equations.

From Coq Require Import Arith List Lia Setoid Morphisms Orders Program.
Import ListNotations.
From Clairvoyance Require Import Core Approx ApproxM List ListA Misc Tick Demand.

Import Tick.Notations.
#[local] Open Scope tick_scope.

Set Implicit Arguments.

(* I have had some problems with inversion_clear. This does the same thing, but
   hopefully better. Note that it might not work as expected if the inverted
   hypothesis "contains" equalities. *)
Tactic Notation "invert_clear" hyp(H) "as" simple_intropattern(pat) :=
  (* Rename the original hypothesis so that its name can be reused if
     desired. *)
  let H' := fresh "H'" in
  rename H into H';
  (* Mark our place in the context with a trivial hypothesis. *)
  let HI := fresh "HI" in
  pose I as HI;
  (* Perform the inversion, possibly adding some equalities to the bottom of the
     context. *)
  inversion H' as pat;
  (* Substitute equalities from the bottom up, stopping when we reach a
     non-equality hypothesis. *)
  repeat lazymatch goal with
    | _ : ?type |- _ => match type with
                        | ?x = ?y => subst x + subst y
                        end
    end;
  (* Clear the marker and the original hypothesis. *)
  clear HI;
  clear H'.

Tactic Notation "invert_clear" hyp(H) :=
  invert_clear H as [ ].

Tactic Notation "invert_clear" integer(n) "as" simple_intropattern(pat) :=
  progress (intros until n);
  match goal with
  | H : _ |- _ => invert_clear H as pat
  end.

(* For some reason, trying to chain this into the above notation causes
   problems. *)
Tactic Notation "invert_clear" integer(n) :=
  progress (intros until n);
  match goal with
  | H : _ |- _ => invert_clear H as [ ]
  end.

(* Tactic to invert/subst/clear a single hypothesis of the form

   P x1 x2 ... (C y1 y2 ... ym) ... xn

   where C is a constructor. This is a common way to make progress. *)
Ltac invert_constructor :=
  let rec head_is_constructor t := match t with
                                   | ?f ?x => head_is_constructor f
                                   | _ => is_constructor t
                                   end in
  let rec should_invert T := match T with
                             | ?P ?x => head_is_constructor x + should_invert P
                             end in
  intros;
  match goal with
  | H : ?T |- _ => should_invert T; invert_clear H
  end.

(* Lift a predicate to T. *)
Inductive LiftT A (P : A -> Prop) : T A -> Prop :=
| LiftT_Undefined : LiftT P Undefined
| LiftT_Thunk x : P x -> LiftT P (Thunk x).
#[global] Hint Constructors LiftT : core.

Lemma listA_ind_alt A (P : listA A -> Prop) :
  P NilA ->
  (forall xD xsD, LiftT P xsD -> P (ConsA xD xsD)) ->
  forall xs, P xs.
Proof.
  induction xs; auto.
Qed.

Lemma LiftT_impl A (P Q : A -> Prop) :
  (forall x, P x -> Q x) -> forall x, LiftT P x -> LiftT Q x.
Proof.
  intros until x. destruct 1; auto.
Qed.
#[global] Hint Resolve LiftT_impl : core.

(* Lift a binary relation to T in a way that preserves the less-defined
   relation. *)
Inductive LiftT2 A B (R : A -> B -> Prop) : T A -> T B -> Prop :=
| LiftT2_Undefined yD : LiftT2 R Undefined yD
| LiftT2_Thunk x y : R x y -> LiftT2 R (Thunk x) (Thunk y).
#[global] Hint Constructors LiftT2 : core.

Lemma LiftT2_impl A B (R1 R2 : A -> B -> Prop) :
  (forall x y, R1 x y -> R2 x y) -> forall xD yD, LiftT2 R1 xD yD -> LiftT2 R2 xD yD.
Proof.
  intros until yD. destruct 1; auto.
Qed.
#[global] Hint Resolve LiftT2_impl : core.

Lemma LiftT2_refl A (R : A -> A -> Prop) :
  (forall x, R x x) -> forall xD, LiftT2 R xD xD.
Proof.
  destruct xD; auto.
Qed.
#[global] Hint Resolve LiftT2_refl : core.

Lemma LiftT2_trans A (R : A -> A -> Prop) :
  (forall x y z, R x y -> R y z -> R x z) ->
  forall xD yD zD, LiftT2 R xD yD -> LiftT2 R yD zD -> LiftT2 R xD zD.
Proof.
  inversion 2; inversion 1; eauto.
Qed.
#[global] Hint Resolve LiftT2_trans : core.

Lemma LiftT_LiftT2_diag A (R : A -> A -> Prop) xD :
  LiftT (fun x => R x x) xD <-> LiftT2 R xD xD.
Proof.
  split; inversion 1; auto.
Qed.
#[global] Hint Resolve -> LiftT_LiftT2_diag : core.
#[global] Hint Resolve <- LiftT_LiftT2_diag : core.

Lemma LiftT2_less_defined A `(LessDefined A) (R : A -> A -> Prop) (x y : T A) :
  LiftT2 less_defined x y <-> x `less_defined` y.
Proof.
  split; inversion 1; auto.
Qed.
#[global] Hint Resolve -> LiftT2_less_defined : core.
#[global] Hint Resolve <- LiftT2_less_defined : core.

Ltac invert_LiftT :=
  match goal with
  | H : LiftT _ _ |- _ => invert_clear H
  | H : LiftT2 _ _ _ |- _ => invert_clear H
  end.

(* Lift a predicate to listA. *)
Inductive ForallA A (P : A -> Prop) : listA A -> Prop :=
| ForallA_NilA : ForallA P NilA
| ForallA_ConsA x xs : LiftT P x -> LiftT (ForallA P) xs -> ForallA P (ConsA x xs).
#[global] Hint Constructors ForallA : core.

Lemma ForallA_impl A (P Q : A -> Prop) :
  (forall x, P x -> Q x) -> forall xs, ForallA P xs -> ForallA Q xs.
Proof.
  induction xs; repeat invert_constructor; eauto.
Qed.
#[global] Hint Resolve ForallA_impl : core.

(* Lift a binary relation to listA in a way that preserves the less-defined
   relation. *)
Inductive ForallA2 A B (R : A -> B -> Prop) : listA A -> listA B -> Prop :=
| ForallA2_NilA : ForallA2 R NilA NilA
| ForallA2_ConsA x y xs ys : LiftT2 R x y -> LiftT2 (ForallA2 R) xs ys -> ForallA2 R (ConsA x xs) (ConsA y ys).
#[global] Hint Constructors ForallA2 : core.

Lemma ForallA2_impl A B (R1 R2 : A -> B -> Prop) :
  (forall x y, R1 x y -> R2 x y) -> forall xs ys, ForallA2 R1 xs ys -> ForallA2 R2 xs ys.
Proof.
  induction xs; repeat invert_constructor; eauto.
Qed.
#[global] Hint Resolve ForallA2_impl : core.

Lemma ForallA2_refl A (R : A -> A -> Prop) :
  (forall x, R x x) -> forall xs, ForallA2 R xs xs.
Proof.
  induction xs; auto.
Qed.
#[global] Hint Resolve ForallA2_refl : core.

Lemma ForallA2_trans A (R : A -> A -> Prop) :
  (forall x y z, R x y -> R y z -> R x z) ->
  forall xs ys zs, ForallA2 R xs ys -> ForallA2 R ys zs -> ForallA2 R xs zs.
Proof.
  intros ? xs ys zs Hxsys Hyszs. revert xs zs Hxsys Hyszs.
  induction ys; repeat invert_constructor; eauto.
Qed.
#[global] Hint Resolve ForallA2_trans : core.

Lemma ForallA_ForallA2_diag A (R : A -> A -> Prop) xs :
  ForallA (fun x => R x x) xs <-> ForallA2 R xs xs.
Proof.
  split; induction xs; repeat invert_constructor; auto.
Qed.
#[global] Hint Resolve -> ForallA_ForallA2_diag : core.
#[global] Hint Resolve <- ForallA_ForallA2_diag : core.

Lemma ForallA2_less_defined A `{LessDefined A} (xs ys : listA A) : ForallA2 less_defined xs ys <-> xs `less_defined` ys.
Proof.
  split.
  - revert ys. induction xs; repeat invert_constructor; auto.
  - induction 1; auto.
Qed.
#[global] Hint Resolve -> ForallA2_less_defined : core.
#[global] Hint Resolve <- ForallA2_less_defined : core.

Notation A := nat (only parsing).

Unset Elimination Schemes.

Inductive Tree : Type :=
| Node : forall (n : nat) (x : A) (ts : list Tree), Tree.

Lemma Tree_ind (P : Tree -> Prop) :
    (forall (n : nat) (x : A) (ts : list Tree), Forall P ts -> P (Node n x ts)) ->
    forall (t : Tree), P t.
Proof.
  intros H. fix SELF 1.
  destruct t. apply H. induction ts; auto.
Qed.

Inductive TreeA : Type :=
| NodeA : forall (nD : T nat) (xD : T A) (tsD : T (listA TreeA)), TreeA.

Lemma TreeA_ind : forall (P : TreeA -> Prop),
    (forall (nD : T nat) (xD : T A) (tsD : T (listA TreeA)), LiftT (ForallA P) tsD -> P (NodeA nD xD tsD)) ->
    forall (tD : TreeA), P tD.
Proof.
  intros ? H. fix SELF 1.
  destruct tD. apply H. destruct tsD as [ ts | ].
  1: induction ts as [ | tD | tD ]. 2, 3: destruct tD.
  all: repeat constructor; try invert_constructor; auto.
Qed.

Inductive LessDefined_TreeA : LessDefined TreeA :=
| less_defined_TreeA_NodeA n1D n2D x1D x2D ts1D ts2D :
  n1D `less_defined` n2D ->
  x1D `less_defined` x2D ->
  (* Need to pass instance explicitly, because LessDefined_TreeA is not yet
     registered. *)
  @less_defined _ (@LessDefined_T _ (@LessDefined_list _ LessDefined_TreeA)) ts1D ts2D ->
  LessDefined_TreeA (NodeA n1D x1D ts1D) (NodeA n2D x2D ts2D).
#[global] Existing Instance LessDefined_TreeA.
#[global] Hint Constructors LessDefined_T : core.

Lemma LessDefined_TreeA_ind :
  forall (P : TreeA -> TreeA -> Prop),
    (forall (n1D n2D : T nat) (x1D x2D : T nat) (ts1D ts2D : T (listA TreeA)),
        n1D `less_defined` n2D ->
        x1D `less_defined` x2D ->
        LiftT2 (ForallA2 P) ts1D ts2D ->
        P (NodeA n1D x1D ts1D) (NodeA n2D x2D ts2D)) ->
    forall (t1 t2 : TreeA), LessDefined_TreeA t1 t2 -> P t1 t2.
Proof.
  intros P H. fix SELF 3.
  intros t1 t2 Hts. destruct Hts as [ n1D n2D x1D x2D ts1D ts2D HnD HxD HtsD ].
  apply H. 1, 2: assumption.
  invert_clear HtsD as [ | ts1 ts2 Hts12 ]; constructor.
  induction Hts12 as [ | t1D t2D ? HtD12 | t1D t2D ? ? HtD12 ].
  1: auto.
  1, 2: inversion HtD12; auto.
Qed.

Set Elimination Schemes.

Lemma LessDefined_TreeA_refl (t : TreeA) :
  t `less_defined` t.
Proof.
  pose (Reflexive_LessDefined_T (a := nat)).
  unfold Reflexive. induction t. constructor.
  3: invert_LiftT.
  all: auto.
Qed.
#[global] Hint Resolve LessDefined_TreeA_refl : core.

#[global] Instance LessDefined_TreeA_reflexive : Reflexive LessDefined_TreeA :=
  LessDefined_TreeA_refl.

Lemma LessDefined_TreeA_trans (t1 t2 t3 : TreeA) :
  t1 `less_defined` t2 -> t2 `less_defined` t3 -> t1 `less_defined` t3.
Proof.
  pose (Transitive_LessDefined_T (a := nat)) as HTransitive_LessDefined_T.
  intros Ht12 Ht23. revert t2 t3 Ht12 Ht23. induction t1 as [ n1D x1D ts1D HtsD1 ]. intros.
  invert_clear Ht12 as [ ? n2D ? x2D ? ts2D HnD12 HxD12 HtsD12 ].
  invert_clear Ht23 as [ ? nD3 ? xD3 ? ts3D HnD23 HxD23 HtsD23 ].
  constructor. 1, 2: eauto.
  invert_clear HtsD1 as [ | ts1 ]. 1: auto.
  invert_clear HtsD12 as [ | ? ts2 Hts12 ].
  invert_clear HtsD23 as [ | ? ts3 Hts23 ].
  constructor.
  revert ts2 ts3 Hts12 Hts23. induction ts1;
    repeat (invert_constructor + invert_LiftT); repeat constructor;
    try (match goal with | H : _ |- _ => eapply H end);
    eauto.
  Qed.
#[global] Hint Resolve LessDefined_TreeA_trans : core.

#[global] Instance LessDefined_TreeA_transitive : Transitive LessDefined_TreeA :=
  LessDefined_TreeA_trans.

Add Relation TreeA LessDefined_TreeA
    reflexivity proved by LessDefined_TreeA_reflexive
    transitivity proved by LessDefined_TreeA_transitive
    as LessDefined_TreeA_Relation.
Print TreeA.
(* Exact_list depends on an Exact instance for the element type, but the
   element type here is Tree. We can't hand out Exact_Tree while it's being
   constructed, because that won't pass the termination checker. So we have to
   roll our own Exact_list here. *)
#[global] Instance Exact_Tree : Exact Tree TreeA := fix Exact_Tree t :=
  let fix Exact_trees (ts : list Tree) : listA TreeA :=
    match ts with
    | [] => NilA
    | t :: ts' => ConsA (Thunk (Exact_Tree t)) (Thunk (Exact_trees ts'))
    end in
  match t with
  | Node n x ts => NodeA (exact n) (exact x) (Thunk (Exact_trees ts))
  end.

(* However, once we have defined Exact_Tree, we can show that it behaves the
   same as if it had been defined using Exact_list. (Of course, this depends
   recursively on the definition of Exact_Tree. There's no way around that.) *)
Lemma Exact_Tree_Exact_list (t : Tree) :
  exact t = match t with
            | Node n x ts => NodeA (exact n) (exact x) (exact ts)
            end.
Proof.
  induction t as [ ? ? ? IH ]. induction IH as [ | ? ? ? ? IHIH ].
  - reflexivity.
  - cbv. simp exact_listA. repeat f_equal.
    cbv in IHIH. injection IHIH. trivial.
Qed.
#[global] Hint Resolve Exact_Tree_Exact_list : core.

Definition link (t1 t2 : Tree) : Tree :=
  match t1, t2 with
  | Node r1 v1 c1, Node r2 v2 c2 => if leb v1 v2
                                    then Node (r1 + 1) v1 (t2 :: c1)
                                    else Node (r2 + 1) v2 (t1 :: c2)
  end.

Definition linkD (t1 t2 : Tree) (d : TreeA) : Tick (T TreeA * T TreeA) :=
  match t1, t2 with
  | Node r1 v1 c1, Node r2 v2 c2 =>
      if leb v1 v2 then
        match d with
        | NodeA rD v1D tsD =>
            let '(t2D, c1D) := TConsD tsD in
            Tick.ret (Thunk (NodeA (exact r1) v1D c1D), t2D)
        end
      else
        match d with
        | NodeA rD v2D tsD =>
            let '(t1D, c2D) := TConsD tsD in
            Tick.ret (t1D, Thunk (NodeA (exact r2) v2D c2D))
        end
  end.

Lemma linkD_approx (t1 t2 : Tree) (outD : TreeA) :
  outD `is_approx` link t1 t2 -> Tick.val (linkD t1 t2 outD) `is_approx` (t1, t2).
Proof.
  destruct t1 as [ n1 x1 ts1 ], t2 as [ n2 x2 ts2 ]. simpl.
  destruct (x1 <=? x2); cbn; repeat invert_constructor; repeat constructor; auto.
Qed.
#[global] Hint Resolve linkD_approx : core.

Definition ConsD {A} (xs : listA A) : T A * T (listA A) :=
  match xs with
  | ConsA x ys => (x, ys)
  | _ => (Undefined, Undefined) (* should not happen *)
  end.

Definition rank (t : Tree) : nat :=
  match t with
  | (Node r v c) => r
  end.

Definition root (t : Tree) : A :=
  match t with
  | (Node r v c) => v
  end.

(*Assumes t has rank <= the rank of the first element of ts (if any).*)
Fixpoint insTree (t : Tree) (ts : list Tree) : list Tree :=
  match ts with
  | [] => [t]
  | t' :: ts' => if rank t <? rank t'
                 then t :: ts
                 else insTree (link t t') ts' (*t and t' should have the same rank*)
  end.

Lemma insTree_is_cons (t : Tree) (ts : list Tree) : exists t' ts', insTree t ts = t' :: ts'.
Proof.
  revert t. induction ts; intro; simpl.
  2: destruct (rank t <? rank a).
  all: eauto.
Qed.
#[global] Hint Resolve insTree_is_cons : core.

#[global] Instance Lub_TreeA : Lub TreeA :=
  fix Lub_TreeA t1 t2 :=
    let fix lub_list_TreeA (ts1 ts2 : listA TreeA) :=
      match ts1, ts2 with
      | NilA, NilA => NilA
      | ConsA t1 ts1, ConsA t2 ts2 => ConsA (lub_T Lub_TreeA t1 t2) (lub_T lub_list_TreeA ts1 ts2)
      | _, _ => NilA
      end in
    match t1, t2 with
    | NodeA n1 x1 ts1, NodeA n2 x2 ts2 => NodeA (lub n1 n2) (lub x1 x2) (lub_T lub_list_TreeA ts1 ts2)
    end.

Lemma cobounded_sym A `(LessDefined A) (x y : A) :
  cobounded x y -> cobounded y x.
Proof.
  firstorder.
Qed.
#[global] Hint Resolve cobounded_sym : core.

Lemma Lub_nat_comm (n1 n2 : nat) :
  cobounded n1 n2 -> lub n1 n2 = lub n2 n1.
Proof.
  intros [ n3 [ Hn13 Hn23 ] ]. inversion Hn13. auto.
Qed.
#[global] Hint Resolve Lub_nat_comm : core.

Lemma lub_T_comm A `(LessDefined A) `(Lub A) :
  (forall (x y : A), cobounded x y -> lub x y = lub y x) ->
  forall (xD yD : T A), cobounded xD yD -> lub xD yD = lub yD xD.
Proof.
  intros Hcomm ? ? [ zD [ Hxz Hyz ] ].
  invert_clear Hxz; invert_clear Hyz. 1, 2, 3: auto.
  unfold lub. simpl. f_equal. eauto.
Qed.
#[global] Hint Resolve lub_T_comm : core.

Lemma Lub_TreeA_comm (t1 t2 : TreeA) :
  cobounded t1 t2 -> lub t1 t2 = lub t2 t1.
Proof.
  pose Lub_nat_comm as HLub_nat_comm.
  revert t2. induction t1 as [ n1D x1D ts1D Hts1D ]. intros t2 [ t3 [ Ht13 Ht23 ] ].
  invert_clear Ht13 as [ ? n3D ? x3D ? ts3D HnD13 HxD13 HtsD13 ].
  invert_clear Ht23 as [ n2D ? x2D ? ts2D ? HnD23 HxD23 HtsD23 ].
  invert_clear Hts1D as [ | ts1 Hts1 ].
  1: { unfold lub. simpl. f_equal. 3: invert_clear HtsD23. all: eauto. }.
  invert_clear HtsD13 as [ | ? ts3 Hts13 ].
  invert_clear HtsD23 as [ | ts2 ? Hts23 ]; unfold lub; simpl; f_equal. 1, 2, 3, 4: eauto.
  f_equal.
  revert ts2 ts3 Hts13 Hts23.
  induction ts1 as [ | t1D ts1D IH ] using listA_ind_alt; intros. 1: invert_clear Hts23; auto.
  invert_clear Hts1 as [ | ? ? Ht1D Hts1D ].
  invert_clear Hts13 as [ | ? t3D ? ts3D Ht13D Hts13D ].
  invert_clear Hts23 as [ | t2D ? ts2D ? Ht23D Hts23D ].
  f_equal.
  - invert_clear Ht1D as [ | t1 Ht1 ];
      invert_clear Ht23D as [ | t2 t3 Ht23 ]. 1, 2, 3: auto.
    simpl. f_equal. apply Ht1. invert_clear Ht13D. eauto.
  - invert_clear Hts1D as [ | ts1 Hts1 ];
      invert_clear Hts23D as [ | ts2 ts3 Hts23 ]. 1, 2, 3: auto.
    simpl. f_equal. invert_clear IH. invert_clear Hts13D. eapply H; eauto.
Qed.
#[global] Hint Resolve Lub_TreeA_comm : core.

#[global] Instance LubLaw_TreeA : LubLaw TreeA.
Proof.
  assert (forall x y : TreeA, cobounded x y -> x `less_defined` lub x y).
  1: {
    intros t1 t2 Ht12. revert t2 Ht12.
    induction t1 as [ n1D x1D ts1D IHts1D ]. destruct 1 as [ t3 [ Ht13 Ht23 ] ].
    invert_clear Ht13 as [ ? n3D ? x3D ? ts3D Hn13D Hx13D Hts13D ].
    invert_clear Ht23 as [ n2D ? x2D ? ts2D ? Hn23D Hx23D Hts23D ].
    constructor. 1, 2: apply lub_upper_bound_l; eauto.
    invert_clear Hts13D as [ | ts1 ts3 Hts13 ]. 1: auto.
    invert_clear Hts23D as [ | ts2 ? Hts23 ]. 1: simpl; auto.
    invert_clear IHts1D as [ | ? IHts1 ].
    revert ts2 ts3 Hts13 Hts23.
    induction ts1 as [ | t1D ts1D IH ] using listA_ind_alt; intros.
    1: invert_clear Hts23; simpl; auto.
    constructor.
    invert_clear Hts23 as [ | t2D t3D ts2D ts3D Ht23D Hts23D ]. 1: auto.
    invert_clear IHts1 as [ | ? ? Ht1D Hts1D ].
    constructor.
    - invert_clear Ht1D as [ | t1 Ht1 ]. 1: auto.
      invert_clear Ht23D. simpl; auto.
      constructor. apply Ht1. invert_clear Hts13 as [ | ? ? ? ? Ht13 Hts13D ].
      invert_clear Ht13. eauto.
    - invert_clear Hts1D as [ | ts1 Hts1 ]. 1: auto.
      invert_clear Hts23D. 1: simpl; auto.
      invert_clear IH as [ | ? IH ]. repeat invert_constructor. eapply IH; eauto.
  }.
  constructor.
  - intros t1 t2 t3 Ht13 Ht23. revert t2 t3 Ht13 Ht23.
    induction t1 as [ n1D x1D ts1D IHts1D ]. intros.
    invert_clear Ht13 as [ ? n3D ? x3D ? ts3D Hn13D Hx13D Hts13D ].
    invert_clear Ht23 as [ n2D ? x2D ? ts2D ? Hn23D Hx23D Hts23D ].
    constructor. 1, 2: apply lub_least_upper_bound; auto.
    invert_clear Hts13D as [ | ts1 ts3 Hts13 ]. 1: auto.
    invert_clear Hts23D as [ | ts2 ? Hts23 ]. 1: simpl; auto.
    constructor.
    revert ts2 ts3 Hts13 Hts23.
    induction ts1 as [ | t1D ts1D IH ] using listA_ind_alt; intros;
      invert_clear Hts23 as [ | t2D t3D ts2D ts3D Ht23D Hts23D ]. 1, 2, 3: auto.
    invert_clear IH; repeat (invert_constructor + invert_LiftT); simpl; auto.
  - assumption.
  - intros. rewrite Lub_TreeA_comm; auto.
Qed.


    (* intros. invert_clear Ht12. invert_clear Ht23. *)
    (* constructor; try (apply lub_least_upper_bound); auto. *)
    (* invert_clear H. 1: auto. *)
    (* destruct ts1D. 2: auto. *)
    (* repeat invert_constructor. constructor. *)
    (* induction x. *)
    (* + invert_clear H; auto. *)
    (* + invert_clear H. 1: auto. *)
    (*   repeat invert_constructor. invert_clear H5. *)
    (*   * repeat invert_constructor. auto. *)
    (*   * repeat invert_constructor. repeat constructor; repeat constructor. 1, 2: auto. *)
    (*     repeat constructor; eauto. *)
    (* + destruct x0. 1: auto. *)
    (*   repeat invert_constructor. *)

(* repeat invert_constructor. *)
(*       * repeat constructor. 2: auto. *)
(*         invert_clear H. 1: auto. *)
(*         repeat invert_constructor; repeat constructor; auto. *)
(*       * constructor. *)
(*         -- admit. *)
(*         -- repeat constructor. invert_clear H8; repeat invert_constructor. *)
(*            ++  *)




Definition strictD (t : Tree) (x' : T TreeA) : T TreeA := lub x' (Thunk (NodeA (exact (rank t)) Undefined Undefined)).

Definition strictConsD {A} (xs' : T (listA A)) : T (listA A) := lub xs' (Thunk (ConsA Undefined Undefined)).

(* [d] is an approximation of the output [insTree t ts] *)
Fixpoint insTreeD (t : Tree) (ts : list Tree) (d : listA TreeA) : Tick (T TreeA * T (listA TreeA)) :=
  match ts with
  | [] =>
    (* [d] is an approximation of [t :: nil] *)
    (* ConsD inverts it and returns approximations of [t] and [nil] (which is ignored) *)
    let '(tD, _) := ConsD d in
    (* To find out what to return, we enumerate all of the uses of the arguments of [insTree]: *)
(*        - [t] was only used in the output list, corresponding to the demand [tD] *)
(*        - [ts] was used in [match], so its demand must at least be [Thunk NilA], which is fully defined. *)
(*     *)
    Tick.ret (tD, Thunk NilA)
  | t' :: ts' => if rank t <? rank t'
    then (* [d] is an approximation of [t :: ts] *)
         let '(tD, tsD) := ConsD d in
         (* [t] occurs in the result [t :: ts] (with demand [tD]), and also to compare its rank, *)
(*             so we use [strictD] to give its demand a defined rank. *)
(*             [ts] was also pattern-matched on, so we similarly require an annotation *)
(*             to make its demand not [Undefined]. *)
         Tick.ret (strictD t tD, strictConsD tsD)
    else (* The result of [insTree] is a recursive call. So we recursively compute the *)
(*             demand on its arguments: [lD] is the demand on [link t t'], and [ts'D] is the demand *)
(*             on [ts]. *)
         let+ (lD, ts'D) := insTreeD (link t t') ts' d in
         (* [linkD] takes [lD] to compute a demand on [t] and [t']. *)

(*             Demand functions return results wrapped in [T] (so that [Undefined] *)
(*             may indicate an unused argument), but the input demand is not wrapped in [T] *)
(*             (since there is no point in calling this if the argument is unused). *)
(*             We use [thunkD] to apply a demand function on a demand wrapped in *)
(*             [T] (here [lD]), usually coming from a pattern or another function. *)
         let+ (tD, t'D) := thunkD (linkD t t') lD in
         Tick.ret (strictD t tD, Thunk (ConsA t'D ts'D))
  end.

(* #[global] Hint Constructors listA : core. *)
(* #[global] Hint Constructors LessDefined_list : core. *)
(* #[global] Hint Unfold LessDefined_prod : core. *)
(* #[global] Hint Constructors Relations.pair_rel : core. *)
(* #[global] Hint Constructors LessDefined_T : core. *)
(* #[global] Hint Unfold Exact_prod : core. *)
(* #[global] Hint Unfold Exact_T : core. *)

(* #[global] Hint Unfold exact : core. *)
#[global] Hint Unfold less_defined : core.
#[global] Hint Unfold LessDefined_prod : core.
#[global] Hint Unfold exact : core.

Lemma insTreeD_approx (t : Tree) (ts : list Tree) (outD : listA TreeA) :
  outD `is_approx` insTree t ts ->
  Tick.val (insTreeD t ts outD) `is_approx` (t, ts).
Proof.
  (* induction ts, outD;  unfold less_defined; simpl; try (destruct (rank t <? rank a)). constructor. auto. simpl. invert_constructors; repeat constructor; auto. *)
  (* - unfold strictD. simpl. *)
  (* - *)
  (* unfold exact, Exact_T. *)

  revert t. induction ts; intros t Hless_defined.
  - admit.
  - simpl in *. destruct (rank t <? rank a).
    + invert_clear Hless_defined.
      * constructor. simpl. autounfold in *. simpl in *. simpl.
(* destruct x1; unfold lub, exact, Exact_T, exact; simpl; unfold constructor. *)
    + apply IHts in Hless_defined



(* linkD_approx : outD `is_approx` link t1 t2 -> Tick.val (linkD t1 t2 outD) `is_approx` (t1, t2). *)
    + repeat constructor.
    +
intros. repeat constructor. repeat invert_constructor; repeat (unfold exact in *; unfold less_defined in *); auto.

  (* induction ts, outD. *)
  (* - split; constructor; auto. *)
  (* - inversion 1. repeat constructor; auto. *)
  (* (* Impossible case. *) *)
  (* - destruct (insTree_is_cons t (a :: ts)) as [ w [ x y ] ]. rewrite y. inversion 1. *)
  (* - inversion 1. simpl. destruct (rank t <? rank a). *)
  (*   + inversion H2. subst. split. unfold strictD. simpl. destruct x1. *)
  (*     * constructor. inversion_clear H3. *)
Admitted.

(* Inductive TreeA : Type := *)
(*   | NodeA : T nat -> T A -> T (listA TreeA) -> TreeA. *)

(* Canonical AA_Tree := *)
(*   {| carrier := Tree *)
(*   ;  approx := TreeA *)
(*   ;  AA_Setoid := TODO *)
(*   ;  AA_IsAA := TODO *)
(*   ;  AA_IsAS := TODO *)
(*   |}. *)

(* Record Heap : Type := MkHeap *)
(*   { trees : list Tree }. *)

(* Record HeapA : Type := MkHeapA *)
(*   { treesA : T (listA TreeA) }. *)

(* Canonical AA_Heap : AA := *)
(*   {| carrier := Heap *)
(*   ;  approx := T HeapA *)
(*   ;  AA_Setoid := TODO *)
(*   ;  AA_IsAA := TODO *)
(*   ;  AA_IsAS := TODO *)
(*   |}. *)

(* Definition link (t1 t2 : Tree) : Tree := *)
(*   match t1, t2 with *)
(*   | Node r1 v1 c1, Node r2 v2 c2 => if leb v1 v2 *)
(*     then Node (r1 + 1) v1 (t2 :: c1) *)
(*     else Node (r2 + 1) v2 (t1 :: c2) *)
(*   end. *)

(* (* Encoding of Node *) *)
(* (* Currently unused, just pattern-match on it instead *) *)
(* Definition NodeD (t : TreeA) : Tick (T nat * T A * T (listA TreeA)) := *)
(*   Tick.ret *)
(*   match t with *)
(*   | NodeA n x ts => (n, x, ts) *)
(*   end. *)

(* Definition TNodeD (t : T TreeA) : Tick (T nat * T A * T (listA TreeA)) := *)
(*   Tick.ret *)
(*   match t with *)
(*   | Thunk (NodeA n x ts) => (n, x, ts) *)
(*   | Undefined => (Undefined, Undefined, Undefined) *)
(*   end. *)

(* Definition ConsD {A} (xs : listA A) : T A * T (listA A) := *)
(*   match xs with *)
(*   | ConsA x ys => (x, ys) *)
(*   | _ => (Undefined, Undefined) (* should not happen *) *)
(*   end. *)

(* Definition TConsD {A} (xs : T (listA A)) : T A * T (listA A) := *)
(*   match xs with *)
(*   | Thunk (ConsA x ys) => (x, ys) *)
(*   | Undefined | _ => (Undefined, Undefined) *)
(*   end. *)

(* Definition linkD (t1 t2 : Tree) (d : TreeA) : Tick (T TreeA * T TreeA) := *)
(*   match t1, t2 with *)
(*   | Node r1 v1 c1, Node r2 v2 c2 => *)
(*     if leb v1 v2 then *)
(*       match d with *)
(*       | NodeA rD v1D tsD => *)
(*         let '(t2D, c1D) := TConsD tsD in *)
(*         Tick.ret (Thunk (NodeA (exact r1) v1D c1D), t2D) *)
(*       end *)
(*     else *)
(*       match d with *)
(*       | NodeA rD v2D tsD => *)
(*         let '(t1D, c2D) := TConsD tsD in *)
(*         Tick.ret (t1D, Thunk (NodeA (exact r2) v2D c2D)) *)
(*       end *)
(*   end. *)

(* (* Currently unused, just pattern-match *) *)
(* Definition MkHeapD (d : HeapA) : Tick (T (listA TreeA)) := *)
(*   Tick.ret (treesA d). *)

(* Definition rank (t : Tree) : nat := *)
(*   match t with *)
(*   | (Node r v c) => r *)
(*   end. *)

(* Definition root (t : Tree) : A := *)
(*   match t with *)
(*   | (Node r v c) => v *)
(*   end. *)

(* (*Assumes t has rank <= the rank of the first element of ts (if any).*) *)
(* Fixpoint insTree (t : Tree) (ts : list Tree) : list Tree := *)
(*   match ts with *)
(*   | [] => [t] *)
(*   | t' :: ts' => if rank t <? rank t' *)
(*     then t :: ts *)
(*     else insTree (link t t') ts' (*t and t' should have the same rank*) *)
(*   end. *)

(* Definition strictD (t : Tree) (x' : T TreeA) : T TreeA := lub x' (Thunk (NodeA (exact (rank t)) Undefined Undefined)). *)
(* Definition strictConsD {A} (xs' : T (listA A)) : T (listA A) := lub xs' (Thunk (ConsA Undefined Undefined)). *)

(* (* [d] is an approximation of the output [insTree t ts] *) *)
(* Fixpoint insTreeD (t : Tree) (ts : list Tree) (d : listA TreeA) : Tick (T TreeA * T (listA TreeA)) := *)
(*   match ts with *)
(*   | [] => *)
(*     (* [d] is an approximation of [t :: nil] *) *)
(*     (* ConsD inverts it and returns approximations of [t] and [nil] (which is ignored) *) *)
(*     let '(tD, _) := ConsD d in *)
(*     (* To find out what to return, we enumerate all of the uses of the arguments of [insTree]: *)
(*        - [t] was only used in the output list, corresponding to the demand [tD] *)
(*        - [ts] was used in [match], so its demand must at least be [Thunk NilA], which is fully defined. *)
(*     *) *)
(*     Tick.ret (tD, Thunk NilA) *)
(*   | t' :: ts' => if rank t <? rank t' *)
(*     then (* [d] is an approximation of [t :: ts] *) *)
(*          let '(tD, tsD) := ConsD d in *)
(*          (* [t] occurs in the result [t :: ts] (with demand [tD]), and also to compare its rank, *)
(*             so we use [strictD] to give its demand a defined rank. *)
(*             [ts] was also pattern-matched on, so we similarly require an annotation *)
(*             to make its demand not [Undefined]. *) *)
(*          Tick.ret (strictD t tD, strictConsD tsD) *)
(*     else (* The result of [insTree] is a recursive call. So we recursively compute the *)
(*             demand on its arguments: [lD] is the demand on [link t t'], and [ts'D] is the demand *)
(*             on [ts]. *) *)
(*          let+ (lD, ts'D) := insTreeD (link t t') ts' d in *)
(*          (* [linkD] takes [lD] to compute a demand on [t] and [t']. *)

(*             Demand functions return results wrapped in [T] (so that [Undefined] *)
(*             may indicate an unused argument), but the input demand is not wrapped in [T] *)
(*             (since there is no point in calling this if the argument is unused). *)
(*             We use [thunkD] to apply a demand function on a demand wrapped in *)
(*             [T] (here [lD]), usually coming from a pattern or another function. *) *)
(*          let+ (tD, t'D) := thunkD (linkD t t') lD in *)
(*          Tick.ret (strictD t tD, Thunk (ConsA t'D ts'D)) *)
(*   end. *)

(* Definition insert (x : A) (hp : Heap) *)
(*   : Heap := *)
(*   MkHeap (insTree (Node 0 x []) (trees hp)). *)

(* Definition insertD (x : A) (hp : Heap) (d : HeapA) : Tick (T A * T HeapA) := *)
(*   let+ (tD, trees_hpD) := thunkD (insTreeD (Node 0 x []) (trees hp)) (treesA d) in *)
(*   let+ (_, xD, _) := TNodeD tD in *)
(*   Tick.ret (xD, Thunk (MkHeapA trees_hpD)). *)


(* Fixpoint mergeAux (trs1 trs2 : list Tree) : list Tree := *)
(*   match trs1 with *)
(*   | [] => trs2 *)
(*   | t1 :: trs1' => let fix merge_trs1 trsR := *)
(*     match trsR with *)
(*     | [] => trs1 *)
(*     | t2 :: trs2' => *)
(*       match Nat.compare (rank t1) (rank t2) with *)
(*       | Lt => t1 :: (mergeAux trs1' trsR) *)
(*       | Eq => insTree (link t1 t2) (mergeAux trs1' trs2') *)
(*       | Gt => t2 :: merge_trs1 trs2' *)
(*       end *)
(*     end in *)
(*     merge_trs1 trs2 *)
(*   end. *)

(* Definition merge (hp1 hp2 : Heap) : Heap := *)
(*   MkHeap (mergeAux (trees hp1) (trees hp2)). *)

(* Fixpoint mergeAuxD (trs1 trs2 : list Tree) (d : listA TreeA) : Tick (T (listA TreeA) * T (listA TreeA)) := *)
(*   match trs1 with *)
(*   | [] => Tick.ret (Thunk NilA, Thunk d) *)
(*   | t1 :: trs1' => let fix merge_trs1 trsR (dR : listA TreeA) : Tick (T (listA TreeA) * T (listA TreeA)) := *)
(*     (* here we compute the demand on [trs1] and [trsR] *) *)
(*     match trsR with *)
(*     | [] => Tick.ret (Thunk dR, Thunk NilA) *)
(*     | t2 :: trs2' => *)
(*       match Nat.compare (rank t1) (rank t2) with *)
(*       | Lt => *)
(*         let '(t1D, mD) := ConsD dR in *)
(*         let+ (trs1'D, trsRD) := thunkD (mergeAuxD trs1' trsR) mD in *)
(*         Tick.ret (Thunk (ConsA (strictD t1 t1D) trs1'D), strictConsD trsRD) *)
(*       | Eq => *)
(*         let+ (lD, mD) := insTreeD (link t1 t2) (mergeAux trs1' trs2') dR in *)
(*         let+ (t1D, t2D) := thunkD (linkD t1 t2) lD in *)
(*         let+ (trs1'D, trs2'D) := thunkD (mergeAuxD trs1' trs2') mD in *)
(*         Tick.ret (Thunk (ConsA (strictD t1 t1D) trs1'D), Thunk (ConsA (strictD t2 t2D) trs2'D)) *)
(*       | Gt => *)
(*         let '(t2D, mD) := ConsD dR in *)
(*         let+ (trs1D, trs2'D) := thunkD (merge_trs1 trs2') mD in *)
(*         Tick.ret (trs1D, Thunk (ConsA (strictD t2 t2D) trs2'D)) *)
(*       end *)
(*     end in *)
(*     let+ (trs1D, trs2D) := merge_trs1 trs2 d in *)
(*     Tick.ret (strictConsD trs1D, trs2D) *)
(*   end. *)

(* Definition mergeD (hp1 hp2 : Heap) (d : HeapA) : Tick (T HeapA * T HeapA) := *)
(*   let+ (ts1D, ts2D) := thunkD (mergeAuxD (trees hp1) (trees hp2)) (treesA d) in *)
(*   Tick.ret (Thunk (MkHeapA ts1D), Thunk (MkHeapA ts2D)). *)

(* Fixpoint removeMinAux (ts : list Tree) : option (Tree * list Tree) := *)
(*   match ts with *)
(*   | [] => None *)
(*   | t :: ts' => match removeMinAux ts' with *)
(*     | None => Some (t, []) *)
(*     | Some (t', ts'') => if leb (root t) (root t') *)
(*       then Some (t, ts') *)
(*       else Some (t', t :: ts'') *)
(*     end *)
(*   end. *)

(* Definition SomeD {A} `{Bottom A} (x : option A) : A := *)
(*   match x with *)
(*   | Some y => y *)
(*   | _ => bottom *)
(*   end. *)

(* Fixpoint removeMinAuxD (ts : list Tree) (d : option (T TreeA * T (listA TreeA))) *)
(*   : Tick (T (listA TreeA)) := *)
(*   match ts with *)
(*   | [] => Tick.ret (Thunk NilA) *)
(*   | t :: ts' => match removeMinAux ts' with *)
(*     | None => *)
(*       let (tD, _) := SomeD d in *)
(*       let+ ts'D := removeMinAuxD ts' None in *)
(*       Tick.ret (Thunk (ConsA tD ts'D)) *)
(*     | Some (t', ts'') => if leb (root t) (root t') *)
(*       then *)
(*         let '(tD, ts'D) := SomeD d in *)
(*         let+ ts'D := removeMinAuxD ts' (Some (strictD t' Undefined, Undefined)) in *)
(*         Tick.ret (Thunk (ConsA tD ts'D)) *)
(*       else *)
(*         let '(t'D, tts''D) := SomeD d in *)
(*         let '(tD, ts''D) := TConsD tts''D in *)
(*         let+ ts'D := removeMinAuxD ts' (Some (strictD t' t'D, ts''D)) in *)
(*         Tick.ret (Thunk (ConsA tD ts'D)) *)
(*     end *)
(*   end. *)

(* Definition removeMinTree (hp : Heap) *)
(*   : option ((Tree) * (Heap)) := *)
(*   match removeMinAux (trees hp) with *)
(*   | Some (t, ts) => Some (t, MkHeap ts) *)
(*   | None => None *)
(*   end. *)

(* Definition removeMinTreeD (hp : Heap) (d : option (TreeA * HeapA))  *)
(*   : Tick (T HeapA) := *)
(*   match d with *)
(*   | Some (tD, hpD) => *)
(*     let+ trsD := removeMinAuxD (trees hp) (Some (Thunk tD, treesA hpD)) in *)
(*       Tick.ret (Thunk (MkHeapA trsD)) *)
(*   | None => *)
(*     let+ trsD := removeMinAuxD (trees hp) None in *)
(*       Tick.ret (Thunk (MkHeapA trsD)) *)
(*   end. *)

(* Definition valid_Tree (t : Tree) : Prop. *)
(* Admitted. *)

(* Fixpoint valid_Trees (r : nat) (ts : list Tree) : Prop := *)
(*   match ts with *)
(*   | nil => True *)
(*   | t :: ts => valid_Tree t /\ r <= rank t /\ valid_Trees (S (rank t)) ts *)
(*   end. *)

(* Definition valid_Heap (h : Heap) : Prop := valid_Trees 0 (trees h). *)

(* Definition max_rank (xs : list Tree) : nat. *)
(* Admitted. *)

(* (* number of zeros in the binary representation of xs *) *)
(* Definition zbitcount (xs : list Tree) : nat := *)
(*   max_rank xs - length xs. *)

(* Definition pot_heap h := zbitcount (trees h). *)

(* Definition pot_heapA (h : HeapA) : nat. *)
(* Admitted. *)

(* Inductive less_defined_TreeA : TreeA -> TreeA -> Prop := *)
(* | ld_node : forall n1 n2 x1 x2 ts1 ts2, *)
(*     less_defined n1 n2 -> *)
(*     less_defined x1 x1 -> *)
(*     less_defined ts1 ts2 -> *)
(*     less_defined_TreeA (NodeA n1 x1 ts1) (NodeA n2 x2 ts2). *)
(* #[global] Instance LessDefined_TreeA : LessDefined TreeA := less_defined_TreeA. *)

(* #[global] Instance Exact_Tree : Exact Tree TreeA := *)
(*   fun t => match t with *)
(*            | Node n x t => NodeA (exact n) (exact x) (exact t) *)
(*            end. *)

(* Lemma link_approx (t1 t2 : Tree) (outD : TreeA) *)
(*   : outD `is_approx` link t1 t2 -> *)
(*     Tick.val (linkD t1 t2 outD) `is_approx` (t1, t2). *)
(* Proof. *)
(*   destruct 1 as [n1 n2 x1 x2 ts1 ts2 Hn Hx Hts]. *)
(*   constructor; destruct t1, t2, ts1. simpl; destruct (Nat.leb_spec n0 n4), x. *)
(*   constructor. unfold less_defined. *)
(*   unfold exact. unfold AO_Exact. *)
(* Admitted. *)

(*   (* destruct t1, t2. simpl. destruct (Nat.leb_spec n0 n4). t1; simpl. destruct x. simpl. *) *)


(*   (* destruct t1, t2, 1. simpl. destruct (Nat.leb_spec n0 n2), ts1; constructor; simpl; try (destruct x); simpl; auto. *) *)
(*   (* constructor. *) *)

(*   (* intros. unfold less_defined in *. destruct H. *) *)
(*   (* destruct t1 as [n1 x1 ts1], t2 as [n2 x2 ts2]. *) *)
(*   (* destruct 1 as [na1 na2 xa1 xa2 ta1 ta2 Hna Hxa Htas]. *) *)
(*   (* unfold linkD. destruct (Nat.leb_spec x1 x2); split. unfold TConsD. destruct ta1. destruct x. simpl. *) *)



(* Definition less_defined_HeapA (h1 h2 : HeapA) : Prop := less_defined (treesA h1) (treesA h2). *)
(* #[global] Instance LessDefined_HeapA : LessDefined HeapA := less_defined_HeapA. *)

(* #[global] Instance Exact_HeapA : Exact Heap HeapA := fun h => MkHeapA (exact (trees h)). *)

(* Definition measureT {a : Type} (f : a -> nat) (t : T a) : nat := *)
(*   match t with *)
(*   | Undefined => 0 *)
(*   | Thunk x => f x *)
(*   end. *)

(* (* *)
(* out = insert x inp *)
(* cost (insertD x inp ..) <= zbitcount out - zbitcount inp *)
(* *) *)

(* Theorem cost_insert : forall x h d, d `is_approx` insert x h -> *)
(*   forall xD hD, (xD, hD) = Tick.val (insertD x h d) -> *)
(*   measureT pot_heapA hD + Tick.cost (insertD x h d) <= 1 + pot_heapA d. *)
(* Proof. *)
(* Admitted. *)

(* Definition findMin (hp : Heap) *)
(*   : option A := *)
(*   match removeMinTree hp with *)
(*   | None => None *)
(*   | Some (t, _) => Some (root t) *)
(*   end. *)

(* Definition findMinD (hp : Heap) (d : option A) : Tick (T HeapA) := *)
(*   match d with *)
(*   | Some n =>  *)
(*     let t := NodeA Undefined (Thunk n) Undefined in *)
(*     let+ hpD := removeMinTreeD hp (Some (t, MkHeapA Undefined)) in *)
(*     Tick.ret hpD *)
(*   | None => Tick.ret (Undefined) *)
(*   end. *)

(* Definition deleteMin (hp : Heap) *)
(*   : Heap := *)
(*   match removeMinTree hp with *)
(*   | None => MkHeap [] *)
(*   | Some (Node r v c, ts) => *)
(*     merge (MkHeap (rev c)) ts *)
(*   end. *)

(* Definition deleteMinD (hp : Heap) (d : HeapA) : Tick (T HeapA) := *)
(*   match removeMinTree hp with *)
(*   | None => removeMinTreeD hp None *)
(*   | Some (Node r v c, ts) => *)
(*     let+ (hpM1, hpM2) := mergeD (MkHeap (rev c)) ts d in *)
(*     (*TODO: rev is strict*) *)
(*     let ts := thunkD treesA hpM1 in *)
(*     let hpM1' := NodeA (Thunk r) (Thunk v) ts in *)
(*     removeMinTreeD hp (thunkD (H := None) (fun y => Some (hpM1', y)) hpM2) *)
(*   end. (*TODO: is None correct for H*) *)


(* (* *)
(* (* Potential: number of trees *)
(*    (times an implementation-dependent multiplicative factor) *)
(*    It would be 1 if we just counted calls to [link].  *) *)
(* 3  *)
(* Definition pot_heap (h : Heap) : T HeapA -> nat := *)
(*   measureT (fun _ => pot_trees (trees h)). *)

(* (* *)
(*   F : A -> B *)
(*   DF : A -> B -> A *)

(*   pot1 : B -> nat *)
(*   pot2 : A -> nat *)

(*   COST[DF a b] + pot1(DF a b) <= pot2(b) + constant *)
(* *) *)

(* Definition OTick_has_cost {A' : Type} (m : nat) (u : OTick A') (pre : A' -> nat) (post : nat) := *)
(*   match u with *)
(*   | None => False *)
(*   | Some v => m + pre (Tick.val v) + Tick.cost v <= post *)
(*   end. *)

(* Definition has_cost_ {A B : AA} {a : A} {b : B} *)
(*     (f : DF a b) (m : nat) (pre : approx A -> nat) (post : approx B -> nat) (n : nat) *)
(*   : Prop := *)
(*   forall b' : approx B, b' `is_approx` b -> *)
(*     OTick_has_cost m (apply f b') pre (n + post b'). *)

(* Definition has_cost {A B : AA} {a : A} {b : B} *)
(*     (f : DF a b) (pre : approx A -> nat) (post : approx B -> nat) (n : nat) *)
(*   : Prop := *)
(*   has_cost_ f 0 pre post n. *)

(* Definition measure_plus {A B : Type} (f : A -> nat) (g : B -> nat) (xy : A * B) : nat := *)
(*   f (fst xy) + g (snd xy). *)

(* Infix "+++" := measure_plus (at level 40). *)

(* Definition zero {A : Type} (_ : A) : nat := 0. *)

(* (* Amortized complexity of insert *) *)
(* Definition insert_budget := 3. *)

(* Class Subadditive {A : AA} (f : approx A -> nat) : Prop := *)
(*   { subadditive_zero : forall x, f (bottom_of x) = 0 *)
(*   ; subadditive_lub  : forall x y, f (lub x y) <= f x + f y *)
(*   }. *)

(* #[global] *)
(* Instance Subadditive_zero {A : AA} : Subadditive (A := A) zero. *)
(* Proof. *)
(*   constructor; reflexivity. *)
(* Qed. *)

(* #[global] *)
(* Instance Subadditive_measure_plus {A B : AA} *)
(*     (f : approx A -> nat) (g : approx B -> nat) *)
(*     `(!Subadditive f, !Subadditive g) *)
(*   : Subadditive (f +++ g). *)
(* Proof. *)
(*   constructor. *)
(*   - intros []; unfold measure_plus; cbn. *)
(*     rewrite 2 subadditive_zero. reflexivity. *)
(*   - intros x y. unfold measure_plus; cbn. *)
(*     rewrite 2 subadditive_lub. lia. *)
(* Qed. *)

(* #[global] Instance Proper_S_le : Proper (le ==> le) S. *)
(* Proof. exact le_n_S. Qed. *)

(* Lemma subadditive_sizeX' {a : Type} (n : nat) (xs ys : listA a) *)
(*   : sizeX' n (lub xs ys) <= sizeX' n xs + sizeX' n ys. *)
(* Proof. *)
(*   revert ys; induction xs as [ | x | x xs IH ]; intros [| y [] ]; cbn; try rewrite IH; lia. *)
(* Qed. *)

(* (* *)
(* #[global] *)
(* Instance Subadditive_pot_heap : Subadditive (A := AA_Heap) pot_heap. *)
(* Proof. *)
(*   constructor. *)
(*   - admit. *)
(*   - admit. *)
(* Admitted. *)
(* *) *)

(* Lemma let_cost {A B C : AA} {a : A} {b : B} {c : C} {f : DF a b} {g : DF (a, b) c} *)
(*     {pre : approx A -> nat} *)
(*     `{!Subadditive pre} *)
(*     (mid : approx B -> nat) (post : approx C -> nat) (m0 m n : nat) *)
(*     (_ : has_cost_ f m0 pre mid m) *)
(*     (_ : has_cost_ g m (pre +++ mid) post n) *)
(*   : has_cost_ (DF.let_ f g) m0 pre post n. *)
(* Proof. *)
(*   unfold DF.let_. *)
(* Admitted. *)

(* (* *)
(*   f : G -> A *)

(*   g : G * A -> B *)

(*   n + post b' *)
(*   >= *)
(*   m + cost (g' b') + pre (fst (g' b')) + mid (snd (g' b')) *)
(*   >= *)
(*   m0 + cost (g' b') + cost (f' ...) + pre (fst (g' b')) + pre (f' ...) *)
(*   >= *)
(*   m0 + cost ... + pre (lub (fst (g' b')) (f' ...)) *)
(* *) *)

(* Lemma tick_cost {A B : AA} {a : A} {b : B} (f : DF a b) *)
(*     m pre post n *)
(*   : has_cost_ f (S m) pre post n -> *)
(*     has_cost_ (DF.tick f) m pre post n. *)
(* Admitted. *)

(* Lemma match_list_nil_cost {G A B : AA} {P : list A -> B} {g : G} *)
(*     `{!AutoDF g []} *)
(*     (NIL : DF (g, []) (P [])) *)
(*     (CONS : forall x ys, DF (g, x :: ys, x, ys) (P (x :: ys))) *)
(*     m pre post n *)
(*   : has_cost_ NIL m (pre +++ zero) post n -> *)
(*     has_cost_ (match_list (var []) NIL CONS) m pre post n. *)
(* Admitted. *)

(* Definition measure_list_uncons {A  : AA} (x : A) (xs : list A) pot0 pot_hd pot_tl : Prop *)
(*   := forall (x' : approx A) (xs' : approx (AA_listA A)), x' `is_approx` x -> xs' `is_approx` xs -> *)
(*       pot0 (Thunk (ConsA (Thunk x') xs')) <= pot_hd + pot_tl xs'. *)

(* Lemma match_list_cons_cost {G A B : AA} {P : list A -> B} {g : G} (x : A) (xs : list A) *)
(*     `{!AutoDF g (x :: xs)} *)
(*     (NIL : DF (g, []) (P [])) *)
(*     (CONS : forall x ys, DF (g, x :: ys, x, ys) (P (x :: ys))) *)
(*     m pre pot0 m' pot_hd pot_tl post n *)
(*   : has_cost_ (var (g := g) (x :: xs)) m pre pot0 m' -> *)
(*     measure_list_uncons x xs pot0 pot_hd pot_tl -> *)
(*     has_cost_ (CONS x xs) (m + pot_hd) (((pre +++ pot0) +++ zero) +++ pot_tl) post n -> *)
(*     has_cost_ (match_list (var (x :: xs)) NIL CONS) m pre post n. *)
(* Admitted. *)

(* (* *)
(* Lemma pot_trees_uncons (r : nat) (t : Tree) (ts : list Tree) *)
(*   : valid_Trees r (t :: ts) -> *)
(*     measure_list_uncons t ts (pot_trees r (t :: ts)) (rank t - r) (pot_trees (S (rank t)) ts). *)
(* Proof. *)
(* Admitted. *)
(* *) *)

(* Lemma consD_cost {G : AA} {g : G} {r : nat} {x : Tree} {xs : list Tree} *)
(*     {xD : DF g x} {xsD : DF g xs} {m pre n} *)
(*     `{!Subadditive pre} *)
(*   : valid_Trees r (x :: xs) -> *)
(*     m <= n + rank x - r -> *)
(*     has_cost_ xD 0 pre zero 0 -> *)
(*     has_cost_ xsD 0 pre zero (pot_trees xs - r) -> *)
(*     has_cost_ (consD xD xsD) m pre zero (pot_trees (x :: xs) - r). *)
(* Admitted. *)

(* (* *)
(* Lemma nilD_cost {G : AA} {g : G} {pre n} {r} *)
(*     `{!Subadditive pre} *)
(*   : has_cost_ (a := g) nilD 0 pre zero (pot_trees []). *)
(* Proof. *)
(* Admitted. *)
(* *) *)

(* Lemma has_cost_id {A : AA} {x : A} p n : has_cost_ (DF.id x) n p p n. *)
(* Proof. *)
(*   unfold has_cost_, DF.id; cbn. lia. *)
(* Qed. *)

(* Lemma has_cost_compose {A B C : AA} {x : A} {y : B} {z : C} *)
(*   (f : DF x y) (g : DF y z) nf ng n pf pg p *)
(*   : has_cost_ f nf pf pg ng -> *)
(*     has_cost_ g ng pg p n -> *)
(*     has_cost_ (f >>> g) nf pf p n. *)
(* Proof. *)
(*   unfold has_cost_, DF.compose, DF.Raw_compose; cbn. *)
(*   intros Hf Hg z' Az. *)
(* Admitted. *)

(* Existing Class has_cost_. *)
(* #[global] *)
(* Hint Mode has_cost_ ! ! ! ! ! - - - - : typeclass_instances. *)

(* #[global] *)
(* Instance has_cost_autoDF_id {A : AA} {x : A} p *)
(*   : has_cost_ (autoDF (x := x) (y := x)) 0 p p 0. *)
(* Proof. *)
(*   unfold autoDF, AutoDF_id. apply has_cost_id. *)
(* Qed. *)

(* Lemma has_cost_proj1 {A B : AA} {x : A} {y : B} n p q *)
(*   : has_cost_ (DF.proj1 (x := x) (y := y)) n (p +++ q) p n. *)
(* Proof. *)
(* Admitted. *)

(* Lemma has_cost_proj2 {A B : AA} {x : A} {y : B} n p q *)
(*   : has_cost_ (DF.proj2 (x := x) (y := y)) n (p +++ q) q n. *)
(* Proof. *)
(* Admitted. *)

(* #[global] *)
(* Instance has_cost_autoDF_proj1 {A B C : AA} {x : A} {y : B} {z : C} `{!AutoDF x z} {p q r} *)
(*   : has_cost_ (autoDF (x := x) (y := z)) 0 p r 0 -> *)
(*     has_cost_ (autoDF (x := (x, y)) (y := z)) 0 (p +++ q) r 0. *)
(* Proof. *)
(*   unfold autoDF at 2, AutoDF_fst. *)
(*   intros H. *)
(*   eapply has_cost_compose. *)
(*   - apply has_cost_proj1. *)
(*   - apply H. *)
(* Qed. *)

(* #[global] *)
(* Instance has_cost_autoDF_proj2 {A B : AA} {x : A} {y : B} {p q} *)
(*   : has_cost_ (autoDF (x := (x, y)) (y := y)) 0 (p +++ q) q 0. *)
(* Proof. *)
(*   apply has_cost_proj2. *)
(* Qed. *)

(* #[global] *)
(* Instance has_cost_pair {A B C : AA} {x : A} {y : B} {z : C} {p q r} *)
(*     (f : DF x y) (g : DF x z) *)
(*   : has_cost_ f 0 p q 0 -> *)
(*     has_cost_ g 0 p r 0 -> *)
(*     has_cost_ (DF.pair f g) 0 p (q +++ r) 0. *)
(* Proof. *)
(* Admitted. *)

(* #[global] *)
(* Instance has_cost_autoDF_pair {A B C : AA} {x : A} {y : B} {z : C} {p q r} *)
(*     `{!AutoDF x y, !AutoDF x z} *)
(*   : has_cost_ (autoDF (x := x) (y := y)) 0 p q 0 -> *)
(*     has_cost_ (autoDF (x := x) (y := z)) 0 p r 0 -> *)
(*     has_cost_ (autoDF (x := x) (y := (y, z))) 0 p (q +++ r) 0. *)
(* Proof. *)
(*   apply has_cost_pair. *)
(* Qed. *)

(* Lemma var_cost {G A : AA} {g : G} {x : A} `{!AutoDF g x} {pre post} *)
(*     {Hauto : has_cost_ (autoDF (x := g) (y := x)) 0 pre post 0} *)
(*   : has_cost_ (var (g := g) x) 0 pre post 0. *)
(* Proof. *)
(*   exact Hauto. *)
(* Qed. *)

(* Lemma weaken_cost {G A : AA} (g : G) (x : A) (f : DF g x) m pre post n *)
(*   : m <= n -> *)
(*     has_cost_ f 0 pre post 0 -> *)
(*     has_cost_ f m pre post n. *)
(* Proof. *)
(* Admitted. *)

(* Lemma call_cost {G1 G2 A : AA} {g1 : G1} {g2 : G2} {x : A} `{!AutoDF g2 g1} *)
(*     {f : DF g1 x} {pre1 pre2 post n m} *)
(*     {Hauto : has_cost_ (autoDF (x := g2) (y := g1)) 0 pre2 pre1 0} *)
(*   : has_cost_ f n pre1 post m -> *)
(*     has_cost_ (call (g1 := g1) (g2 := g2) f) n pre2 post m. *)
(* Proof. *)
(*   unfold call. *)
(*   intros H. eapply has_cost_compose. *)
(*   - eapply weaken_cost; [ reflexivity | ]. *)
(*     exact Hauto. *)
(*   - apply H. *)
(* Qed. *)

(* Lemma if_cost {G A : AA} {g : G} {b : bool} {P : bool -> A} *)
(*     (CASE : DF g b) *)
(*     (TRUE : DF g (P true)) *)
(*     (FALSE : DF g (P false)) *)
(*     m n p q *)
(*   : has_cost_ CASE 0 p zero 0 -> *)
(*     (b = true -> has_cost_ TRUE m p q n) -> *)
(*     (b = false -> has_cost_ FALSE m p q n) -> *)
(*     has_cost_ (DF.if_ CASE TRUE FALSE) m p q n. *)
(* Proof. *)
(* Admitted. *)

(* Theorem insTree_cost (t : Tree) (ts : list Tree) *)
(*   : valid_Tree t -> *)
(*     valid_Trees (rank t) ts -> *)
(*     has_cost_ (insTreeDF t ts) (pot_trees ts) (zero +++ zero) zero (pot_trees (insTree t ts)). *)
(* Proof. *)
(* Admitted. (* *)
(*   revert t; induction ts as [ | u ts IH]; intros t Vt Vts. *)
(*   - cbn [insTreeDF]. *)
(*     apply tick_cost. *)
(*     apply match_list_nil_cost. *)
(*     apply consD_cost. *)
(*     + split; [ | split]; [ assumption | lia | exact I]. *)
(*     + admit. *)
(*     + apply var_cost. *)
(*     + eapply weaken_cost. { unfold insert_budget; lia. } *)
(*       apply nilD_cost. *)
(*   - cbn [insTreeDF]. *)
(*     apply tick_cost. *)
(*     eapply match_list_cons_cost with (pot0 := pot_trees (rank t) (u :: ts)) (pot_tl := pot_trees (S (rank u)) ts) (m' := S (rank t)). *)
(*     + apply weaken_cost. { reflexivity. } *)
(*       apply var_cost. *)
(*     + apply pot_trees_uncons. assumption. *)
(*     + apply let_cost with (mid := zero) (m := S (rank t) + (rank u - rank t)). *)
(*       { apply call_cost. admit. } *)
(*       apply let_cost with (mid := zero) (m := S (rank t) + (rank u - rank t)). *)
(*       { apply call_cost. admit. } *)
(*       apply let_cost with (mid := zero) (m := S (rank t) + (rank u - rank t)). *)
(*       { apply call_cost. admit. } *)
(*       refine (if_cost _ _ _ _ _ _ _ _ _ _). *)
(*       * intros Htrue. *)
(*         cbn [insTree]. rewrite Htrue. *)
(*         assert (Vts' : valid_Trees (S (rank t)) (u :: ts)). *)
(*         { admit. } *)
(*         assert (Vtts' : valid_Trees 0 (t :: u :: ts)). *)
(*         { admit. } *)
(*         apply consD_cost. *)
(*         { assumption. } *)
(*         { admit. } *)
(*         { exact _.  } *)
(*         { apply consD_cost. *)
(*           { assumption. } *)
(*           { lia. } *)
(*           { exact _. } *)
(*           { eapply weaken_cost. cbn. lia. apply var_cost. } } *)
(*       * intros Hfalse. *)
(*         apply let_cost with (mid := zero) (m := 1 + (rank u - r)). *)
(*         { apply call_cost. admit. } *)
(*         apply call_cost. *)
(*         eapply weaken_cost. *)
(* Qed. *)
(* *) *)

(* Lemma nodeD_cost_zero {r : AA} {s : r} {n x : nat} {ts : list Tree} *)
(*     {pre : approx r -> nat} *)
(*     `{!Subadditive pre} *)
(*     (nD : DF s n) (xD : DF s x) (tsD : DF s ts) *)
(*   : has_cost_ nD 0 pre zero 0 -> *)
(*     has_cost_ xD 0 pre zero 0 -> *)
(*     has_cost_ tsD 0 pre zero 0 -> *)
(*     has_cost_ (nodeD nD xD tsD) 0 pre zero 0. *)
(* Proof. *)
(* Admitted. *)

(* Theorem insert_cost (x : A) (h : Heap) *)
(*   : valid_Heap h -> *)
(*     has_cost_ (insertDF x h) 0 (zero +++ zero) zero insert_budget. *)
(* Proof. (* *)
(*   intros Vh. *)
(*   change insert_budget with (0 + insert_budget). *)
(*   apply let_cost with (mid := zero) (m := 0); [ admit | |]. *)
(*   { apply nodeD_cost_zero. *)
(*     + admit. *)
(*     + admit. *)
(*     + admit. } *)
(*   change insert_budget with (0 + insert_budget). *)
(*   apply let_cost with (mid := zero) (m := 0); [ admit | |]. *)
(*   { admit. } *)
(*   assert (HH : has_cost_ (insTreeDF (Node 0 x []) (trees h)) 0 (zero +++ pot_list) pot_list insert_budget). *)
(*   { apply insTree_cost. assumption. } *)
(*   admit. *) *)
(* Admitted. *)

(* (* *)
(* Below: TODO *)
(* *) *)

(* Canonical AA_comparison : ApproxAlgebra := exact_AA comparison. *)

(* Definition DF_compare {G A : ApproxAlgebra} {g : G} {b : comparison} {P : comparison -> A} *)
(*   : DF g b -> DF g (P Lt) -> DF g (P Eq) -> DF g (P Gt) -> DF g (P b) := *)
(*   (* TODO: use first argument *) *)
(*   match b with *)
(*   | Lt => fun _ p _ _ => p *)
(*   | Eq => fun _ _ p _ => p *)
(*   | Gt => fun _ _ _ p => p *)
(*   end. *)

(* Parameter compare_ : forall x y : nat, DF (x, y) (Nat.compare x y). *)

(* Fixpoint mergeAuxDF (trs1 trs2 : list Tree) : DF (trs1, trs2) (mergeAux trs1 trs2) := *)
(*   match_list (P := fun trs1 => mergeAux trs1 trs2) (var trs1) *)
(*     (var trs2) *)
(*     (fun t1 trs1' => *)
(*       let trs1_ := t1 :: trs1' in *)
(*       let fix merge_trs1DF trsR : DF (t1 :: trs1', t1, trs1', trsR) (mergeAux trs1_ trsR) := *)
(*         match_list (P := fun trsR => mergeAux trs1_ trsR) (var trsR) *)
(*         (var trs1_) *)
(*         (fun t2 trs2' => *)
(*           let trsR_ := t2 :: trs2' in *)
(*           DF.let_ (call (rankDF t1)) *)
(*           (DF.let_ (call (rankDF t2))  *)
(*           (DF.let_ (call (compare_ (rank t1) (rank t2))) *)
(*           (DF_compare (P := fun b => match b with Eq => _ | Lt => _ | Gt => _ end) *)
(*              (var (Nat.compare (rank t1) (rank t2))) *)
(*              (DF.let_ (call (mergeAuxDF trs1' trsR_)) *)
(*               (consD (var t1) (call (mergeAuxDF trs1' trsR_)))) *)
(*               (DF.let_ (call (linkDF t1 t2)) *)
(*                 (DF.let_ (call (mergeAuxDF trs1' trs2')) *)
(*                 (DF.let_ (call (insTreeDF (link t1 t2) (mergeAux trs1' trs2'))) *)
(*                 (call (insTreeDF (link t1 t2) (mergeAux trs1' trs2')))))) *)
(*               (consD (var t2) (call (merge_trs1DF trs2'))))))) *)
(*       in *)
(*       call (merge_trs1DF trs2)). *)

(* Definition mergeDF (hp1 hp2 : Heap) : DF (hp1, hp2) (merge hp1 hp2) := *)
(*   DF.let_ (treesD (var hp1))  *)
(*   (DF.let_ (treesD (var hp2)) *)
(*   (MkHeapD (call (mergeAuxDF _ _)))). *)

(* Fixpoint removeMinAux (ts : list Tree) : option (Tree * list Tree) :=  *)
(*   match ts with *)
(*   | [] => None *)
(*   | t :: ts' => match removeMinAux ts' with *)
(*     | None => Some (t, []) *)
(*     | Some (t', ts'') => if leb (root t) (root t') *)
(*       then Some (t, ts') *)
(*       else Some (t', t :: ts'') *)
(*     end *)
(*   end. *)

(* Canonical AA_optionA (a : AA) : AA := *)
(*   {| carrier := option a *)
(*   ;  approx := T (option (approx a)) *)
(*   ; AA_IsAA := TODO *)
(*   ; AA_IsAS := TODO *)
(*   ; AA_Setoid := TODO *)
(*   |}. *)

(* Definition noneD {G a : AA} {g : G} : DF g (None (A := a)). *)
(* Admitted. *)

(* Definition someD {G A : AA} {g : G} {x : A} *)
(*   : DF g x -> DF g (Some x). *)
(* Admitted. *)

(* (* Auxiliary definition for match_option *) *)
(* Definition force_some {G A : AA} {g : G} {x : A} *)
(*   : DF (g, (Some x)) (g, x). *)
(* Admitted. *)

(* Definition match_option {G A B : AA} {P : option A -> B} {g : G} {xO : option A} *)
(*     (CASE : DF g xO) *)
(*     (NONE : DF g (P None)) *)
(*     (SOME : forall x, DF (g, x) (P (Some x))) *)
(*   : DF g (P xO) := *)
(*   DF.bind CASE *)
(*   match xO with *)
(*   | None => DF.proj1 >>> NONE *)
(*   | Some x => force_some >>> SOME x *)
(*   end. *)

(* Fixpoint removeMinAuxDF (ts : list Tree) : DF ts (removeMinAux ts). *)
(* Admitted. (* match_list (P := fun ts => removeMinAux ts) (var ts) *)
(*   noneD *)
(*   (fun t ts' =>  *)
(*     DF.let_ (call (removeMinAuxDF ts')) *)
(*     (match_option (P  *)
(*       (someD (DF.pair (var t) nilD)) *)
(*       (fun p =>  *)
(*         DF.let_ (call (rootDF t)) *)
(*         (DF.let_ (DF.proj1 >>> call (rootDF _)) *)
(*         (DF.let_ (DF.proj1 >>> call (lt_ (root _) (root t))) *)
(*           (DF.if_ (P := fun b => if b then _ else _) *)
(*             (DF.proj1 >>> var (root _ <? root t)) *)
(*             (someD (DF.pair (DF.proj1) (DF.proj2 >>> consD (var t) _))) *)
(*             (someD (DF.pair (var t) (var ts'))))))) *)
(*     )).*) *)

(* Definition heapConvert (p : Tree * (list Tree)) : (Tree * Heap) := *)
(*   match p with *)
(*   | (t, ts) => (t, MkHeap ts) *)
(*   end. *)

(* Definition heapConvertDF (p : Tree * (list Tree)) : DF p (heapConvert p). *)
(* Admitted. *)

(* Definition removeMinTree (hp : Heap)  *)
(*   : option ((Tree) * (Heap)) := *)
(*   match removeMinAux (trees hp) with *)
(*   | Some (t, ts) => Some (t, MkHeap ts) *)
(*   | None => None *)
(*   end. *)

(* (*Definition mergeDF (hp1 hp2 : Heap) : DF (hp1, hp2) (merge hp1 hp2) := *)
(*   DF.let_ (treesD (var hp1))  *)
(*   (DF.let_ (treesD (var hp2)) *)
(*   (MkHeapD (call (mergeAuxDF _ _)))).*) *)

(* (*Definition bind `{x : a, y : b, z : c} `(f : DF x y) `(g : DF (x, y) z) : DF x z := *)
(*   pair (id x) f >>> g.*) *)

(* (*Definition treesD {G : AA} {g : G} {h : Heap} (f : DF g h) : DF g (trees h).*) *)

(* (*Definition match_option {G A B : AA} {P : option A -> B} {g : G} {xO : option A} *)
(*     (CASE : DF g xO) *)
(*     (NONE : DF g (P None)) *)
(*     (SOME : forall x, DF (g, x) (P (Some x))) *)
(*   : DF g (P xO) :=*) *)

(* (* *)
(* Definition var {G A : AA} {g : G} (x : A) `{AutoDF _ _ g x} : DF g x := autoDF. *)
(* Definition call {x : A} `{AutoDF _ _ g2 g1} (f : DF g1 x) *)
(*   : DF g2 x := autoDF >>> f.*) *)


(* (*Fixpoint removeMinAuxDF (ts : list Tree) : DF ts (removeMinAux ts). *)

(* Definition someD {G A : AA} {g : G} {x : A} *)
(*   : DF g x -> DF g (Some x).*) *)

(* Definition removeMinTreeDF (hp : Heap) : DF hp (removeMinTree hp). *)
(* Admitted. *)
(*   (*DF.let_  *)
(*   (treesD (var hp)) *)

(*   (*(g: DF (hp, trees hp) (removeMinTree hp))*) *)

(*   (DF.let_ *)
(*     (*(f : DF (hp, trees hp) (removeMinAux ts))*) (call (removeMinAuxDF _)) *)
(*     (*(g : DF ((hp, trees hp), (removeMinAux ts)) (removeMinTree hp))*) *)
(*     (match_option {P := fun h => removeMinAux h} *)
(*       (*(CASE : DF ((hp, trees hp), (removeMinAux ts)) (removeMinAux ts))*) *)
(*       (var (removeMinAux (trees hp))) *)
(*       (*(NONE: DF ((hp, trees hp), (removeMinAux ts)) (P None))*) *)
(*       noneD *)
(*       (*(SOME: forall x, DF (((hp, trees hp), (removeMinAux ts)), x) (P (Some x))))*) *)
(*       (fun p => someD (call (heapConvertDF p))) *)
(*     )).*) *)
(* (*  (DF.let_ (call (removeMinAuxDF _)) *)
(*   (match_option (var (removeMinAux ts))  *)
(*   noneD *)
(*   (fun p => someD (DF.pair (DF.proj1) (DF.proj2 >>> MkHeapD _)))).*) *)

(* Definition findMin (hp : Heap) *)
(*   : option A := *)
(*   match removeMinTree hp with *)
(*   | None => None *)
(*   | Some (t, _) => Some (root t) *)
(*   end. *)

(* Definition findMinDF (hp : Heap) : DF hp (findMin hp). *)
(* Admitted. (* := *)
(*   DF.let_ (call (removeMinTreeDF hp)) *)
(*   (match_option (var _) *)
(*     noneD *)
(*     (fun p => DF.proj1 >>>  *)
(*       DF.let_ (rootDF _) *)
(*       (someD _))).*) *)

(* Definition deleteMin (hp : Heap) *)
(*   : Heap := *)
(*   match removeMinTree hp with *)
(*   | None => MkHeap [] *)
(*   | Some (Node r v c, ts) => *)
(*     merge (MkHeap (rev c)) ts *)
(*   end. *)

(* Definition revDF {A : AA} (xs : list A) : DF xs (rev xs). *)
(* Admitted. *)

(* Definition deleteMinDF (hp : Heap) : DF hp (deleteMin hp). *)
(* Admitted. *)
(* (*removeMinTreeDF hp >>> *)
(*   (match_option (var _) *)
(*   (MkHeapD nilD) *)
(*   (fun p => DF.proj1 >>> *)
(*     match_Tree *)
(*     _ *)
(*     (fun r1 v1 c1 =>  *)
(*       DF.let_ (revD c1) (DF.let_ (MkHeapD _) (mergeDF _ (DF.proj2)))))).*) *)


(* (* *)
(* Canonical AABComparison : AA := *)
(*   {| carrier := comparison |}. *)

(* Definition if_ {a b : AA} {x : a} {cond : bool} *)
(*   {f : bool -> b} *)
(*   (i : DF x cond) *)
(*   (thn : DF x (f true)) *)
(*   (els : DF x (f false)) *)
(*   : DF x (f cond). *)
(* Proof. refine TODO. Defined.   *)

(* (* Encoding of [Nat.compare] *) *)
(* Definition natCompare {a b : AA} {c : a} {x y : nat}  *)
(*   {f : comparison -> b} *)
(*   (nats : DF c (x, y)) *)
(*   (Lt_ : DF c (f Lt)) *)
(*   (Eq_ : DF c (f Eq)) *)
(*   (Gt_ : DF c (f Gt)) *)
(*   : DF c (f (Nat.compare x y)). *)
(* Proof. refine TODO. Defined. *)

(* Fixpoint mergeAuxDF (trs1 trs2 : list Tree) : DF (trs1, trs2) (mergeAux trs1 trs2). *)
(* Proof. *)
(*   refine ((TODO : DF (trs1, trs2) (trs2, trs1)) >>> *)
(*     (match_list (f := fun trs => mergeAux trs trs2) *)
(*     _ (fun t1 trs1' => _))). *)
(*   - cbn. refine TODO. *)
(*   - refine ((TODO: DF (trs2, t1, trs1') (t1, trs1', trs2)) >>> *)
(*     match_list (f := fun trs => mergeAux _ trs) *)
(*     _ (fun t2 trs2' => _)). *)
(*     + cbn [mergeAux]. refine (consD TODO TODO). *)
(*     + cbn [mergeAux]. refine (natCompare  *)
(*       (f := fun c => match c with *)
(*         | Lt => _ *)
(*         | Eq => _ *)
(*         | Gt => _ *)
(*         end) *)
(*         _ *)
(*         _ *)
(*         _  *)
(*         _). *)
(*         * refine TODO. *)
(*         * refine TODO. *)
(*         * refine TODO. *)
(*         * refine TODO.  *)
(* Defined. *)

(* Definition merge (hp1 hp2 : Heap) : Heap := *)
(*   MkHeap (mergeAux (trees hp1) (trees hp2)). *)

(* Definition mergeDF {hp1 hp2} : DF (hp1, hp2) (merge hp1 hp2). *)
(* Proof. *)
(*   refine (letDF (TODO >>> @treesD hp1) _). *)
(*   refine (letDF (TODO >>> @treesD hp2) _). *)
(*   refine (letDF (TODO >>> mergeAuxDF (trees hp1) (trees hp2)) _). *)
(*   refine (proj2DF >>> MkHeapD _). *)
(* Defined. *)

(* Fixpoint removeMinAux (ts : list Tree) :=  *)
(*   match ts with *)
(*   | [] => None *)
(*   | t :: ts' => match removeMinAux ts' with *)
(*     | None => Some (t, []) *)
(*     | Some (t', ts'') => if leb (root t) (root t') *)
(*       then Some (t, ts') *)
(*       else Some (t', t :: ts'') *)
(*     end *)
(*   end. *)

(* Canonical AAoption (a : AA) : AA := *)
(*   {| carrier := option a |}. *)

(* (* Encoding of match on options *) *)
(* Definition match_option {a b c : AA} {g : b} {f : option a -> c} {xM : option a} *)
(*     (NONE : DF g (f None)) *)
(*     (SOME : forall x, DF (g, x) (f (Some x))) *)
(*   : DF (g, xM) (f xM) := *)
(*   match xM with *)
(*   | None => TODO >>> NONE *)
(*   | Some x => TODO >>> (SOME x) *)
(*   end. *)

(* (* Encoding of None *) *)
(* Definition noneD {a b : AA} {x : a} : DF x (None (A := b)). *)
(* Proof. refine TODO. Defined. *)

(* (* Encoding of (Some _) *) *)
(* Definition someD {r a : AA} {s : r} {x : a} {xM : option a} (sD : DF s x) *)
(*   : DF s (Some x). *)
(* Proof. refine TODO. Defined. *)

(* Fixpoint removeMinAuxDF {ts} : DF ts (removeMinAux ts). *)
(* Proof. *)
(*   refine (TODO >>>  *)
(*     match_list (f := fun ts => removeMinAux ts) (g := ts) _ (fun t ts' => _)). (*TODO*) *)
(*   - cbn. refine TODO. *)
(*   - cbn. refine TODO. *)
(* Defined. *)

(* Definition removeMinTree (hp : Heap)  *)
(*   : option ((Tree) * (Heap)) := *)
(*   match removeMinAux (trees hp) with *)
(*   | Some (t, ts) => Some (t, MkHeap ts) *)
(*   | None => None *)
(*   end. *)

(* Definition removeMinTreeDF {hp} : DF hp (removeMinTree hp). *)
(* Proof. *)
(*   refine (letDF (TODO >>> @treesD hp) _). *)
(*   refine (letDF (TODO >>> removeMinAuxDF) _). *)
(*   refine (TODO >>> match_option  *)
(*     (f := fun pM => match pM with *)
(*       | None => None *)
(*       | Some (t, ts) => Some (t, MkHeap ts)  *)
(*       end) *)
(*     (g := hp) (*TODO*) *)
(*     (xM := removeMinAux (trees hp)) *)
(*     _ (fun x => _)).  *)
(*   - refine noneD. *)
(*   - refine TODO. Unshelve. cbn. apply trees. assumption. (*TODO*) *)
(* Defined. *)

(* Definition findMin (hp : Heap) *)
(*   : option A := *)
(*   match removeMinTree hp with *)
(*   | None => None *)
(*   | Some (t, _) => Some (root t) *)
(*   end. *)

(* Definition findMindDF {hp} : DF hp (findMin hp). *)
(* Proof. *)
(*   refine (TODO >>> match_option  *)
(*     (f := fun pM => match pM with *)
(*       | None => None *)
(*       | Some (t, _) => Some (root t)  *)
(*   end) *)
(*   (g := hp) (*TODO*) *)
(*   (xM := removeMinTree hp) *)
(*   _ (fun x => _)).  *)
(*   - refine noneD. *)
(*   - refine TODO. (*TODO*) *)
(* Defined. *)

(* Definition deleteMin (hp : Heap) *)
(*   : Heap := *)
(*   match removeMinTree hp with *)
(*   | None => MkHeap [] *)
(*   | Some (Node r v c, ts) => *)
(*     merge (MkHeap (rev c)) ts *)
(*   end. *)

(* Definition deleteMinDF {hp} : DF hp (deleteMin hp). *)
(* Proof. *)
(*   refine (TODO >>> match_option  *)
(*     (f := fun pM => match pM with *)
(*       | None => MkHeap [] *)
(*       | Some (Node r v c, ts) => *)
(*         merge (MkHeap (rev c)) ts *)
(*     end) *)
(*   (g := hp) (*TODO*) *)
(*   (xM := removeMinTree hp) *)
(*   _ (fun x => _)).  *)
(*   - refine TODO. *)
(*   - refine TODO. (*TODO*) *)
(* Defined.*) *)
(* *) *)
