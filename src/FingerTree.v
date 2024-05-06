From Coq Require Import List Arith Lia RelationClasses.
From Clairvoyance Require Import Core Approx ApproxM List Misc BankersQueue.

Import ListNotations.

From Hammer Require Import Tactics Hammer.

Set Primitive Projections.
Set Implicit Arguments.
Set Contextual Implicit.
Set Maximal Implicit Insertion.

Tactic Notation "invert_clear" hyp(H) "as" simple_intropattern(pat) :=
  let HI := fresh "HI" in
  pose I as HI;
  inversion H as pat;
  repeat lazymatch goal with
    | _ : ?type |- _ => match type with
                        | ?x = ?y => subst x + subst y
                        end
    end;
  clear HI;
  clear H.

Tactic Notation "invert_clear" hyp(H) :=
  invert_clear H as [ ].

Tactic Notation "invert_clear" integer(n) "as" simple_intropattern(pat) :=
  progress (intros until n);
  match goal with
  | H : _ |- _ => invert_clear H as pat
  end.

Tactic Notation "invert_clear" integer(n) :=
  progress (intros until n);
  match goal with
  | H : _ |- _ => invert_clear H as [ ]
  end.

#[local] Existing Instance Exact_id.
#[local] Existing Instance LessDefined_id.
#[local] Existing Instance PreOrder_LessDefined_id.
#[local] Existing Instance ExactMaximal_id.
#[local] Existing Instance Lub_id.
#[local] Existing Instance LubLaw_id.
#[local] Existing Instance Exact_T.
#[local] Existing Instance LessDefined_T.
#[local] Existing Instance PreOrder_LessDefined_id.
#[local] Existing Instance ExactMaximal_T.
#[local] Existing Instance Lub_T.
#[local] Existing Instance LubLaw_T.

#[local] Instance Reflexive_LessDefined_T (a : Type) `{LDA : LessDefined a, !Reflexive LDA} :
  Reflexive (@LessDefined_T a _).
Proof.
  unfold Reflexive. destruct x.
  - constructor. reflexivity.
  - constructor.
Qed.
#[local] Hint Resolve Reflexive_LessDefined_T : core.

#[local] Instance Transitive_LessDefined_T (a : Type) `{LDA : LessDefined a, !Transitive LDA} :
  Transitive (@LessDefined_T a _).
Proof.
  unfold Transitive. invert_clear 1. { fcrush. } invert_clear 1. constructor.
  etransitivity; eauto.
Qed.
#[local] Hint Resolve Transitive_LessDefined_T : core.

Variant Crowd (a : Type) : Type :=
  | One (x : a) : Crowd a
  | Two (x y : a) : Crowd a
  | Three (x y z : a) : Crowd a.

Variant CrowdA (a : Type) : Type :=
  | OneA (xD : T a) : CrowdA a
  | TwoA (xD yD : T a) : CrowdA a
  | ThreeA (xD yD zD : T a) : CrowdA a.

Variant LessDefined_CrowdA (a : Type) : LessDefined (CrowdA a) :=
  | LessDefined_OneA (xD xD' : T a) :
    xD `less_defined` xD' ->
    LessDefined_CrowdA (OneA xD) (OneA xD')
  | LessDefined_TwoA (xD yD xD' yD' : T a) :
    xD `less_defined` xD' ->
    yD `less_defined` yD' ->
    LessDefined_CrowdA (TwoA xD yD) (TwoA xD' yD')
  | LessDefined_ThreeA (xD yD zD xD' yD' zD' : T a) :
    xD `less_defined` xD' ->
    yD `less_defined` yD' ->
    zD `less_defined` zD' ->
    LessDefined_CrowdA (ThreeA xD yD zD) (ThreeA xD' yD' zD').
#[local] Hint Constructors LessDefined_CrowdA : core.
#[local] Existing Instance LessDefined_CrowdA.

#[local] Instance Reflexive_LessDefined_CrowdA (a : Type) :
  Reflexive (LessDefined_CrowdA (a := a)).
Proof.
  unfold Reflexive. destruct x; auto with *.
Qed.
#[local] Hint Resolve Reflexive_LessDefined_CrowdA : core.

#[local] Instance Transitive_LessDefined_CrowdA (a : Type) :
  Transitive (LessDefined_CrowdA (a := a)).
Proof.
  unfold Transitive. invert_clear 1; fcrush.
Qed.
#[local] Hint Resolve Transitive_LessDefined_CrowdA : core.

#[local] Instance Preorder_LessDefined_CrowdA (a : Type) :
  PreOrder (LessDefined_CrowdA (a := a)).
Proof.
  split; auto.
Qed.

#[local] Instance Exact_Crowd (a b : Type) `{Exact a b} : Exact (Crowd a) (CrowdA b) :=
  fun c => match c with
        | One x => OneA (exact x)
        | Two x y => TwoA (exact x) (exact y)
        | Three x y z => ThreeA (exact x) (exact y) (exact z)
        end.

#[local] Instance ExactMaximal_Crowd (a b : Type) {_ : Exact a b} {_ : ExactMaximal b a} :
  ExactMaximal (CrowdA b) (Crowd a).
Proof.
  unfold ExactMaximal. destruct x; sauto.
Qed.

#[local] Instance Lub_CrowdA (a : Type) : Lub (CrowdA a) :=
  fun cA cA' => match cA, cA' with
             | OneA x, OneA x' => OneA (lub x x')
             | TwoA x y, TwoA x' y' => TwoA (lub x x') (lub y y')
             | ThreeA x y z, ThreeA x' y' z' => ThreeA (lub x x') (lub y y') (lub z z')
             | _, _ => OneA bottom
             end.

#[local] Instance LubLaw_CrowdA (a : Type) : LubLaw (CrowdA a).
Proof.
  split.
  - do 2 inversion 1; fcrush.
  - destruct x; fcrush.
  - destruct y; fcrush.
Qed.

#[local] Instance BottomOf_CrowdA (a : Type) : BottomOf (CrowdA a) :=
  fun u => match u with
        | OneA _ => OneA bottom
        | TwoA _ _ => TwoA bottom bottom
        | ThreeA _ _ _ => ThreeA bottom bottom bottom
        end.

Variant Tuple (a : Type) : Type :=
  | Pair (x y : a) : Tuple a
  | Triple (x y z : a) : Tuple a.

Variant TupleA (a : Type) : Type :=
  | PairA (xD yD : T a) : TupleA a
  | TripleA (xD yD zD : T a) : TupleA a.

Variant LessDefined_TupleA (a : Type) : LessDefined (TupleA a) :=
  | LessDefined_Pair (xD yD xD' yD' : T a) :
    xD `less_defined` xD' ->
    yD `less_defined` yD' ->
    LessDefined_TupleA (PairA xD yD) (PairA xD' yD')
  | LessDefined_TripleA (xD yD zD xD' yD' zD' : T a) :
    xD `less_defined` xD' ->
    yD `less_defined` yD' ->
    zD `less_defined` zD' ->
    LessDefined_TupleA (TripleA xD yD zD) (TripleA xD' yD' zD').
#[local] Hint Constructors LessDefined_TupleA : core.
#[local] Existing Instance LessDefined_TupleA.

#[local] Instance Reflexive_LessDefined_TupleA (a : Type) :
  Reflexive (LessDefined_TupleA (a := a)).
Proof.
  sauto unfold:Reflexive.
Qed.
#[local] Hint Resolve Reflexive_LessDefined_TupleA : core.

#[local] Instance Transitive_LessDefined_TupleA (a : Type) :
  Transitive (LessDefined_TupleA (a := a)).
Proof.
  unfold Transitive. invert_clear 1; fcrush.
Qed.
#[local] Hint Resolve Transitive_LessDefined_TupleA : core.

#[local] Instance Preorder_LessDefined_TupleA (a : Type) :
  PreOrder (LessDefined_TupleA (a := a)).
Proof.
  split; auto.
Qed.

#[local] Instance Exact_Tuple (a b : Type) `{Exact a b} : Exact (Tuple a) (TupleA b) :=
  fun t => match t with
        | Pair x y => PairA (exact x) (exact y)
        | Triple x y z => TripleA (exact x) (exact y) (exact z)
        end.

#[local] Instance ExactMaximal_Tuple (a b : Type) {_ : Exact a b} {_ : ExactMaximal b a} :
  ExactMaximal (TupleA b) (Tuple a).
Proof.
  unfold ExactMaximal. destruct x; sauto.
Qed.

#[local] Instance Lub_TupleA (a : Type) : Lub (TupleA a) :=
  fun t t' =>
    match t, t' with
    | PairA xD yD, PairA xD' yD' => PairA (lub xD xD') (lub yD yD')
    | TripleA xD yD zD, TripleA xD' yD' zD' => TripleA (lub xD xD') (lub yD yD') (lub zD zD')
    | _, _ => PairA bottom bottom
    end.

#[local] Instance LubLaw_TupleA (a : Type) : LubLaw (TupleA a).
Proof.
  split.
  - do 2 inversion 1; fcrush.
  - destruct x; fcrush.
  - destruct y; fcrush.
Qed.

#[local] Instance BottomOf_TupleA (a : Type) : BottomOf (TupleA a) :=
  fun t => match t with
        | PairA _ _ => PairA bottom bottom
        | TripleA _ _ _ => TripleA bottom bottom bottom
        end.

Inductive Seq (a : Type) : Type :=
| Nil : Seq a
| Unit (x : a) : Seq a
| More (f : Crowd a) (m : Seq (Tuple a)) (r : Crowd a) : Seq a.

Unset Elimination Schemes.

Inductive SeqA (a : Type) : Type :=
| NilA : SeqA a
| UnitA (xD : T a) : SeqA a
(* When the moon hits your eye like a big pizza pie, that's a *)
| MoreA (fD : T (CrowdA a)) (mD : T (SeqA (TupleA a))) (rD : T (CrowdA a)) : SeqA a.

Lemma SeqA_ind (P : forall (a : Type), SeqA a -> Prop) :
  (forall a, P a NilA) ->
  (forall a xD, P a (UnitA xD)) ->
  (forall a fD mD rD (IHmD : TR1 (P _) mD), P a (MoreA fD mD rD)) ->
  forall a sA, P a sA.
Proof.
  intros HNilA HUnitA HMoreA. fix SELF 2. destruct sA.
  - apply HNilA.
  - apply HUnitA.
  - apply HMoreA. destruct mD; constructor. apply SELF.
Qed.

Set Elimination Schemes.

Inductive LessDefined_SeqA {a : Type} : LessDefined (SeqA a) :=
  | LessDefined_NilA :
    NilA `less_defined` NilA
  | LessDefined_UnitA xD xD' :
    xD `less_defined` xD' ->
    LessDefined_SeqA (UnitA xD) (UnitA xD')
  | LessDefined_MoreA fD mD rD fD' mD' rD' :
    fD `less_defined` fD' ->
    @LessDefined_T _ LessDefined_SeqA mD mD' ->
    rD `less_defined` rD' ->
    LessDefined_SeqA (MoreA fD mD rD) (MoreA fD' mD' rD').
#[local] Hint Constructors LessDefined_SeqA : core.
#[local] Existing Instance LessDefined_SeqA.

#[local] Instance Reflexive_LessDefined_SeqA (a : Type) :
  Reflexive (LessDefined_SeqA (a := a)).
Proof.
  unfold Reflexive. induction x. 1, 2: fcrush.
    constructor. 1, 3: auto with *.
    invert_clear IHmD; constructor; auto.
Qed.
#[local] Hint Resolve Reflexive_LessDefined_SeqA : core.

#[local] Instance Transitive_LessDefined_SeqA (a : Type) :
  Transitive (LessDefined_SeqA (a := a)).
Proof.
  unfold Transitive. induction z; repeat invert_clear 1; constructor.
  1, 2, 4: etransitivity; eauto.
  invert_clear IHmD.
  - invert_clear H1; fcrush.
  - sauto.
Qed.
#[local] Hint Resolve Transitive_LessDefined_SeqA : core.

#[local] Instance Preorder_LessDefined_SeqA (a : Type) :
  PreOrder (LessDefined_SeqA (a := a)).
Proof.
  split; auto.
Qed.

Definition Exact_Seq : forall (a b : Type) `{Exact a b}, Exact (Seq a) (SeqA b) :=
  fix Exact_Seq {a b} `{_} s :=
    match s with
    | Nil => NilA
    | Unit x => UnitA (exact x)
    | More f m r => MoreA (exact f) (@Exact_T _ _ Exact_Seq m) (exact r)
    end.
#[local] Existing Instance Exact_Seq.

#[local] Instance ExactMaximal_Seq : forall (a b : Type) `{Exact a b} {_ : ExactMaximal b a},
    ExactMaximal (SeqA b) (Seq a).
Proof.
  unfold ExactMaximal. intros a b HExact HExactMaximal x. revert dependent a.
  induction x. 1, 2: inversion 2; sauto.
  intros b HExact HExactMaximal s Hs.
  destruct s as [ | | f m r ]; inversion_clear Hs as [ | | ? ? ? ? ? ? Hf Hm Hr ].
  fcrush unfold:exact,Exact_T.
Qed.

#[local] Instance Lub_SeqA : forall (a : Type), Lub (SeqA a) :=
  fix Lub_SeqA {a} u u' :=
    match u, u' with
    | UnitA x, UnitA x' => UnitA (lub x x')
    | MoreA f m r, MoreA f' m' r' => MoreA (lub f f') (@Lub_T _ Lub_SeqA m m') (lub r r')
    | _, _ => NilA
    end.

#[local] Instance LubLaw_SeqA (a : Type) : LubLaw (SeqA a).
Proof.
  split.
  - induction z. 1, 2: fcrush.
    invert_clear 1 as [ | | fD' mD' rD' ? ? ? HfD' HmD' HrD' ].
    invert_clear 1 as [ | | fD'' mD'' rD'' ? ? ? HfD'' HmD'' HrD'' ].
    constructor. 1, 3: apply lub_least_upper_bound; auto.
    invert_clear IHmD as [ mA IHmA | ].
    + invert_clear HmD'; invert_clear HmD''; sauto.
    + sauto.
  - induction x. 1, 2: fcrush.
    intro s'. destruct 1 as [ s'' [ Hs Hs' ] ].
    invert_clear Hs as [ | | ? ? ? fD'' mD'' rD'' HfD HmD HrD ].
    invert_clear Hs' as [ | | fD' mD' rD' ? ? ? HfD' HmD' HrD' ].
    constructor. 1, 3: apply lub_upper_bound_l; eauto.
    invert_clear IHmD as [ mA IHmA | ]; [ | constructor ].
    invert_clear HmD'.
    + reflexivity.
    + invert_clear HmD. constructor. apply IHmA. eauto.
  - intro s. induction y as [ | | ? fD' mD' rD' IHmD' ]. 1, 2: fcrush.
    destruct 1 as [ s'' [ Hs Hs' ] ].
    invert_clear Hs' as [ | | ? ? ? fD'' mD'' rD'' HfD' HmD' HrD' ].
    invert_clear Hs as [ | | fD mD rD ? ? ? HfD HmD HrD ].
    constructor. 1, 3: apply lub_upper_bound_r; eauto.
    invert_clear IHmD' as [ mA' IHmA' | ]; [ | constructor ].
    invert_clear HmD.
    + reflexivity.
    + invert_clear HmD'. constructor. apply IHmA'. eauto.
Qed.

#[local] Instance BottomOf_SeqA (a : Type) : BottomOf (SeqA a) :=
  fun u => match u with
        | NilA => NilA
        | UnitA _ => UnitA bottom
        | MoreA _ _ _ => MoreA bottom bottom bottom
        end.

Definition Crowd_toList {a:Type} (c : Crowd a) : list a :=
  match c with
  | (One x) => [x]
  | (Two x y) => [x; y]
  | (Three x y z) => [x;y;z]
  end.

Fixpoint cons {a : Type} (x : a) (s : Seq a) : Seq a :=
  match s with
  | Nil => Unit x
  | Unit y => More (One x) Nil (One y)
  | (More (One y) q u) => More (Two x y) q u
  | (More (Two y z) q u) => More (Three x y z) q u
  | (More (Three y z w) q u) => More (Two x y) (cons (Pair z w) q) u
  end.

Fixpoint consA' (a : Type) (x : T a) (s : SeqA a) : M (SeqA a) :=
  match s with
  | NilA => ret (UnitA x)
  | UnitA y =>
      let~ f' := ret (OneA x) in
      let~ q' := ret NilA in
      let~ r' := ret (OneA y) in
      ret (MoreA f' q' r')
  | MoreA f q u =>
      let! f := force f in
      match f with
      | OneA y =>
          let~ f' := ret (TwoA x y) in
          ret (MoreA f' q u)
      | TwoA y z =>
          let~ f' := ret (ThreeA x y z) in
          ret (MoreA f' q u)
      | ThreeA y z w =>
          let~ f' := ret (TwoA x y) in
          let~ p := ret (PairA z w) in
          let~ q' := forcing q (consA' p) in
          ret (MoreA f' q' u)
      end
  end.

Definition consA (a : Type) (x : T a) (s : T (SeqA a)) : M (SeqA a) :=
  forcing s (consA' x).

Fixpoint snoc {a: Type} (s: Seq a) (x:a) : Seq a := 
 match s with
   | Nil => Unit x
   | (Unit y) => More (One y) Nil (One x)
   | (More u q (One y)) => More u q (Two y x)
   | (More u q (Two y z)) => More u q (Three y z x)
   | (More u q (Three y z w)) =>
   More u (snoc q (Pair y z)) (Two w x)
end.

Definition head {a:Type} (t: Seq a) : option a :=
  match t with
  | Nil => None
  | (Unit x) => Some x
  | (More (One x) _ _ ) => Some x
  | (More (Two x _) _ _) => Some x
  | (More (Three x _ _) _ _) => Some x
  end.

Definition map1 {a:Type} (f : a -> a) (s : Seq a) : Seq a :=
  match s with
  | Nil => Nil
  | (Unit x) => Unit (f x)
  | (More (One x) q u) => More (One (f x)) q u
  | (More (Two x y) q u) => More (Two (f x) y) q u
  | (More (Three x y z) q u) => More (Three (f x) y z) q u
  end.

Definition tail_ {a} more0 (t: Seq a) : Seq a :=
  match t with
  | Nil => Nil
  | Unit x => Nil
  | More (One _) q u => more0 q u
  | More (Two x y) q u => More (One y) q u
  | More (Three x y z) q u => More (Two y z) q u
  end.

Definition chop {a:Type} ( x: Tuple a) : Tuple a :=
  match x with
  | Triple _ y z => Pair y z
  | _ => x
  end.

Fixpoint more0 {a:Type} (q: Seq (Tuple a)) (u: Crowd a) : Seq a :=
  match (q,u) with
  | (Nil, (One y)) => Unit y
  | (Nil, (Two y z)) => More (One y) Nil (One z)
  | (Nil, (Three y z w)) => More (One y) Nil (Two z w)
  | (Unit (Pair x y), _)
  | (More (One (Pair x y)) _ _, _)
  | (More (Two (Pair x y) _) _ _, _)
  | (More (Three (Pair x y) _ _) _ _, _) => More (Two x y) (tail_ more0 q) u
  | (Unit (Triple x _ _), _)
  | (More (One (Triple x _ _)) _ _, _)
  | (More (Two (Triple x _ _) _) _ _, _)
  | (More (Three (Triple x _ _) _ _) _ _, _) => More (One x) (map1 chop q) u
  end.

Definition tail {a:Type} : Seq a -> Seq a := tail_ more0.

Fixpoint toTuples {a:Type} (la : list a) : list (Tuple a) := 
  match la with
    | [] => []
    | [x] => [] (* extra *)
    | [x ; y] => [Pair x y]
    | [x ; y; z; w] => [Pair x y; Pair z w]
    | (x :: y :: z :: xs) => Triple x y z :: toTuples xs
  end.

Fixpoint glue {a:Type} (q1 : Seq a) (la: list a) (q2: Seq a) : Seq a :=
  match (q1,q2) with
  | (Nil,_) => List.fold_right cons q2 la
  | (_,Nil) => List.fold_left snoc la q1
  | (Unit x, _) => List.fold_right cons q2 (x :: la)
  | (_, Unit y) => List.fold_left snoc (la ++ [y]) q1
  | (More u1 q1 v1, More u2 q2 v2) =>
      More u1 (glue q1 (toTuples (Crowd_toList v1 ++ la ++ Crowd_toList u2)) q2) v2
  end.

Definition append {a:Type} (q1 : Seq a) (q2 : Seq a) : Seq a :=
    glue q1 nil q2.

Fixpoint fromTuples {a:Type} (lta : list (Tuple a)) : list a :=
  match lta with
  | [] => []
  | (Pair x y :: xs) => [x; y] ++ fromTuples xs  (* extra *)
  | (Triple x y z :: xs) => [x; y; z] ++ fromTuples xs
  end.

Fixpoint Seq_toList {a:Type} (q : Seq a) : list a :=
  match q with
  | Nil => []
  | Unit x => (x :: [])
  | More r q l =>
      Crowd_toList r ++ fromTuples (Seq_toList q) ++ Crowd_toList l
  end.

Lemma nil_spec : forall {a:Type}, Seq_toList (@Nil a) = [].
Proof.
  intros. simpl. auto. Qed.

Lemma cons_spec : forall {a:Type} (x:a)(q: Seq a), Seq_toList (cons x q) = x :: Seq_toList q.
Proof.
  intros.
  induction q; simpl; auto.
  destruct c; simpl.
  + f_equal.
  + f_equal.
  + f_equal.
    f_equal.
    repeat rewrite app_comm_cons.
    f_equal.
    rewrite IHq.
    simpl.
    destruct (Seq_toList q); auto.
Qed.

Lemma fromTuples_app {a} (xs ys : list (Tuple a))
  : fromTuples (xs ++ ys) = fromTuples xs ++ fromTuples ys.
Proof.
  induction xs as [ | [] xs IH]; cbn [fromTuples app]; [ reflexivity | | ].
  - rewrite IH; reflexivity.
  - rewrite IH; reflexivity.
Qed.

Lemma fromTuples_toTuples' {a} (n : nat) : forall (xs : list a),
  2 <= length xs -> length xs <= n -> fromTuples (toTuples xs) = xs.
Proof.
  induction n as [ | n IH ]; intros [ | x xs ] H2 Hn; cbn; try reflexivity.
  - inversion Hn.
  - destruct xs as [ | x1 xs]; [ cbn in H2; lia |].
    destruct xs as [ | x2 [ | x3 [ | x4 xs ] ] ]; cbn; try reflexivity.
    repeat f_equal. apply (IH (x3 :: x4 :: xs)); cbn in *; lia.
Qed.


Lemma fromTuples_toTuples {a} (xs : list a) : 2 <= length xs -> fromTuples (toTuples xs) = xs.
Proof.
  intros; eapply fromTuples_toTuples'; [ auto | reflexivity ].
Qed.

Lemma snoc_spec : forall {a:Type} (x:a)(q: Seq a), Seq_toList (snoc q x) = Seq_toList q ++ [x].
Proof.
  intros a x q; revert x; induction q as [ | | ? ? ? IH ]; cbn; intros; try reflexivity.
  destruct c0; cbn.
  - rewrite <- !app_assoc; cbn; reflexivity.
  - rewrite <- !app_assoc; cbn; reflexivity.
  - rewrite <- !app_assoc; cbn. rewrite IH; cbn.
    rewrite fromTuples_app; cbn. rewrite <- !app_assoc. reflexivity.
Qed.

Lemma more0_spec : forall {a} (q: Seq (Tuple a)) c0, Seq_toList (more0 q c0) = fromTuples (Seq_toList q) ++ Crowd_toList c0.
Proof.
  fix SELF 2. intros ? [ | | ] u; intros; cbn.
  - destruct u; cbn; reflexivity.
  - destruct t; cbn; reflexivity.
  - destruct c; cbn.
    + destruct t; cbn. { rewrite SELF. reflexivity. } { reflexivity. }
    + destruct t; cbn; reflexivity.
    + destruct t; reflexivity.
Qed.

Lemma tail_spec : forall {a:Type} (q: Seq a), Seq_toList (tail q) = tl (Seq_toList q).
Proof.
  intros ? [ | | [] ? ? ]; cbn; auto using more0_spec.
Qed.

Lemma foldr_cons_spec {a} {q : Seq a} xs : Seq_toList (fold_right cons q xs) = xs ++ Seq_toList q.
Proof.
  induction xs as [ | ? ? IH]; cbn; auto. rewrite cons_spec, IH. reflexivity.
Qed.

Lemma foldl_snoc_spec {a} {q : Seq a} xs : Seq_toList (fold_left snoc xs q) = Seq_toList q ++ xs.
Proof.
  revert q; induction xs as [ | ? ? IH]; cbn; intros.
  - rewrite app_nil_r; auto.
  - rewrite IH. rewrite snoc_spec. rewrite <- app_assoc; reflexivity.
Qed.

Lemma glue_spec {a} (q : Seq a) (la : list a) q' : Seq_toList (glue q la q') = Seq_toList q ++ la ++ Seq_toList q'.
Proof.
  revert la q'. induction q; cbn.
  - intros; apply foldr_cons_spec.
  - destruct q'; cbn.
    + rewrite app_nil_r, foldl_snoc_spec; reflexivity.
    + rewrite cons_spec, foldr_cons_spec. reflexivity.
    + rewrite cons_spec, foldr_cons_spec; reflexivity.
  - destruct q'; cbn.
    + rewrite foldl_snoc_spec, app_nil_r. reflexivity.
    + rewrite foldl_snoc_spec. reflexivity.
    + rewrite IHq, !fromTuples_app, fromTuples_toTuples.
      2:{ destruct c0; cbn; [ | lia .. ].
          destruct c1; cbn; rewrite app_length; cbn; lia. }
      rewrite <- !app_assoc. reflexivity.
Qed.

Lemma append_spec {a} (q q' : Seq a) : Seq_toList (append q q') = Seq_toList q ++ Seq_toList q'.
Proof.
  apply (glue_spec _ []).
Qed.

Lemma map1_spec : forall a (f: a -> a) x (q: Seq a), 
    map1 f (cons x q) = cons (f x) q.
Proof.
  intros.
  destruct q; simpl; auto.
  destruct c; simpl; auto.
Qed.

(** Utils *)

Fixpoint depth {a} (t: Seq a) : nat :=
  match t with
  | More _ t _ => 1 + depth t
  | _ => 0
  end.
