From Coq Require Import List Arith Psatz.

From Clairvoyance Require Import
  Core Approx List ListA Prod Tick.

Import ListNotations.
Import Tick.Notations.

(* Now, what if we did the same but with mergesort *)

(* MergeSort and its attendent functions as given by Software Foundations *) 

Fixpoint split {X:Type} (l:list X) : (list X * list X) :=
  match l with
  | [] => ([],[])
  | [x] => ([x],[])
  | x1 :: x2 :: l' =>
    let (l1,l2) := split l' in
    (x1 :: l1, x2 :: l2)
  end.

Fixpoint merge l1 l2 n :=
  match l1, l2, n with
  | _, _, 0 => []
  | [], _, _ => l2
  | _, [], _ => l1
  | a1::l1', a2::l2', S n =>
      if a1 <=? a2 then a1 :: merge l1' l2 n else a2 :: merge l1 l2' n
  end.

(* We swapped this to use fuel instead of well-founded induction *)
Fixpoint mergesort' (l: list nat) (n : nat) : list nat :=
  match n, l with
  | 0, _ => [] (* Ran out of fuel *)
  | _, [] => []
  | _, [x] => [x]
  | S n, _ => let (l1,l2) := split l in 
              merge (mergesort' l1 n) (mergesort' l2 n) (length l)
  end.

Definition mergesort (l : list nat) : list nat :=
  mergesort' l (length l).

(* Demand functions for split/merge/mergesort *)

Definition thunkTupleD {a b} `{Bottom b} (f : a * a -> b) (x : T a * T a) (p : a) : b :=
  match x with
  | (Thunk x1, Thunk x2) => f (x1, x2)
  | (Thunk x1, Undefined) => f (x1, p)
  | (Undefined, Thunk x2) => f (p, x2)
  | (Undefined, Undefined) => bottom
  end.

Fixpoint splitD {a : Type} (xs : list a)
  (outD : prodA (listA a) (listA a)) :
  Tick (T (listA a)) :=
  Tick.tick >>
  match xs, outD with
  | [], _ => Tick.ret (Thunk NilA)
  | [x], _ => Tick.ret (Thunk (ConsA (Thunk x) (Thunk NilA)))
  | x :: x' :: xs, p =>
    let+ xsD := splitD xs (prodD tailX tailX p) in
    Tick.ret (Thunk (ConsA (Thunk x) (Thunk (ConsA (Thunk x') xsD))))
  end.

(* Compute splitD [1;2;3;4;5;6;7;8] (pairA (exact [1;3;5;7]) (exact [2;4;6;8])). *)

Fixpoint mergeD (xs ys : list nat) (n : nat)
  (outD : listA nat) : Tick (T (listA nat) * T (listA nat)) :=
  Tick.tick >>
  match xs, ys, n, outD with
  | _,  _, 0, _ => Tick.ret (Undefined, Undefined) 
  | [], _, _, _ => Tick.ret (Thunk NilA, Undefined)
  | _, [], _, _ => Tick.ret (Undefined, Thunk NilA)
  | x' :: xs', y' :: ys', S n', ConsA zD zsD =>
      if x' <=? y' then
        let+ (xsD, ysD) := thunkD (mergeD xs' ys n') zsD in
        Tick.ret (Thunk (ConsA (Thunk x') xsD), ysD)
      else 
        let+ (xsD, ysD) := thunkD (mergeD xs ys' n') zsD in
        Tick.ret (xsD, Thunk (ConsA (Thunk y') ysD))
  | _, _, _, _ => bottom
  end.

(* Compute mergeD [1;3;5] [2;4;6] 3 (ConsA (Thunk 1) (Thunk (ConsA (Thunk 2) (Thunk (ConsA (Thunk 3) Undefined))))). *)

Fixpoint mergesort'D (l : list nat) (n : nat) (outD : listA nat) : Tick (T (listA nat)) :=
  Tick.tick >>
  match n, l with
  | 0, _ => Tick.ret Undefined
  | _, [] => Tick.ret (Thunk NilA)
  | _, [x] => Tick.ret (Thunk (ConsA (Thunk x) (Thunk NilA)))
  | S n, _ =>
    let (xs, ys) := split l in
    let xs' := mergesort' xs n in
    let ys' := mergesort' ys n in
    let+ (mxsD, mysD) := mergeD xs' ys' (length l) outD in
    let+ xsD := thunkD (mergesort'D xs n) mxsD in
    let+ ysD := thunkD (mergesort'D ys n) mysD in
    let+ lD := splitD l (pairA xsD ysD) in
    Tick.ret lD
  end.

Definition merge_sortD (l : list nat) (outD : listA nat) : Tick (T (listA nat)) :=
  mergesort'D l (length l) outD.

  Lemma split_ind {A} :
  forall (P : list A -> Prop),
    P [] ->
    (forall x, P [x]) ->
    (forall x1 x2 xs, P xs -> P (x1 :: x2 :: xs)) ->
    forall xs, P xs.
Proof.
  intros. apply induction_ltof1 with (f := @length A). intros.
  rename x into ys. destruct ys.
  - apply H.
  - destruct ys.
    + apply H0.
    + enough (length ys < length (a :: a0 :: ys)).
      * apply H1. apply H2. apply H3.
      * destruct ys; simpl; auto.
Qed.

Lemma splitD__approx (x : nat) (xs : list nat) (outD : _)
  : outD `is_approx` split xs ->
    Tick.val (splitD xs outD) `is_approx` xs.
Proof.
  revert x outD.
  apply split_ind with (xs:=xs); intros;
    try solve [solve_approx]. 
  simpl in H0. specialize (H x).
  destruct (split xs0) eqn:Hsplit.
  simpl. destruct outD; simpl.
  unfold exact, Exact_prodA in H0. inversion H0.
  autorewrite with exact in H1.
  autorewrite with exact in H2.
  inversion H1; inversion H2; subst.
  - simpl. solve_approx.
    apply H. solve_approx.
  - simpl. destruct x3; solve_approx.
    + apply H. solve_approx.
    + apply H. solve_approx.
      inversion H7; subst. assumption.
  - simpl. destruct x0; solve_approx.
    + apply H. solve_approx.
    + apply H. solve_approx.
      inversion H5; subst. assumption.
  - simpl. destruct x0; destruct x3; solve_approx;
      try (apply H; solve_approx).
    + inversion H8; assumption.
    + inversion H5; assumption.
    + inversion H5; assumption.
    + inversion H8; assumption.
Qed.

Ltac destruct_lia :=
  match goal with
  | [ |- context[match ?x with |_ => _ end] ] =>
      let H := fresh "Hdes" in
       destruct x eqn:H; simpl; try lia
  end.

Lemma splitD_cost (x : nat) (xs : list nat) outD ys zs :
  pairA ys zs = outD ->
  Tick.cost (splitD xs outD) <= max 1 (max (sizeX 1 ys) (sizeX 1 zs)). 
Proof.
  revert x outD ys zs.
  apply split_ind with (xs:=xs); intros.
  - simpl. repeat destruct_lia.
  - simpl. repeat destruct_lia.
  - simpl. repeat destruct_lia.
    + rewrite <- H0. simpl.
      specialize (H x (pairA (tailX ys) (tailX zs)) _ _ eq_refl).
      admit. (* Should be provable with H and Hdes. *)
    + rewrite <- H0. simpl.
      specialize (H x (pairA (tailX ys) (tailX zs)) _ _ eq_refl).
      admit. (* Might need some extra lemmas here. *)
Admitted.
