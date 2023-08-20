
From Coq Require Import Arith List Psatz Morphisms Relations.
From Equations Require Import Equations.

From Clairvoyance Require Import Core Approx ApproxM Tick Misc ListA.

#[local] Existing Instance Exact_id | 1.
#[local] Existing Instance LessDefined_id | 100.
#[local] Existing Instance PreOrder_LessDefined_id | 100.
#[local] Existing Instance ExactMaximal_id | 100.

Set Primitive Projections.
Set Implicit Arguments.
Set Maximal Implicit Insertion.
Set Contextual Implicit.

Import ListNotations.
Import Tick.Notations.

Global Instance Proper_S_le : Proper (le ==> le) S.
Proof.
  unfold Proper, respectful. lia.
Qed.

(* ---------------------- List operations ---------------------- *)

Fixpoint append {a} (xs ys : list a) : list a :=
  match xs with
  | nil => ys
  | cons x xs1 => let zs := append xs1 ys in x :: zs
  end.

(* returns the prefix of xs of length n or xs when n > length xs. *)
Fixpoint take {a} (n : nat) (xs : list a) : list a :=
  match n, xs with
  | O, _ => nil
  | S _, nil => nil
  | S n1, x :: xs1 => let zs := take n1 xs1 in x :: zs
  end.

(* This is rev_append *)
Fixpoint rev_ {a} (xs : list a) (ys : list a) : list a :=
  match xs with 
  | nil => ys
  | x :: xs1 => rev_ xs1 (x :: ys)
  end.

Definition p {a} (n : nat) (xs ys : list a) : list a :=
  let zs := append xs ys in
  take n zs.

Fixpoint drop {a} (n : nat) (xs : list a) : list a :=
  match n, xs with
  | O, _ => xs
  | S _, nil => nil
  | S n1, x :: xs1 => drop n1 xs1
  end.

(* ---------------------- Section 4: Translation ---------------------- *)

(* Definitions needed for the by-hand translation of the examples from Section 2 *)


(** * Figure 9.

    Definition of the [foldrA] function used in the translation of [foldr]. *)
Fixpoint foldrA' {a b} (n : M b) (c : T a -> T b -> M b) (x' : listA a) : M b :=
  tick >>
  match x' with
  | NilA => n
  | ConsA x1 x2 =>
    let~ y2 := foldrA' n c $! x2 in
    c x1 y2
  end.

Definition rev {a} (xs : list a) := rev_ xs nil.

Fixpoint foldl {a b} (f : b -> a -> b) (v : b) (xs : list a) : b :=
  match xs with
  | nil => v
  | cons x xs => foldl f (f v x) xs
  end.

Fixpoint foldr {a b} (v : b) (f : a -> b -> b)  (xs : list a) : b :=
  match xs with
  | nil => v
  | cons x xs => f x (foldr v f xs)
  end.


Fixpoint insert (x : nat) (xs : list nat) : list nat :=
  match xs with 
  | y :: ys => if Nat.leb x y then y :: insert x ys else x :: y :: ys
  | nil => x :: nil
  end.

Definition insert_sort (xs : list nat) : list nat :=
  foldr nil insert xs.


(* ---------------------- Approximate versions ---------------------- *)


(** 

    The translated code of append and take from the pure version of Fig. 1. *)
Fixpoint append_ {a : Type} (xs' : listA a) (ys : T (listA a)) : M (listA a) :=
  tick >>
  match xs' with
  | NilA => force ys
  | ConsA x xs1 =>
    let~ t := (fun xs1' => append_ xs1' ys) $! xs1 in
    ret (ConsA x t)
  end.

Definition appendA {a : Type} (xs ys : T (listA a)) : M (listA a) :=
  (fun xs' => append_ xs' ys) $! xs.

Fixpoint take_ {a : Type} (n : nat) (xs' : listA a) : M (listA a) :=
  tick >>
  match n, xs' with
  | O, _ => ret NilA
  | S _, NilA => ret NilA
  | S n1, ConsA x xs1 =>
    let~ t := take_ n1 $! xs1 in
    ret (ConsA x t)
  end.

Definition takeA {a : Type} (n : nat) (xs : T (listA a)) : M (listA a) :=
  take_ n $! xs.

Definition pA {a} (n : nat) (xs ys : T (listA a)) : M (listA a) :=
  tick >>
  let~ t := appendA xs ys in
  takeA n t.


Fixpoint revA_ {a : Type} (xs' : listA a) (ys : T (listA a)) : M (listA a) :=
  tick >>
  match xs' with
  | NilA => force ys
  | ConsA x xs1 =>
    let~ ys1 := ret (ConsA x ys) in
    (fun xs1' => revA_ xs1' ys1) $! xs1
  end.

Definition revA {a : Type} (xs : T (listA a)) : M (listA a) :=
  let~ ys := ret NilA in
  (fun xs' => revA_ xs' ys) $! xs.

Fixpoint insertA_ (x : nat) (xs : listA nat) : M (listA nat) :=
  match xs with 
  | ConsA y ys => 
      tick >>
      forcing y (fun y' =>
      if Nat.leb x y' then 
        tick >>
        forcing ys (fun ys' => 
        let~ t := insertA_ x ys' in
        ret (ConsA y t)) else ret (ConsA (Thunk x) (Thunk (ConsA y ys))))
  | NilA => ret (ConsA (Thunk x) (Thunk NilA))
  end.

Definition insertA (x:T nat) (xs : T(listA nat)) : M (listA nat) :=
  tick >>
  tick >>
  let! x' := force x in
  let! xs' := force xs in 
  insertA_ x' xs'.


Fixpoint foldlA_ {a b} (f : T b -> T a -> M b) (v : T b) (xs : listA a) : M b :=
  tick >>
  match xs with
  | NilA => force v
  | ConsA x xs => let~ t := f v x in
                  foldlA_ f t $! xs
  end.

Definition foldlA {a b} (f : T b -> T a -> M b) (v : T b) (xs : T (listA a)) : M b :=
  foldlA_ f v $! xs.

Fixpoint foldrA_ {a b} (f : T a -> T b -> M b) (v : T b) (xs : listA a) : M b :=
  tick >>
  match xs with
  | NilA => force v
  | ConsA x xs => let~ t := foldrA_ f v $! xs in
                 f x t
  end.

Definition foldrA {a b} (f : T a -> T b -> M b) (v : T b) (xs : T (listA a)) : M b :=
  foldrA_ f v $! xs.

(* ----------------------------------------------------- *)


Definition headX {a} (xs : T (listA a)) : T a :=
  match xs with
  | Thunk (ConsA x _) => x
  | _ => Undefined
  end.


Definition tailX {a} (xs : T (listA a)) : T (listA a) :=
  match xs with
  | Thunk (ConsA _ xs) => xs
  | _ => Undefined
  end.



(* --------------------- demand functions -------------------- *)

(* Demand function for [appendA]. Note that the output demand [outD] is at least
   either [NilA] or [ConsA] (i.e., it forces the result at least to WHNF).
   [thunkD] can then be used to lift the output demand type to thunks.  *)
Fixpoint appendD {a} (xs ys : list a) (outD : listA a) : Tick (T (listA a) * T (listA a)) :=
  Tick.tick >>
  match xs, outD with
  | nil, _ => Tick.ret (Thunk NilA, Thunk outD)
  | x :: xs, ConsA zD zsD =>
    let+ (xsD, ysD) := thunkD (appendD xs ys) zsD in
    Tick.ret (Thunk (ConsA zD xsD), ysD)
  | _, _ => bottom (* Nonsense: if (xs = _ :: _) then append xs ys = (_ :: _)
                      so the demand cannot be of the form [] *)
  end.

Fixpoint lsum (xs : list nat) : nat :=
  match xs with
  | nil => 0
  | x :: xs' => x + lsum xs'
  end.

(* Entire list must be forced *)
Definition lsumD (xs : list nat) (outD : nat) : Tick (T (listA nat)) :=
  Tick.MkTick (1 + length xs) (exact xs).

(* We force the list until n = 0 or we run out of list *)
Fixpoint takeD {a} (n : nat) (xs : list a) (outD : listA a) : Tick (T (listA a)) :=
  Tick.tick >>
  match n, xs, outD with
  | 0, _, _ => Tick.ret (Undefined)
  | _, nil, _ => Tick.ret (Thunk NilA)
  | S m, y :: ys, ConsA zD zsD =>
    let+ ysD := thunkD (takeD m ys) zsD in
    Tick.ret (Thunk (ConsA (Thunk y) ysD))
  | _, _, _ => bottom (* does not occur *)
  end.

Definition sumOfTakeD (n : nat) (xs : list nat) (outD : nat) : Tick (T (listA nat)) :=
  let+ take_xsD := lsumD (take n xs) outD in  
  let+ xsD := thunkD (takeD n xs) take_xsD in
  Tick.ret xsD.

Lemma lsumD_cost (xs : list nat) outD :
  Tick.cost (lsumD xs outD) = 1 + length xs.
Proof.
  reflexivity. Qed.

Lemma takeD_cost (n : nat) (xs : list nat) outD :
  Tick.cost (takeD n xs outD) <= 1 + n.
Proof.
  (* The proof follows the structure of [takeD]. It is a match on three variables [n, xs, outD],
     which is sugar for nested matches each on one variable:
<<
    match n with
    | O => Tick.ret ...
    | S m => match xs with
             | nil => ...
             | y :: ys => match outD with ...
>>
     This nesting is reflected in the proof below, each [match] corresponding to [induction]
     or [destruct]. (The first match works with the [Fixpoint] to ensure termination, which
     is a hint that [induction] should be used instead of [destruct].) *)
  (* All 3 arguments of takeD change in the recursive call, so we should
     generalize the induction hypothesis with [revert xs outD]
     so we can then specialize it with different arguments (in [rewrite Ihn]). *)
  revert xs outD; induction n; intros xs outD; simpl.
  - reflexivity.
  - destruct xs; simpl.
    + lia.
    + destruct outD.
      * simpl. lia.
      * destruct x2; simpl.
        -- rewrite IHn. lia.
        -- lia.
Qed.

Lemma length_take_Sn_leq_1Sn (n n0 : nat) (xs : list nat) :
  length (take n (n0 :: xs)) <= S n -> length (take (S n) (n0 :: xs)) <= 1 + S n.
Proof.
  revert xs n0.
  induction n.
  - simpl. lia.
  - simpl. destruct xs.
    + simpl. lia.
    + simpl. intros. simpl in IHn. apply le_n_S.
      eapply IHn. apply le_S_n. apply H.
Qed.

Lemma length_take_n_leq_n (n : nat) (xs : list nat) : 
  length (take n xs) <= 1 + n.
Proof.
  induction n.
  - simpl. lia.
  - destruct xs.
    + simpl. lia.
    + simpl in IHn.
      rewrite length_take_Sn_leq_1Sn.
      * lia.
      * apply IHn.
Qed.

Lemma sum_of_take_cost (n : nat) (xs : list nat) outD
  : outD `is_approx` (lsum (take n xs)) ->
    forall xsA, xsA = Tick.val (sumOfTakeD n xs outD) ->
    Tick.cost (sumOfTakeD n xs outD) <= (2 * n) + 3.
Proof.
  intros. rewrite H. simpl.
  destruct n.
  - destruct xs; simpl; lia.
  - destruct xs.
    + simpl. lia.
    + simpl.
      rewrite length_take_n_leq_n.
      rewrite takeD_cost.
      lia.
Qed.

(* Select and selsort as given by Software Foundations Chapter 3 *)
Fixpoint select (x: nat) (l: list nat) : nat * list nat :=
  match l with
  | [] => (x, [])
  | h :: t =>
    if x <=? h
    then let (j, l') := select x t in (j, h :: l')
    else let (j, l') := select h t in (j, x :: l')
  end.

Fixpoint selection_sort (l : list nat) (n : nat) : list nat :=
  match l, n with
  | _, 0 => [] (* ran out of fuel *)
  | [], _ => []
  | x :: r, S n' => let (y, r') := select x r in y :: selection_sort r' n'
end.

(* The entire list must be forced to select smallest element *)
Definition selectD (x : nat) (xs : list nat) (outD : listA nat) : Tick (T (listA nat)) :=
  Tick.MkTick (1 + length xs) (exact (x::xs)).

(* The entire list is forced one selection at a time*)
Fixpoint selection_sortD (xs : list nat) (outD : listA nat) : Tick (T (listA nat)) :=
  Tick.tick >>
  match xs, outD with
  | [], _ => Tick.ret (Thunk NilA)
  | x :: xs', ConsA zD zsD =>
    let+ _ := thunkD (selection_sortD xs') zsD in
    let+ xsD := selectD x xs' (exact xs) in
    Tick.ret xsD (* We invariably force the entire input list *)
  | _, _ => bottom
  end.

Lemma sort_produces_element (n : nat) (x : nat) (xs : list nat) :
  selection_sort (x :: xs) (S n) = fst (select x xs) :: selection_sort (snd (select x xs)) n.
Proof.
  simpl. destruct (select x xs). simpl. reflexivity.
Qed.

Definition head_def {a} (xs : list a) (d : a) : a :=
  match xs with
  | [] => d
  | x :: _ => x
  end.

(* We force the empty list or the first element only *)
Definition headD {a} (xs : list a) (d : a) (outD : a) : Tick (T (listA a)) :=
  Tick.tick >>
  match xs with
  | [] => Tick.ret (Thunk NilA)
  | x :: _ => Tick.ret (Thunk (ConsA (Thunk x) (Undefined)))
  end.

Definition head_selection_sortD (xs : list nat) (outD : nat) : Tick (T (listA nat)) :=
  let+ list_headD := headD (selection_sort xs (length xs)) 0 outD in
  let+ xsD := thunkD (selection_sortD xs) list_headD in
  Tick.ret xsD.

Lemma head_selection_sortD_cost (xs : list nat) (outD : nat) :
  outD `is_approx` head_def (selection_sort xs (length xs)) 0 ->
  forall xsA, xsA = Tick.val (head_selection_sortD xs outD) ->
  Tick.cost (head_selection_sortD xs outD) <= length xs + 2.
Proof.
  intros. rewrite H. destruct xs.
  - simpl. lia.
  - unfold head_selection_sortD.
    assert (H1 : length (n :: xs) = S (length xs)). auto. rewrite H1.
    rewrite sort_produces_element. simpl. lia.
Qed.

Definition take_selection_sortD (n : nat) (xs : list nat) (outD : listA nat) :
  Tick (T (listA nat)) :=
  let+ list_takeD := takeD n (selection_sort xs (length xs)) outD in
  let+ xsD := thunkD (selection_sortD xs) list_takeD in
  Tick.ret xsD.

Lemma selection_sortD_cost (xs : list nat) (outD : listA nat) :
  Tick.cost (selection_sortD xs outD) <= (sizeX' 1 outD) * (length xs + 2).
Proof.
  intros. generalize dependent xs. induction outD;
  intro; destruct xs; simpl; try rewrite IHoutD; lia.
Qed.

Lemma headD_demand {a} (xs : list a) (d : a) (outD : a) : 
  sizeX 1 (Tick.val (headD xs d outD)) = 1.
Proof.
  destruct xs; reflexivity.
Qed.

Theorem head_selection_sortD_cost' (xs : list nat) (outD : nat) :
  Tick.cost (head_selection_sortD xs outD) <= length xs + 3.
Proof.
  unfold head_selection_sortD. unfold Tick.bind. simpl.
  unfold thunkD. destruct (selection_sort xs (length xs)); simpl;
  rewrite selection_sortD_cost; simpl; lia.
Qed.

Lemma takeD_demand {a} (n : nat) (xs : list a) (outD : listA a) :
  sizeX 1 (Tick.val (takeD n xs outD)) <= sizeX' 1 outD.
Proof.
  generalize dependent n. generalize dependent xs.
  induction outD; intros;
  destruct n; destruct xs; simpl; try lia.
  destruct (Tick.val (takeD n xs outD)) eqn : E; try lia.
  apply le_n_S. assert (H' : sizeX' 1 x = sizeX 1 (Thunk x)). { auto. }
  rewrite H'. symmetry in E. rewrite E. apply IHoutD.
Qed.

Theorem take_selection_sortD_cost (n : nat) (xs : list nat) (outD : listA nat) :
  Tick.cost (take_selection_sortD n xs outD) <= (sizeX' 1 outD) * (length xs + 2) + n + 1.
Proof.
  unfold take_selection_sortD. unfold Tick.bind. 
  simpl. rewrite takeD_cost. unfold thunkD. 
  destruct (Tick.val (takeD n (selection_sort xs (length xs)) outD)) eqn:  E.
  - assert (H : sizeX' 1 x = sizeX 1 (Thunk x)). { reflexivity. }
    symmetry in E. rewrite E in H.
    rewrite selection_sortD_cost. rewrite H. rewrite takeD_demand. lia.
  - simpl. lia.
Qed.


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

Fixpoint splitD {a : Type} (xs : list a) (outD : listA a * listA a) : Tick (T (listA a)) :=
  Tick.tick >>
  match xs, outD with
  | [], _ => Tick.ret (Thunk NilA)
  | [x], _ => Tick.ret (Thunk (ConsA (Thunk x) (Thunk NilA)))
  | x :: x' :: xs, (ConsA zD zsD, ConsA zD' zsD') =>
    Tick.tick >>
    let+ xsD := thunkTupleD (splitD xs) (zsD, zsD') (ConsA Undefined Undefined) in
    Tick.ret (Thunk (ConsA zD (Thunk (ConsA zD' xsD))))
  | _, _ => bottom
  end.

Compute splitD [1;2;3;4;5;6;7;8] (exact [1;3;5;7], exact [2;4;6;8]).

Fixpoint mergeD (xs ys : list nat) (outD : listA nat) : Tick (T (listA nat) * T (listA nat)) :=
  Tick.tick >>
  match xs, ys, outD with
  | [], _, _ => Tick.ret (Thunk NilA, Undefined)
  | _, [], _ => Tick.ret (Undefined, Thunk NilA)
  | x :: xs, y :: ys, ConsA zD (Thunk (ConsA zD' zsD)) =>
    Tick.tick >>
    let+ (xsD, ysD) := thunkD (mergeD xs ys) zsD in
    Tick.ret (Thunk (ConsA zD xsD), Thunk (ConsA zD' ysD))
  | _, _, _ => bottom
  end.

Fixpoint mergesortD' (l : list nat) (n : nat) (outD : listA nat) : Tick (T (listA nat)) :=
  Tick.tick >>
  match l, outD, n with
  | _, _, 0 => Tick.ret Undefined
  | [], _, _ => Tick.ret (Thunk NilA)
  | [x], _, _ => Tick.ret (Thunk (ConsA (Thunk x) (Thunk NilA)))
  | _ :: _, ConsA _ _, S n =>
    let (xs, ys) := split l in
    let+ (mxsD, mysD) := mergeD (mergesort xs) (mergesort ys) outD in
    let+ xsD := thunkD (mergesortD' xs n) mxsD in
    let+ ysD := thunkD (mergesortD' ys n) mysD in
    let+ lD := thunkTupleD (splitD l) (xsD, ysD) (ConsA Undefined Undefined) in
    Tick.ret lD
  | _, _, _ => bottom
  end.

Definition merge_sortD (l : list nat) (outD : listA nat) : Tick (T (listA nat)) :=
  mergesortD' l (length l) outD.

(* Long-term goal:
   show that   head (selection_sort xs)   in O(n)
   (also could be merge_sort) *)

(* Demand function for [revA].
   [revA] has to traverse the list: the input demand is the whole list.
   (Actually, a finer solution is to force only the spine, not the elements,
   since they are protected by [T], but, simplicity.) *)
Definition revD {a} (xs : list a) (outD : listA a) : Tick (T (listA a)) :=
  Tick.MkTick (1 + length xs) (exact xs).

(* Demand function for [insertA]. 
   The input list needs to be forced only as long as its elements are <= x. 
*)
Fixpoint insertD_ (x:nat) (xs: list nat)  (outD : listA nat) : Tick (T (listA nat)) :=
  match xs, outD with 
  | nil, _ => Tick.ret (Thunk NilA)
  | y :: ys, ConsA zD zsD => 
     Tick.tick >>
     if Nat.leb x y then 
       Tick.tick >>
       let+ ysD := thunkD (insertD_ x ys) zsD in
       Tick.ret (Thunk (ConsA (Thunk y) ysD))
     else 
       Tick.ret zsD
  | _ , _ => bottom
  end.


Definition insertD (x:nat) (xs: list nat) (outD : listA nat) : Tick (T nat * T (listA nat)) :=
  Tick.tick >> Tick.tick >>
  let+ ysD := insertD_ x xs outD in 
  Tick.ret (Thunk x, ysD).


(* ----------------------------------------------------- *)

(** * Monotonicity *)

(** Making inputs of approximation functions more defined makes the output more defined.
  These can be used to generalize the demand specifications above to inputs greater than
  the input demand. *)

(** Proofs of monotonicity are largely automated by the [solve_mon] tactic from the
  [ApproxM] module. *)

Lemma appendA__mon {a} (xsA xsA' : listA a) (ysA ysA' : T (listA a))
  : xsA `less_defined` xsA' ->
    ysA `less_defined` ysA' ->
    append_ xsA  ysA `less_defined` append_ xsA' ysA'.
Proof.
  intros Hxs; revert ysA ysA'; induction Hxs; intros * Hys; cbn; solve_mon.
Qed.

#[global] Hint Resolve appendA__mon : mon.

Lemma appendA_mon {a} (xsA xsA' ysA ysA' : T (listA a))
  : xsA `less_defined` xsA' ->
    ysA `less_defined` ysA' ->
    appendA xsA  ysA `less_defined` appendA xsA' ysA'.
Proof.
  intros; unfold appendA; solve_mon.
Qed.

#[global] Hint Resolve appendA_mon : mon.

Lemma revA__mon {a} (xsA xsA' : listA a) (ysA ysA' : T (listA a))
  : xsA `less_defined` xsA' ->
    ysA `less_defined` ysA' ->
    revA_ xsA ysA `less_defined` revA_ xsA' ysA'.
Proof.
  intros Hxs; revert ysA ysA'; induction Hxs; intros * Hys; cbn; solve_mon.
Qed.

#[global] Hint Resolve revA__mon : mon.

Lemma revA_mon {a} (xsA xsA' : T (listA a))
  : xsA `less_defined` xsA' ->
    revA xsA `less_defined` revA xsA'.
Proof.
  intros; unfold revA; solve_mon.
Qed.

#[global] Hint Resolve revA_mon : mon. 

Lemma insertA__mon (v:nat) (xsA xsA' : listA nat) 
  : xsA `less_defined` xsA' ->
    insertA_ v xsA `less_defined` insertA_ v xsA'.
Proof.
  intros Hxs; induction Hxs; cbn; solve_mon.
Qed.

#[global] Hint Resolve insertA__mon : mon.


Lemma insertA_mon (v1 v2 :T nat) (xsA xsA' : T (listA nat))
  : v1 `less_defined` v2 -> xsA `less_defined` xsA' ->
    insertA v1 xsA `less_defined` insertA v2 xsA'.
Proof.
  intros; unfold insertA; solve_mon.
Qed.

#[global] Hint Resolve insertA_mon : mon.


Lemma tailX_mon {a} (xs xs' : T (listA a))
  : xs `less_defined` xs' -> tailX xs `less_defined` tailX xs'.
Proof.
  destruct 1 as [ | ? ? [ | ] ]; cbn; auto.
Qed.

#[global] Hint Resolve tailX_mon : mon.

#[global] Instance Proper_tailX {a} : Proper (less_defined ==> less_defined) (@tailX a).
Proof. exact (@tailX_mon a). Qed.


(** * append *)

(** *

    The partial functional correctness and pure functional correctness theorems
    and their proofs. *)
Theorem appendA_correct_partial {a} :
  forall (xs ys : list a) (xsA ysA : T (listA a)),
    xsA `is_approx` xs -> ysA `is_approx` ys ->
    (appendA xsA ysA) {{ fun zsA _ => zsA `is_approx` append xs ys }}.
Proof.
  destruct xsA; [| mgo_list].
  intros ysA Hxs. revert ys ysA.
  funelim (exact_listA xs); mgo_list.
  relax_apply H0; try eassumption; mgo_list.
Qed.

Theorem appendA_correct_pure {a} :
  forall (xs ys : list a) (xsA ysA : T (listA a)),
    xsA = exact xs -> ysA = exact ys ->
    (appendA xsA ysA) [[ fun zsA _ => zsA = exact (append xs ys) ]].
Proof.
  destruct xsA; [|mgo_list].
  intros ysA Hxs. revert ys ysA.
  funelim (exact_listA xs); mgo_list.
  apply optimistic_thunk_go.
  relax_apply H0; try eassumption; try reflexivity.
  mgo_list.
Qed.


(** The pessimistic specification for the cost of [appendA]. *)
Theorem appendA_cost_interval {a} : forall (xsA ysA : T (listA a)),
    (appendA xsA ysA)
    {{ fun zsA cost => 1 <= cost <= sizeX 1 xsA }}.
Proof.
  destruct xsA; [|mgo_list].
  induction x; mgo_list.
  relax_apply IHx. mgo_list.
Qed.

(** The pessimistic specification for the cost + functional correctness of
    [appendA] can be obtained using the conjunction rule. *)
Theorem appendA_spec {a} :
  forall (xs ys : list a) (xsA ysA : T (listA a)),
    xsA `is_approx` xs ->
    ysA `is_approx` ys ->
    (appendA xsA ysA) {{ fun zsA cost => zsA `is_approx` append xs ys /\ 1 <= cost <= sizeX 1 xsA }}.
Proof.
  intros. apply pessimistic_conj.
  - apply appendA_correct_partial; assumption.
  - apply appendA_cost_interval.
Qed.

(** [appendA_prefix_cost] as described in the paper. This is the case when the
    execution of [appendA] does not reach the end of [xsA]. *)
Theorem appendA_prefix_cost {a} : forall n (xsA ysA : T (listA a)),
    1 <= n <= sizeX 0 xsA ->
    (appendA xsA ysA) [[ fun zsA cost => n = sizeX 0 (Thunk zsA) /\ cost <= n ]].
Proof.
  destruct xsA; [| cbn; intros; lia].
  generalize dependent n.
  induction x; mgo_list.
  - apply optimistic_skip. mgo_list.
  - destruct (dec_eq_nat n 1).
    + apply optimistic_skip; mgo_list.
    + apply optimistic_thunk_go.
      relax. apply IHx with (n:=n-1); lia.
      mgo_list.
Qed.

(** [appendA_full_cost] as described in the paper. This is the case when the
    execution of [appendA] does reach the end of [xsA]. *)
Theorem appendA_full_cost {a} : forall (xs : list a) (xsA := exact xs) ysA,
    is_defined ysA ->
    (appendA xsA ysA) [[ fun zsA cost =>
      length xs + sizeX 1 ysA = sizeX 1 (Thunk zsA) /\ cost <= length xs + 1 ]].
Proof.
  induction xs; mgo_list.
  apply optimistic_thunk_go.
  relax_apply IHxs; mgo_list.
Qed.

(** Demand-based reasoning for appendD *)

(** These proofs should be automatable, the demand functions can be derived from the
  pure functions. *)

Lemma appendD_approx {a} (xs ys : list a) (outD : _)
  : outD `is_approx` append xs ys -> Tick.val (appendD xs ys outD) `is_approx` (xs, ys).
Proof.
  revert outD; induction xs; cbn.
  - intros; solve_approx.
  - autorewrite with exact; intros. inversion H; subst.
    inversion H4; subst; cbn.
    + constructor; cbn; constructor. autorewrite with exact. constructor; auto; constructor.
    + specialize (IHxs _ H2). inversion IHxs; subst.
      destruct (Tick.val _); cbn in *. solve_approx.
Qed.


Lemma appendD_size {a} (xs ys : list a) (outD : _)
  : outD `is_approx` append xs ys ->
    let xy := Tick.val (appendD xs ys outD) in
    sizeX' 0 outD = sizeX (sizeX 0 (snd xy)) (fst xy).
Proof.
  revert outD; induction xs; cbn; intros; [ reflexivity | ].
  destruct outD as [ | ? [] ]; cbn; [ reflexivity | | reflexivity ].
  rewrite IHxs.
  - destruct appendD as [ ? [ [] ? ] ] eqn:E; cbn; reflexivity.
  - inversion H; subst. inversion H5; subst. auto.
Qed.

Lemma appendD_Thunk_r {a} (xs ys : list a) (outD : _)
  : outD `is_approx` append xs ys ->
    forall xsA ysA, (xsA, Thunk ysA) = Tick.val (appendD xs ys outD) ->
    sizeX 0 xsA = length xs.
Proof.
  revert outD; induction xs; cbn; intros outD Hout xsA ysA H.
  - inversion H; reflexivity.
  - inversion Hout; subst.
    inversion H4; subst; cbn in H.
    + inversion H.
    + destruct appendD as [ ? [] ] eqn:ED in H; inversion H; subst; cbn.
      erewrite <- IHxs by (try rewrite ED; cbn; eauto).
      destruct t as [ xs' | ]; reflexivity.
Qed.


Lemma appendD_spec {a} (xs ys : list a) (outD : listA a)
  : outD `is_approx` append xs ys ->
    forall xsD ysD dcost, Tick.MkTick dcost (xsD, ysD) = appendD xs ys outD ->
    appendA xsD ysD [[ fun out cost => outD `less_defined` out /\ cost <= dcost ]].
Proof.
  revert outD; induction xs; cbn; intros * Hout *.
  - inversion 1; subst; cbn; mgo_; split; reflexivity.
  - autorewrite with exact in Hout. inv Hout. destruct thunkD as [ ? [] ] eqn:Eth; cbn.
    inversion 1; subst; cbn. mgo_. inv H3; cbn in Eth; inv Eth.
    + apply optimistic_skip. mgo_. split; reflexivity.
    + apply optimistic_thunk_go. relax_apply IHxs; [ try rewrite H1; eauto .. | cbn; intros * [] ].
      mgo_. split; [solve_approx | ]. lia.
Qed.

Lemma appendD_spec' {a} (xs ys : list a) (outD : listA a)
  : outD `is_approx` append xs ys ->
    forall xsD ysD dcost, Tick.MkTick dcost (xsD, ysD) = appendD xs ys outD ->
    forall xsD' ysD', xsD `less_defined` xsD' -> ysD `less_defined` ysD' ->
    appendA xsD' ysD' [[ fun out cost => outD `less_defined` out /\ cost <= dcost ]].
Proof.
  intros; eapply optimistic_corelax.
  - eapply appendA_mon; eassumption.
  - apply uc_cost.
  - eapply appendD_spec; eassumption.
Qed.

(** ** Cost specs for auxiliary functions *)

(** [appendA] is our first example where the notion of demand is relevant
  (so this differs from the spec from our initial paper).

  1. The caller (user of this theorem) must specify a demand [outD] on the
     output (first condition: [outD] must be an approximation of the pure
     output [append xs ys]).
  2. This corresponds to an input demand [(xsA, ysA)], via the demand
     function [appendD].
  3. When that input demand is met (i.e., we use [xsA] and [ysA] as the inputs
     of [appendA]), we can satisfy the output demand: we can (optimistically)
     produce an output [out] at least as defined as [outD] in time bounded
     by some function of the output demand (here it is a function of the input
     demand, which is itself a function of the output demand). *)

Lemma appendD_cost {a} (xs ys : list a) outD
  : outD `is_approx` append xs ys ->
    forall xsA, xsA = fst (Tick.val (appendD xs ys outD)) ->
    Tick.cost (appendD xs ys outD) = sizeX 1 xsA.
Proof.
  revert outD; induction xs; cbn; intros * Hout * ->; [ reflexivity | ].
  autorewrite with exact in Hout. inv Hout. inv H3; cbn; [ lia | ].
  erewrite IHxs by eauto. destruct (Tick.val _) as [ [] ? ]; cbn; lia.
Qed.

Lemma appendA_cost {a} (xs ys : list a) outD
  : outD `is_approx` append xs ys ->
    forall xsA ysA, (xsA, ysA) = Tick.val (appendD xs ys outD) ->
    appendA xsA ysA [[ fun out cost =>
      outD `less_defined` out /\ cost <= sizeX 1 xsA ]].
Proof.
  intros. destruct appendD as [ ? [] ] eqn:ED; inv H0.
  relax; [ eapply appendD_spec; eassumption + rewrite ED; reflexivity | cbn; intros * [] ].
  split; [ auto | ]. rewrite H1.
  replace cost with (Tick.cost (appendD xs ys outD)) by (rewrite ED; reflexivity).
  apply Nat.eq_le_incl, appendD_cost; [ assumption | rewrite ED; reflexivity ].
Qed.

(** We can then generalize that theorem: the postcondition can be satisfied
  as long as the input [(xsA',ysA')] is at least as defined as the input demand
  [(xsA,ysA)]. This is a straightforward consequence of [appendA]'s monotonicity
  proved earlier. *)

(** Relaxed cost specification *)
Lemma appendA_cost' {a} (xs ys : list a) outD
  : outD `is_approx` append xs ys ->
    forall xsA ysA, (xsA, ysA) = Tick.val (appendD xs ys outD) ->
    forall xsA' ysA', xsA `less_defined` xsA' -> ysA `less_defined` ysA' ->
    appendA xsA' ysA' [[ fun out cost =>
      outD `less_defined` out /\ cost <= sizeX 1 xsA ]].
Proof.
  intros. eapply optimistic_corelax.
  - eapply appendA_mon; eassumption.
  - apply uc_cost.
  - eauto using appendA_cost.
Qed.


(** * rev *)

(** The pessimistic specification about [revA]. *)

Lemma revA_pessim_ {a} :
forall (xs : list a) (xsA : listA a) (ysA : T (listA a)),
  xsA `is_approx` xs ->
  (revA_ xsA ysA) {{ fun zsA cost => cost = length xs + 1 }}.
Proof.
  intros. funelim (exact_listA xs); mgo_list.
  - relax_apply H0. assumption.
    cbn. intros. lia.
  - relax_apply H0. assumption.
    cbn. intros. lia.
Qed.

Theorem revA_pessim {a} :
forall (xs : list a) (xsA : T (listA a)),
  xsA `is_approx` xs ->
  (revA xsA) {{ fun zsA cost => cost = length xs + 1 }}.
Proof.
  unfold revA. destruct xsA; [|mgo_list].
  mgo_list; apply revA_pessim_; assumption.
Qed.

(* demand-based reasoning for rev *)

Lemma revD_approx {a} (xs : list a) (outD : _)
  : Tick.val (revD xs outD) `is_approx` xs.
Proof.
  unfold revD. reflexivity.
Qed.


Lemma revD_cost {a} (xs : list a) outD : Tick.cost (revD xs outD) = 1 + length xs.
Proof. reflexivity. Qed.

Lemma revA__cost {a} (xs ys : list a)
  : revA_ (exact xs) (exact ys) [[ fun out cost =>
      out = exact (rev_ xs ys) /\ cost = 1 + length xs ]].
Proof.
  revert ys; induction xs; [ rewrite exact_list_unfold_nil | rewrite exact_list_unfold_cons ];
    intros; mgo'.
  apply optimistic_thunk_go; mgo'.
  specialize (IHxs (a0 :: ys)). unfold exact at 2, Exact_T in IHxs.
  rewrite exact_list_unfold_cons in IHxs.
  relax; [ exact IHxs | ]. cbn; intros * [ ? -> ]; split; [auto | lia].
Qed.

Lemma revA_cost {a} (xs : list a)
  : revA (exact xs) [[ fun out cost =>
      out = exact (rev xs) /\ cost = 1 + length xs ]].
Proof.
  unfold revA; mgo'. apply optimistic_thunk_go; mgo'. relax_apply (revA__cost xs nil).
Qed.

(* This proof for [revD] is backwards (we prove [revA_cost] first, whereas for other
   functions we use the [*D_spec] lemma to prove [*A_cost]), because we took
   a shortcut in the definition of [revD]. *)
Lemma revD_spec {a} (xs : list a) (outD : listA a)
  : outD `is_approx` rev xs ->
    forall xsD dcost, Tick.MkTick dcost xsD = revD xs outD ->
    revA xsD [[ fun out cost => outD `less_defined` out /\ cost <= dcost ]].
Proof.
  intros Hout *; inversion 1; subst. relax; [ apply revA_cost | cbn; intros * []; subst ].
  split; [ assumption | reflexivity ].
Qed.


(** * Left and right folds. *)

Module CaseStudyFolds.

Definition foldl_pessim {a b bA} `{LessDefined bA} `{Exact b bA} :
(** The pessimistic specification of [foldlA]. *)
forall f (xs : list a) (xsA : T (listA a)) (v : b) (vA : T bA),
  (forall x y, (f x y) {{ fun bA cost => exists b, bA `is_approx` b /\ cost = 1 }}) ->
  xsA `is_approx` xs ->  vA `is_approx` v ->
  (foldlA f vA xsA)
    {{ fun zsA cost => cost >= length xs + 1 /\ cost <= 2 * length xs + 1 }}.
Proof.
  intros f xs xsA v vA Hf Hxs. revert v vA.
  unfold foldlA. funelim (exact_listA xs); mgo_list.
  - relax_apply Hf. cbn; intros.
    destruct H3 as (? & ? & ?); subst.
    relax. eapply H0 with (v:=x1); try eassumption.
    constructor; assumption.
    cbn. intros. lia.
  - specialize (H0 _ _ _ _ f (Thunk x)).
    cbn in H0. relax; [ apply H0 with (v:=v); auto; solve_approx | ].
    cbn; lia.
Qed.

Definition foldr_pessim {a b bA} `{LessDefined bA} `{LessDefined (T bA)} `{Exact b bA} :
(** The pessimistic specification of [foldrA]. *)
forall f (xs : list a) (xsA : T (listA a)) (v : b) (vA : T bA),
  (forall x y, (f x y) {{ fun bA cost => cost = 1 }}) ->
  xsA `is_approx` xs ->  vA `is_approx` v ->
  (foldrA f vA xsA)
    {{ fun zsA cost => cost >= 1 /\ cost <= 2 * sizeX 0 xsA + 1 }}.
Proof.
  intros f xs xsA v vA Hf Hxs. revert v vA.
  unfold foldrA. funelim (exact_listA xs); mgo_list.
  - specialize (H0 _ _ _ _ _ f (Thunk x)).
    relax; [ eapply H0; auto; solve_approx | ].
    mgo_list. relax_apply Hf. mgo_list.
  - relax_apply Hf. cbn. intros. subst.
    destruct xs; simpl; lia.
Qed.

Definition foldr_optim1 {a b bA} `{LessDefined bA} `{LessDefined (T bA)} `{Exact b bA} :
forall f (xs : list a) (xsA : T (listA a)) (v : b) (vA : T bA) n,
  1 <= n -> n < sizeX 0 xsA ->
  xsA `is_approx` xs ->  vA `is_approx` v ->
  (forall x y, (f x y) [[ fun bA cost => cost = 1 ]]) ->
  (foldrA f vA xsA) [[ fun zsA cost => cost = 2 * n ]].
Proof.
  destruct xsA; [| cbn; intros; lia]. cbn.
  revert x. induction xs; mgo_list.
  destruct (dec_eq_nat n 1); subst.
  - apply optimistic_skip. relax. eapply H6.
    cbn. intros. lia.
  - apply optimistic_thunk_go.
    destruct xs0; [|lia].
    relax. eapply IHxs with (n:=n-1); try eassumption; try lia.
    cbn; intros. relax_apply H6. cbn; intros. lia.
Qed.

Definition foldr_optim2 {a b bA} `{LessDefined bA} `{LessDefined (T bA)} `{Exact b bA}:
(** And a special cost exists when [xs] is fully evaluated. *)
forall f (xs : list a) (xsA : T (listA a)) (v : b) (vA : T bA),
  xsA = exact xs ->  vA `is_approx` v -> is_defined vA ->
  (forall x y, (f x y) [[ fun bA cost => cost = 1 ]]) ->
  (foldrA f vA xsA) [[ fun zsA cost => cost = 2 * length xs + 1 ]].
Proof.
  induction xs; mgo_list.
  apply optimistic_thunk_go.
  specialize (IHxs (Thunk (exact_listA xs)) v (Thunk x)).
  cbn in IHxs. relax_apply IHxs; auto.
  cbn. intros; subst. relax_apply H5. cbn; intros. lia.
Qed.

End CaseStudyFolds.

Module CaseStudyInsert.

Import CaseStudyFolds.

Definition insertA_pessim_ :
(** The pessimistic specification of [insertA_]. *)
forall (xs : list nat) (xsA : (listA nat)) (v : nat),
  xsA `is_approx` xs ->  
  (insertA_ v xsA)
    {{ fun zsA cost => cost <= 2 * length xs }}.
Proof.
  intros. revert xsA H.
  induction xs; intros.
  - mgo_list.
  - mgo_list. 
    destruct (v <=? exact a) eqn:LE.
    + mgo_. subst. inv H4.
      relax_apply IHxs; eauto.
      intros xs' n L.
      mgo_.
    + mgo_. 
Qed.

Definition insertA_pessim :
(** The pessimistic specification of [foldrA]. *)
forall (xs : list nat) (xsA : T (listA nat)) (vA : T nat) (v : nat),
  vA `is_approx` v ->
  xsA `is_approx` xs ->  
  (insertA vA xsA)
    {{ fun zsA cost => cost <= 2 * length xs + 2 }}.
Proof.
  intros xs xsA. 
  destruct xsA; unfold insertA; [|mgo_list].
  intros. 
  mgo_. subst. inv H. inv H0.
  relax_apply insertA_pessim_. eauto.
  cbn.
  intros y n h. lia.
Qed.

Definition sizeT {a} ( x : T a) : nat := 
  match x with 
  | Thunk v => 1
  | Undefined => 0
  end.

Definition insertSize : T (listA nat) -> nat := sizeAX sizeT 0.

(* I don't know how to give an optimistic specification of insertA.
   We don't know how many of the list elements need to be evaluated 
   when we insert. *)
Theorem insertA_prefix_cost : forall x (xsA : (listA nat)) n,
    1 <= n <= sizeX' 0 xsA ->
    (insertA_ x xsA) [[ fun zsA cost => n + 1 = sizeX' 0 zsA /\ cost <= 2 * n ]].
Proof.
  intro x.
  induction xsA; mgo_list.
Abort.


Lemma insertD__approx (x : nat) (xs : list nat) (outD : _)
  : outD `is_approx` insert x xs -> Tick.val (insertD_ x xs outD) `is_approx` xs.
Proof.
  revert outD; induction xs; cbn.
  - intros; solve_approx.
  - autorewrite with exact; intros. 
    destruct (x <=? a) eqn:LE.
    + inversion H; subst.    
      inversion H4; subst; cbn. solve_approx.
      specialize (IHxs _ H2). solve_approx.
    + inversion H; subst. solve_approx.
Qed.

Lemma insertD_size x (xs : list nat) (outD : _)
  : outD `is_approx` insert x xs ->
    let ins := Tick.val (insertD_ x xs outD) in
    (sizeX 0 ins) <= sizeX' 0 outD.
Proof.
  revert outD; induction xs; cbn; intros. 
  inversion H; subst; cbn.
  - destruct xs; lia. 
  - destruct (x <=? a) eqn:L.
    + inversion H; subst. cbn.
      inversion H4. subst. cbn. auto.
      subst. specialize (IHxs _ H2). cbn in IHxs.
      cbn. destruct (Tick.val _) eqn:T. unfold sizeX in IHxs. lia. lia.
    + inversion H. subst. cbn.
      destruct xs0. simpl. auto. simpl. auto.
Defined.


Lemma insertD_spec x (xs : list nat) (outD : listA nat)
  : outD `is_approx` insert x xs ->
    forall xsD dcost, Tick.MkTick dcost xsD = insertD_ x xs outD ->
    insertA (Thunk x) xsD [[ fun out cost => outD `less_defined` out /\ cost <= dcost ]].
Proof.
  unfold insertA.
  revert outD; induction xs; cbn; intros * Hout *.
  - unfold Tick.ret. intros h. inversion h. subst. 
    mgo_.
Admitted.

End CaseStudyInsert.


Lemma less_defined_tail_cons {a} (l : T (listA a)) x xs
  : l `less_defined` Thunk (ConsA x xs) ->
    l `less_defined` Thunk (ConsA x (tailX l)).
Proof.
  inversion 1; subst; constructor. inversion H2; constructor; cbn; [ auto | reflexivity ].
Qed.

Fixpoint selectA_ (l : listA nat) : M (option (T (listA nat) * nat)) :=
  tick >>
  match l with
  | NilA => ret None
  | ConsA x xs =>
    forcing x (fun x =>
    forcing xs (fun xs =>
    let! o := selectA_ xs in
    match o with
    | None => ret (Some (Thunk NilA, x))
    | Some (ys, y) =>
      if x <? y then
        ret (Some (Thunk (ConsA (Thunk y) ys), x))
      else
        ret (Some (Thunk (ConsA (Thunk x) ys), y))
    end))
  end.

(* Invariant: n = length l. n is the decreasing argument. *)
Fixpoint selectsortA (n : nat) (l : T (listA nat)) : M (listA nat) :=
  tick >>
  let! l := force l in
  let! o := selectA_ l in
  match n, o with
  | S n, Some (ys, y) =>
    let~ zs := selectsortA n ys in
    ret (ConsA (Thunk y) zs)
  | _, _ => ret NilA
  end.

Parameter selectsort : forall (l : list nat), list nat.

Lemma selectsortA_cost {l n}
  : n = length l ->
    forall (d : listA nat), d `is_approx` exact (selectsort l) ->
    let m := sizeX' 1 d in
    selectsortA n (exact l) [[ fun sorted cost => d `less_defined` sorted /\ cost <= m * (length l + 1) ]].
Proof.
Admitted.

Lemma selectsortA_cost' {l n}
  : n = length l ->
    forall (d : listA nat), d `is_approx` exact (selectsort l) ->
    exists (lA : T (listA nat)), lA `is_approx` l /\
    let m := sizeX' 1 d in
    selectsortA n lA [[ fun sorted cost => d `less_defined` sorted /\ cost <= m * (length l + 1) ]].
Proof.
Admitted.

(* Partial function: we assume that both arguments approximate the same list *)
Fixpoint lub_listA {a} (xs ys : listA a) : listA a :=
  match xs, ys with
  | NilA, NilA => NilA
  | ConsA x xs, ConsA y ys => ConsA (lub_T (fun r _ => r) x y) (lub_T lub_listA xs ys)
  | _, _ => NilA  (* silly case *)
  end.

#[global] Instance Lub_listA {a} : Lub (listA a) := lub_listA.

#[global] Instance LubLaw_listA {a} : LubLaw (listA a).
Proof.
  constructor.
  - intros x y z Hx; revert y; induction Hx; intros ?; inversion 1; subst; cbn; constructor; auto.
    1: inversion H; subst; inversion H4; subst; try constructor; auto.
    1: inversion H; subst; inversion H5; subst; try constructor; auto.
    inversion H6; constructor; auto.
  - intros x y [z [ Hx Hy] ]; revert y Hy; induction Hx; intros ?; inversion 1; subst; cbn;
      constructor; auto.
    1: inversion H; inversion H3; constructor; reflexivity + auto.
    1: inversion H; inversion H4; constructor; reflexivity.
    inversion H5; subst; constructor; [ reflexivity | auto ].
  - intros x y [z [Hx Hy] ]; revert x Hx; induction Hy; intros ?; inversion 1; subst; cbn;
      constructor; auto.
    1: inversion H; inversion H3; subst; invert_approx; constructor; reflexivity + auto; inversion H7; invert_approx; reflexivity.
    1: inversion H; inversion H4; subst; invert_approx; constructor; reflexivity + auto; inversion H8; invert_approx; reflexivity.
    inversion H5; subst; constructor; [ reflexivity | auto ].
Qed.
