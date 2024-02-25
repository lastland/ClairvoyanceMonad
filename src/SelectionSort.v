From Coq Require Import List Arith Psatz.

From Clairvoyance Require Import Core Approx List ListA Tick Misc.
From Equations Require Import Equations.

Import ListNotations.
Import Tick.Notations.

(** * Pure functions *)

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

Definition head_def {a} (xs : list a) (d : a) : a :=
  match xs with
  | [] => d
  | x :: _ => x
  end.


(** * Demand functions *)

Inductive prodA (A B : Type) : Type :=
  | pairA : T A -> T B -> prodA A B.

Arguments pairA {A} {B}.

Check thunkD.

Definition prodD {A B C D} (f : T A -> T C) (g : T B -> T D)
  (p : prodA A B) : prodA C D :=
  match p with
  | pairA a b => pairA (f a) (g b)
  end.

Fixpoint selectD (x : nat) (l : list nat) (outD : prodA nat (listA nat)) : Tick (T (listA nat)) :=
  Tick.tick >>
  match l with
  | [] => Tick.ret (Thunk NilA) 
  | h :: t => if x <=? h then
              let+ ysD := selectD x t (prodD id tailX outD) in
              Tick.ret (Thunk (ConsA (exact h) ysD))
            else
              let+ ysD := selectD h t (prodD id tailX outD) in
              Tick.ret (Thunk (ConsA (exact h) ysD))
    end.
           
Fixpoint selection_sortD (l : list nat) (n : nat) (outD : listA nat) :
  Tick (T (listA nat)) :=
  Tick.tick >>
  match l, n with
  | _, 0 => match outD with
           | NilA => Tick.ret Undefined
           | _ => bottom
           end
  | [], _ => match outD with
           | NilA => Tick.ret (Thunk NilA)
           | _ => bottom
           end
  | x :: r, S n' => match outD with
           | ConsA yD ysD =>
               let (y, r') := select x r in
               let+ xsD := thunkD (selection_sortD r' n') ysD in
               let+ resD := selectD x r (pairA (exact y) xsD) in
               Tick.ret (Thunk (ConsA (Thunk x) resD))
           | _ => bottom
           end
  end.

(* We force the empty list or the first element only *)
Definition headD {a} (xs : list a) (d : a) (outD : a) : Tick (T (listA a)) :=
  Tick.tick >>
  match xs with
  | [] => Tick.ret (Thunk NilA)
  | x :: _ => Tick.ret (Thunk (ConsA (Thunk x) Undefined))
  end.

Definition head_selection_sortD (xs : list nat) (outD : nat) : Tick (T (listA nat)) :=
  let res := selection_sort xs (length xs) in
  let+ list_headD := headD res 0 outD in
  let+ xsD := thunkD (selection_sortD xs (length xs)) list_headD in
  Tick.ret xsD.


(** * Alternative defs (specs) *)

(* The entire list must be forced to select smallest element *)
Definition selectD' (x : nat) (xs : list nat) (outD : listA nat) : Tick (T (listA nat)) :=
  Tick.MkTick (1 + length xs) (exact xs).

(* The entire list is forced one selection at a time*)
Fixpoint selection_sortD' (xs : list nat) (outD : listA nat) :
  Tick (T (listA nat)) :=
  Tick.tick >>
  match xs, outD with
  | [], _ => Tick.ret (Thunk NilA)
  | x :: xs', ConsA zD zsD =>
    let+ _ := thunkD (selection_sortD' xs') zsD in
    let+ xsD := selectD' x xs' (exact xs) in
    Tick.ret xsD (* We invariably force the entire input list *)
  | _, _ => bottom
  end.

Definition head_selection_sortD' (xs : list nat) (outD : nat) : Tick (T (listA nat)) :=
  let+ list_headD := headD (selection_sort xs (length xs)) 0 outD in
  let+ xsD := thunkD (selection_sortD' xs) list_headD in
  Tick.ret xsD.

(** * Theorem for pure functions *)

Lemma sort_produces_element (n : nat) (x : nat) (xs : list nat) :
  selection_sort (x :: xs) (S n) = fst (select x xs) :: selection_sort (snd (select x xs)) n.
Proof.
  simpl. destruct (select x xs). simpl. reflexivity.
Qed.

(** * Equivalence between demand functions and specs *)

Lemma selectD_selectD'_leq : forall x xs yD ysD outD,
    Tick.cost (selectD x xs (pairA yD ysD)) <= Tick.cost (selectD' x xs outD).
Proof.
  intros x xs. revert x.
  induction xs as [|y ys]; intros; simpl; try lia.
  destruct (x <=? y); simpl.
  - specialize (IHys x (id yD) (tailX ysD) outD).
    unfold selectD' in IHys. simpl in IHys. lia.
  - specialize (IHys y (id yD) (tailX ysD) outD).
    unfold selectD' in IHys. simpl in IHys. lia.
Qed.

Lemma selectD_selectD'_eq : forall x xs outD,
    let (y, ys) := select x xs in
    forall yD ysD,
      yD `is_approx` y ->
      ysD `is_approx` ys ->
      outD = exact ys ->
      selectD x xs (pairA yD ysD) = selectD' x xs outD.
Proof.
  intros x xs. revert x.
  induction xs as [|x' xs']; intros.
  - intros yD ysD Hly Hlys ->. reflexivity.
  - simpl. destruct (x <=? x') eqn:Hleq; simpl.
    + destruct (select x xs') eqn:Hselect.
      intros yD ysD Hly Hlys ->.
      unfold selectD', Tick.bind. simpl.
      specialize (IHxs' x (exact l)).
      rewrite Hselect in IHxs'.
      inversion Hlys; subst.
      * simpl. specialize (IHxs' yD Undefined Hly).
        assert (Hundef: Undefined `less_defined` exact l) by solve_approx.
        specialize (IHxs' Hundef eq_refl).
        unfold selectD' in IHxs'. 
        unfold id. rewrite IHxs'; simpl.
        f_equal. lia.
      * simpl. inversion H1; subst.
        specialize (IHxs' yD xs Hly H4 eq_refl).
        unfold id. rewrite IHxs'. unfold selectD'; simpl.
        f_equal. lia.
    + destruct (select x' xs') eqn:Hselect.
      intros yD ysD Hly Hlys ->.
      unfold selectD', Tick.bind. simpl.
      specialize (IHxs' x' (exact l)).
      rewrite Hselect in IHxs'.
      inversion Hlys; subst.
      * simpl. specialize (IHxs' yD Undefined Hly).
        assert (Hundef: Undefined `less_defined` exact l) by solve_approx.
        specialize (IHxs' Hundef eq_refl).
        unfold selectD' in IHxs'. 
        unfold id. rewrite IHxs'; simpl.
        f_equal. lia.
      * simpl. inversion H1; subst.
        specialize (IHxs' yD xs Hly H4 eq_refl).
        unfold id. rewrite IHxs'. unfold selectD'; simpl.
        f_equal. lia.
Qed.

Lemma selection_sortD_sortD' (xs : list nat) (outD : listA nat) :
  forall n, n >= length xs ->
  Tick.cost (selection_sortD xs n outD) =
    Tick.cost (selection_sortD' xs outD).
Proof.
  induction xs as [| x xs]; simpl; intros.
  - destruct n, outD; simpl; lia.
  - destruct n, outD; simpl; try lia.
    destruct (select x xs) eqn:Hselect.
    destruct x2; simpl.
    + admit.      
    + pose proof (selectD_selectD'_eq x xs (exact l)) as Hdd'.
      rewrite Hselect in Hdd'. specialize (Hdd' (exact n0) bottom).
      assert (selectD x xs (pairA (exact n0) bottom) = selectD' x xs (exact l)).
      { apply Hdd'; solve_approx. }
      unfold AO_Exact in H0. simpl in H0.
      rewrite H0. reflexivity.
Admitted.    

(** TODO: Finish this. *)

(*
Lemma selection_sortD_cost (xs : list nat) (outD : listA nat) :
  Tick.cost (selection_sortD xs outD) <= (sizeX' 1 outD) * (length xs + 2).
Proof.
  intros. generalize dependent xs. induction outD;
  intro; destruct xs; simpl; try rewrite IHoutD; try lia.
  - pose proof (selectD_selectD'_leq n xs (exact (n :: xs))) as Hle.
    unfold selectD' in Hle. simpl in Hle. lia.
  - pose proof (selectD_selectD'_leq n xs (exact (n :: xs))) as Hle.
    unfold selectD' in Hle. simpl in Hle. lia.
Qed.

Lemma head_selection_sortD_cost (xs : list nat) (outD : nat) :
  outD `is_approx` head_def (selection_sort xs (length xs)) 0 ->
  forall xsA, xsA = Tick.val (head_selection_sortD xs outD) ->
  Tick.cost (head_selection_sortD xs outD) <= length xs + 2.
Proof.
  intros. rewrite H. destruct xs.
  - simpl. lia.
  - unfold head_selection_sortD.
    assert (H1 : length (n :: xs) = S (length xs)). auto. rewrite H1.
    rewrite sort_produces_element. simpl.
    pose proof (selectD_selectD'_leq n xs (exact (n :: xs))) as Hle.
    unfold selectD' in Hle. simpl in Hle. lia.
Qed.

Definition take_selection_sortD (n : nat) (xs : list nat) (outD : listA nat) :
  Tick (T (listA nat)) :=
  let+ list_takeD := takeD n (selection_sort xs (length xs)) outD in
  let+ xsD := thunkD (selection_sortD xs) list_takeD in
  Tick.ret xsD.

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
*)

(* I'm not sure if we need these... *)

(*
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

*)
