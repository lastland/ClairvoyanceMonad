From Coq Require Import List Arith Psatz.

From Clairvoyance Require Import Core Approx List ListA Tick Misc.

Import ListNotations.
Import Tick.Notations.

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
