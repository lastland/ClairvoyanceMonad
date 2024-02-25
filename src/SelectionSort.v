From Coq Require Import List Arith Psatz RelationClasses.

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

Definition take_selection_sortD (n : nat) (xs : list nat) (outD : listA nat) :
  Tick (T (listA nat)) :=
  let res := selection_sort xs (length xs) in
  let+ list_takeD := takeD n res outD in
  let+ xsD := thunkD (selection_sortD xs (length xs)) list_takeD in
  Tick.ret xsD.

(** * Alternative defs (specs) *)

(* The entire list must be forced to select smallest element *)
Definition selectD' (x : nat) (xs : list nat) (outD : listA nat) : Tick (T (listA nat)) :=
  Tick.MkTick (1 + length xs) (exact xs).

(* 
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
*)

(** * Theorem for pure functions *)

Lemma select_length_inv : forall x xs y ys,
    select x xs = (y, ys) ->
    length xs = length ys.
Proof.
  intros x xs. revert x. induction xs; simpl.
  - inversion 1; subst; reflexivity.
  - intros. destruct (x <=? a) eqn:Hxa.
    + destruct (select x xs) eqn:Hselect; subst.
      inversion H; subst. simpl.
      specialize (IHxs x y l Hselect). lia.
    + destruct (select a xs) eqn:Hselect; subst.
      inversion H; subst. simpl.
      specialize (IHxs a y l Hselect). lia.
Qed.

Lemma sort_produces_element (n : nat) (x : nat) (xs : list nat) :
  selection_sort (x :: xs) (S n) = fst (select x xs) :: selection_sort (snd (select x xs)) n.
Proof.
  simpl. destruct (select x xs). simpl. reflexivity.
Qed.

(** * Equivalence between demand functions and specs *)

Lemma selectD_cost : forall x xs yD ysD,
    Tick.cost (selectD x xs (pairA yD ysD)) <= (1 + length xs).
Proof.
  intros x xs. revert x.
  induction xs as [|y ys]; intros; simpl; try lia.
  destruct (x <=? y); simpl.
  - specialize (IHys x (id yD) (tailX ysD)); lia.
  - specialize (IHys y (id yD) (tailX ysD)); lia.
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

(*
Lemma selection_sortD_sortD' (xs : list nat) (outD : listA nat) :
  forall n, n >= length xs ->
  Tick.cost (selection_sortD xs n outD) =
    Tick.cost (selection_sortD' xs outD).
Proof.
  revert outD. induction xs as [| x xs]; simpl; intros.
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
*)

Lemma selection_sortD_cost (xs : list nat) (n : nat) (outD : listA nat) :
  n >= length xs ->
  Tick.cost (selection_sortD xs n outD) <= (sizeX' 1 outD) * (length xs + 1).
Proof.
  revert xs outD. induction n.
  - simpl. destruct outD; destruct xs; simpl; try lia; destruct x2; lia.
  - simpl. destruct xs; destruct outD; simpl; try lia; destruct x2; try lia.
    + destruct (select n0 xs) eqn:Hselect. intros.
      simpl. specialize (IHn l x).
      pose proof (select_length_inv n0 xs n1 l Hselect).
      assert (n >= length l) by lia. rewrite H0. specialize (IHn H1).
      rewrite selectD_cost. lia.
    + destruct (select n0 xs) eqn:Hselect. intros.
      simpl. specialize (IHn l NilA).
      pose proof (select_length_inv n0 xs n1 l Hselect).
      assert (n >= length l) by lia. rewrite H0. specialize (IHn H1).
      rewrite selectD_cost. lia.
Qed.

Open Scope tick_scope.

Lemma bind_cost : forall {A B : Type} (m : Tick A) (k : A -> Tick B),
  Tick.cost (let+ x := m in k x) = Tick.cost m + Tick.cost (k (Tick.val m)).
Proof. reflexivity. Qed.

Lemma right_ret : forall {A : Type} (m : Tick A),
  (let+ x := m in Tick.ret x) = m.
Proof.
  intros. unfold Tick.bind. destruct m; simpl.
  f_equal. lia.
Qed.

Lemma headD_demand {a} (xs : list a) (d : a) (outD : a) : 
  sizeX 1 (Tick.val (headD xs d outD)) = 1.
Proof.
  destruct xs; reflexivity.
Qed.

Lemma headD_cost : forall {A : Type} (xs : list A) (d x : A),
    Tick.cost (headD xs d x) = 1.
Proof.
  destruct xs; reflexivity.
Qed.

Lemma takeD_cost : forall {A : Type} (n : nat) (xs : list A) (outD : listA A),
    Tick.cost (takeD n xs outD) <= sizeX' 1 outD.
Proof.
  induction n; destruct xs, outD; simpl; try lia;
    destruct x2; simpl; try lia.
  specialize (IHn xs x). lia.  
Qed.

Lemma takeD_length : forall {A : Type}
                            (n : nat) (xs : list A) (outD ys : listA A),
    Tick.val (takeD n xs outD) = Thunk ys ->
    sizeX' 1 ys  <= sizeX' 1 outD /\ sizeX' 1 ys <= n.
Proof.
  induction n; destruct xs, outD; simpl; intros;
    inversion H; subst; simpl; try lia.
  - destruct x2; lia.
  - destruct x2; simpl; try lia.
    destruct (Tick.val (takeD n xs x)) eqn:Htake.
    + specialize (IHn _ _ _ Htake). lia.
    + lia.
Qed.

Lemma thunkD_cost : forall {A B : Type} `{LessDefined A} `{Bottom B}
                      (x : A) (y : T A) (f : A -> Tick B),
  y = Thunk x \/ y = Undefined ->
  Tick.cost (thunkD f y) <= Tick.cost (f x).
Proof.
  intros. destruct H1; subst; simpl; lia.
Qed.

Lemma head_selection_sortD_cost (xs : list nat) (outD : nat) :
  outD `is_approx` head_def (selection_sort xs (length xs)) 0 ->
  forall xsA, xsA = Tick.val (head_selection_sortD xs outD) ->
  Tick.cost (head_selection_sortD xs outD) <= length xs + 2.
Proof.
  intros. unfold head_selection_sortD.
  rewrite bind_cost, headD_cost, right_ret.
  destruct (selection_sort xs (length xs)) eqn:Hsort.
  - simpl. rewrite selection_sortD_cost; simpl; lia.
  - simpl. rewrite selection_sortD_cost; simpl; lia.
Qed.  

Theorem take_selection_sortD_cost (n : nat) (xs : list nat) (outD : listA nat) :
  Tick.cost (take_selection_sortD n xs outD) <= n * (length xs + 1) + sizeX' 1 outD + 1.
Proof.
  intros. unfold take_selection_sortD.
  rewrite bind_cost, takeD_cost, right_ret.
  destruct (selection_sort xs (length xs)) eqn:Hsort.
  - pose proof (takeD_length n [] outD).
    destruct (takeD n [] outD) eqn:HtD; destruct val; simpl.
    + specialize (H x eq_refl).
      rewrite selection_sortD_cost; [|lia]. destruct H; nia.
    + lia.
  - pose proof (takeD_length n (n0 :: l) outD).
    destruct (takeD n (n0 :: l) outD) eqn:HtD; destruct val; simpl.
    + specialize (H x eq_refl).
      rewrite selection_sortD_cost; [|lia]. destruct H; nia.
    + lia.
Qed.
