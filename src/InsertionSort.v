From Coq Require Import List Arith Psatz.

From Clairvoyance Require Import Core Approx List ListA Tick Misc.

Import ListNotations.
Import Tick.Notations.

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
