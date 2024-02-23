From Coq Require Import List Arith Psatz.

From Clairvoyance Require Import Core Approx ApproxM List ListA Tick Misc.

Import ListNotations.
Import Tick.Notations.

Fixpoint insert (x : nat) (xs : list nat) : list nat :=
  match xs with 
  | y :: ys => if Nat.leb x y then y :: insert x ys else x :: y :: ys
  | nil => x :: nil
  end.

Definition insert_sort (xs : list nat) : list nat :=
  foldr nil insert xs.

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

