From Coq Require Import List Arith Psatz.

From Clairvoyance Require Import
  Core Approx ApproxM List ListA Tick Misc TickCost.

From Equations Require Import Equations.

Import ListNotations.
Import Tick.Notations.

Fixpoint insert (x : nat) (xs : list nat) : list nat :=
  match xs with 
  | nil => x :: nil
  | y :: ys => if y <=? x then
               let zs := insert x ys in
               y :: zs
             else x :: y :: ys
  end.

Fixpoint insertion_sort (xs : list nat) : list nat :=
  match xs with
  | nil => nil
  | y :: ys =>
      let zs := insertion_sort ys in
      insert y zs
  end.

Fixpoint insertA_ (x : nat) (xs : listA nat) : M (listA nat) :=
  tick >>
  match xs with 
  | ConsA y ys => 
      forcing y (fun y' =>
      if Nat.leb x y' then 
        forcing ys (fun ys' => 
        let~ t := insertA_ x ys' in
        ret (ConsA y t))
      else ret (ConsA (Thunk x) (Thunk (ConsA y ys))))
  | NilA => ret (ConsA (Thunk x) (Thunk NilA))
  end.

Definition insertA (x:T nat) (xs : T(listA nat)) : M (listA nat) :=
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

Lemma insert_length_inv : forall x xs,
    length (insert x xs) = length xs + 1.
Proof.
  intros x xs. revert x. induction xs.
  - simpl. lia.
  - simpl; intros.
    destruct (a <=? x) eqn:Hax; simpl; [|lia].
    specialize (IHxs x). lia.
Qed.

Lemma insertion_sort_length_inv : forall xs,
    length (insertion_sort xs) = length xs.
Proof.
  induction xs; simpl; [lia|].
  rewrite insert_length_inv. lia.
Qed.

Lemma insert_is_cons : forall x xs,
    exists y ys, insert x xs = y :: ys.
Proof.
  intros x xs. revert x. induction xs; intros.
  - simpl. exists x. exists []. reflexivity.
  - simpl. destruct (a <=? x);
    do 2 eapply ex_intro; reflexivity.
Qed.
  
Module CaseStudyInsert.

Import CaseStudyFolds.

Definition insertA_pessim_ :
(** The pessimistic specification of [insertA_]. *)
forall (xs : list nat) (xsA : (listA nat)) (v : nat),
  xsA `is_approx` xs ->  
  (insertA_ v xsA)
    {{ fun zsA cost => cost <= 2 * length xs + 1 }}.
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
    {{ fun zsA cost => cost <= 2 * length xs + 1 }}.
Proof.
  intros xs xsA. 
  destruct xsA; unfold insertA; [|mgo_list].
  intros. 
  mgo_. subst. inv H. inv H0.
  relax_apply insertA_pessim_. eauto.
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
Fixpoint insertD (x:nat) (xs: list nat)  (outD : listA nat) : Tick (T (listA nat)) :=
  Tick.tick >>
  match xs, outD with 
  | [], ConsA zD zsD =>
      Tick.ret (Thunk NilA)
  | y :: ys, ConsA zD zsD => 
     if Nat.leb y x then 
       let+ ysD := thunkD (insertD x ys) zsD in
       Tick.ret (Thunk (ConsA (Thunk y) ysD))
     else 
       Tick.ret zsD
  | _ , _ => bottom (* absurdity case *)
  end.

Fixpoint insertion_sortD (xs: list nat)  (outD : listA nat) : Tick (T (listA nat)) :=
  Tick.tick >>
  match xs with
  | [] => Tick.ret (Thunk NilA)
  | y :: ys =>
      let zs := insertion_sort ys in
      let+ zsD := insertD y zs outD in
      let+ ysD := thunkD (insertion_sortD ys) zsD in
      Tick.ret (Thunk (ConsA (Thunk y) ysD))
  end.

Lemma insertD__approx (x : nat) (xs : list nat) (outD : _)
  : outD `is_approx` insert x xs -> Tick.val (insertD x xs outD) `is_approx` xs.
Proof.
  revert outD; induction xs; cbn.
  - intros; destruct outD; solve_approx.
  - autorewrite with exact; intros. 
    destruct (a <=? x) eqn:LE.
    + inversion H; subst.    
      inversion H4; subst; cbn. solve_approx.
      specialize (IHxs _ H2). solve_approx.
    + inversion H; subst. solve_approx. 
Qed.

Lemma insertD_size x (xs : list nat) outD :
    let ins := Tick.val (insertD x xs outD) in
    (sizeX 1 ins) <= sizeX' 1 outD.
Proof.
  revert outD; induction xs; cbn; intros.
  - destruct outD; simpl. lia. destruct x2; lia.
  - destruct (a <=? x) eqn:L.
    + destruct outD; simpl; try lia.
      destruct x2; simpl; try lia.
      specialize (IHxs x0).
      destruct (insertD x xs x0); simpl in *.
      destruct val; simpl in *; lia.
    + destruct outD; simpl; try lia.
      destruct x2; simpl; lia.
Qed.

Fixpoint leb_count x (xs : list nat) : nat :=
  match xs with
  | [] => 0
  | (y::ys) => if Nat.leb y x
             then 1 + leb_count x ys
             else 0
  end.

Lemma insertD_cost x (xs : list nat)  (outD : listA nat) :
  Tick.cost (insertD x xs outD) <= leb_count x xs + 1.
Proof.
  revert x outD. induction xs; simpl; intros.
  - destruct outD; simpl; lia.
  - destruct (a <=? x) eqn:Hax.
    + destruct outD; simpl; [lia|].
      destruct x2; simpl; [|lia].
      specialize (IHxs x x0). lia.
    + destruct outD; simpl; lia.
Qed.

Lemma insertD_cost' x (xs : list nat) (outD : listA nat) :
  Tick.cost (insertD x xs outD) <= sizeX' 1 outD.
Proof.
  revert x outD. induction xs; simpl; intros.
  - destruct outD; simpl. lia.
    destruct x2; simpl; lia.
  - destruct (a <=? x) eqn:Hax.
    + destruct outD; simpl; [lia|].
      destruct x2; simpl; [|lia].
      specialize (IHxs x x0). lia.
    + destruct outD; simpl. lia.
      destruct x2; simpl; lia.
Qed.

Lemma insertD_cost'' x (xs : list nat) (outD : listA nat) :
  Tick.cost (insertD x xs outD) <= length xs + 1.
Proof.
  revert x outD. induction xs; simpl; intros.
  - destruct outD; simpl; lia.
  - destruct (a <=? x) eqn:Hax.
    + destruct outD; simpl; [lia|].
      destruct x2; simpl; [|lia].
      specialize (IHxs x x0). lia.
    + destruct outD; simpl; lia.
Qed.

Lemma insertion_sortD__approx (xs : list nat) (outD : _)
  : outD `is_approx` insertion_sort xs ->
    Tick.val (insertion_sortD xs outD) `is_approx` xs.
Proof.
  revert outD. induction xs.
  - simpl; solve_approx.
  - simpl. destruct outD; intros H.
    + pose proof (insert_is_cons a (insertion_sort xs)).
      destruct H0 as [y [ ys Hic] ]. rewrite Hic in H.
      autorewrite with exact in H. inversion H.
    + pose proof (insertD__approx a (insertion_sort xs) (ConsA x1 x2) H).
      inversion H0; subst.
      * solve_approx.
      * specialize (IHxs x H3). simpl.
        solve_approx.
Qed.        

Lemma insertion_sortD_cost (xs : list nat)  (outD : listA nat) :
  Tick.cost (insertion_sortD xs outD) <= (sizeX' 1 outD + 1) * (length xs + 1).
Proof.
  revert outD. induction xs; simpl.
  - destruct outD; simpl; try lia. 
  - intros. rewrite insertD_cost'.
    destruct (insertD a (insertion_sort xs) outD)
      as [cost [ x |] ] eqn:Hinsert.
    + simpl. specialize (IHxs x).
      pose proof (insertD_size a (insertion_sort xs) outD).
      rewrite Hinsert in H. simpl in H.
      rewrite IHxs. rewrite H. nia.
    + simpl. nia.
Qed.

Definition head_insertion_sortD (xs : list nat) (outD : nat) :
  Tick (T (listA nat)) :=
  let res := insertion_sort xs in
  let+ list_headD := headD res 0 outD in
  let+ xsD := thunkD (insertion_sortD xs) list_headD in
  Tick.ret xsD.

Definition take_insertion_sortD (n : nat) (xs : list nat) (outD : listA nat) :
  Tick (T (listA nat)) :=
  let res := insertion_sort xs in
  let+ list_takeD := takeD n res outD in
  let+ xsD := thunkD (insertion_sortD xs) list_takeD in
  Tick.ret xsD.

Lemma head_insertion_sortD_cost (xs : list nat) (outD : nat) :
  outD `is_approx` head_def (insertion_sort xs) 0 ->
  forall xsA, xsA = Tick.val (head_insertion_sortD xs outD) ->
  Tick.cost (head_insertion_sortD xs outD) <= 2 * length xs + 3.
Proof.
  intros. unfold head_insertion_sortD.
  rewrite bind_cost, headD_cost, Tick.right_ret.
  destruct (insertion_sort xs) eqn:Hsort.
  - simpl. rewrite insertion_sortD_cost; simpl; lia.
  - simpl. rewrite insertion_sortD_cost; simpl; lia.
Qed.  

Theorem take_insertion_sortD_cost (n : nat) (xs : list nat) (outD : listA nat) :
  Tick.cost (take_insertion_sortD n xs outD) <=
    (n + 1) * (length xs + 2) + 1.
Proof.
  intros. unfold take_insertion_sortD.
  rewrite bind_cost, takeD_cost, Tick.right_ret.
  destruct (insertion_sort xs) eqn:Hsort.
  - pose proof (@takeD_length _ n [] outD).
    destruct (takeD n [] outD) eqn:HtD; destruct val; simpl.
    + specialize (H x eq_refl).
      rewrite insertion_sortD_cost. destruct H; nia.
    + lia.
  - pose proof (@takeD_length _ n (n0 :: l) outD).
    destruct (takeD n (n0 :: l) outD) eqn:HtD; destruct val; simpl.
    + specialize (H x eq_refl).
      rewrite insertion_sortD_cost. destruct H; nia.
    + lia.
Qed.

End CaseStudyInsert.
