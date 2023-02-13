(* Overview

- Pure implementation of binomial heaps: [Tree], [Heap], [link], [rank], 
    [root], [insTree], [insert], [merge], [removeMinTree], [findMin], [deleteMin]
- Clairvoyant-monadic implementation: [TreeA], [HeapA], [linkA], [rankA], 
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

Import DF.Notations.
#[local] Open Scope df.

Notation A := nat (only parsing).

Inductive Tree : Type :=
  | Node : nat -> A -> list Tree -> Tree.

Inductive TreeA : Type :=
  | NodeA : T nat -> T A -> T (listA TreeA) -> TreeA.

Canonical AA_Tree :=
  {| carrier := Tree
  ;  approx := TreeA
  ;  AA_Setoid := TODO
  ;  AA_IsAA := TODO
  ;  AA_IsAS := TODO
  |}.

(* Encoding of Node *)
Definition nodeD {r : AA} {s : r} {n : nat} {x : A} {ts : list Tree}
    (nD : DF s n) (xD : DF s x) (tsD : DF s ts)
  : DF s (Node n x ts).
Proof. refine TODO. Defined.

(* Encoding of match on Tree *)
Definition match_Tree {a c : AA}
    {g : c} {t : Tree} (f : Tree -> a)
    (CASE : DF g t)
    (NODE : forall n x ts, DF (g, n, x, ts) (f (Node n x ts)))
  : DF g (f t) :=
  match t with
  | Node n x ts => TODO >>> NODE n x ts
  end.

(* Encoding of operators *)

Definition le_ (x y : nat) : DF (x, y) (x <=? y).
Proof. refine TODO. Defined.

Definition lt_ (x y : nat) : DF (x, y) (x <? y).
Proof. refine TODO. Defined.

Definition add1 (x : nat) : DF x (x + 1).
Proof. refine TODO. Defined.

Definition link (t1 t2 : Tree) : Tree :=
  match (t1, t2) with
  | (Node r1 v1 c1, Node r2 v2 c2) => if leb v1 v2
    then Node (r1 + 1) v1 (t2 :: c1)
    else Node (r2 + 1) v2 (t1 :: c2)
  end.

Definition linkDF t1 t2 : DF (t1, t2) (link t1 t2) :=
  DF.tick (
  match_Tree (fun t1 => link t1 t2)
    (var t1)
    (fun r1 v1 c1 =>
      match_Tree (fun t2 => link (Node r1 v1 c1) t2)
        (var t2)
        (fun r2 v2 c2 =>
          DF.if_ (P := fun b => if b then _ else _) (call (le_ v1 v2))
              (nodeD (call (add1 r1)) (var v1) (consD (nodeD (var r2) (var v2) (var c2)) (var c1)))
              (nodeD (call (add1 r2)) (var v2) (consD (nodeD (var r1) (var v1) (var c1)) (var c2))))
    )
  ).

Record Heap : Type := MkHeap
  { trees : list Tree }.

Record HeapA : Type := MkHeapA
  { treesA : T (listA TreeA) }.

Canonical AA_Heap : AA :=
  {| carrier := Heap
  ;  approx := T HeapA
  ;  AA_Setoid := TODO
  ;  AA_IsAA := TODO
  ;  AA_IsAS := TODO
  |}.

Definition MkHeapD {G : AA} {ts : list Tree} {g : G} (f : DF g ts) : DF g (MkHeap ts).
Proof. refine TODO. Defined.

Definition treesD {G : AA} {g : G} {h : Heap} (f : DF g h) : DF g (trees h).
Proof. refine TODO. Defined.

Definition match_Heap {a c : AA}
    {g : c} {t : Heap} {f : Heap -> a}
    (MKHEAP : forall ts, DF (g, ts) (f (MkHeap ts)))
  : DF (g, t) (f t) :=
  match t with
  | MkHeap ts => TODO >>> MKHEAP ts
  end.

Definition rank (t : Tree) : nat :=
  match t with
  | (Node r v c) => r
  end.

Definition rankDF t : DF t (rank t) :=
  DF.tick (
  match_Tree (fun t => rank t)
    (var t)
    (fun r v c => var r)
  ).

Definition root (t : Tree) : A :=
  match t with
  | (Node r v c) => v
  end.

Definition rootDF t : DF t (root t) :=
  DF.tick (
  match_Tree (fun t => root t)
    (var t)
    (fun r v c => var v)
  ).

(*Assumes t has rank <= the rank of the first element of ts (if any).*)
Fixpoint insTree (t : Tree) (ts : list Tree) : list Tree :=
  match ts with
  | [] => [t]
  | t' :: ts' => if rank t <? rank t'
    then t :: ts
    else insTree (link t t') ts' (*t and t' should have the same rank*)
  end.

Fixpoint insTreeDF (t : Tree) (ts : list Tree)
  : DF (t, ts) (insTree t ts) :=
  DF.tick (
    match_list (P := fun ts => insTree t ts) (var ts)
      (consD (var t) nilD)
      (fun t' ts' =>
        DF.let_ (call (rankDF t)) (
        DF.let_ (call (rankDF t')) (
        DF.let_ (call (lt_ (rank t) (rank t'))) (
        DF.if_ (P := fun b => if b then _ else _) (var (rank t <? rank t'))
          (consD (var t) (consD (var t') (var ts')))
          (DF.let_ (call (linkDF t t')) (
           call (insTreeDF (link t t') ts')))))))
  ).

Definition insert (x : A) (hp : Heap)
  : Heap :=
  MkHeap (insTree (Node 0 x []) (trees hp)).

Definition natD {G : AA} {g : G} (n : nat) : DF g n.
Admitted.

Definition insertDF x hp : DF (x, hp) (insert x hp) :=
  DF.let_ (nodeD (natD 0) (var x) nilD) (
  DF.let_ (treesD (var hp)) (
  MkHeapD (call (insTreeDF _ _)))).

(* Potential: number of trees
   (times an implementation-dependent multiplicative factor)
   It would be 1 if we just counted calls to [link].  *)

Definition pot_list {A : Type} (ts : T (listA A)) : nat :=
  3 * sizeX 0 ts.

Definition measureT {a : Type} (f : a -> nat) (t : T a) : nat :=
  match t with
  | Undefined => 0
  | Thunk x => f x
  end.

Definition pot_heap : T HeapA -> nat :=
  measureT (fun h => pot_list (treesA h)).

Definition valid_Trees (ts : list Tree) : Prop.
Admitted.

Definition valid_Heap (h : Heap) : Prop := valid_Trees (trees h).

Definition OTick_has_cost {A' : Type} (m : nat) (u : OTick A') (pre : A' -> nat) (post : nat) :=
  match u with
  | None => False
  | Some v => m + pre (Tick.val v) + Tick.cost v <= post
  end.

Definition has_cost_ {A B : AA} {a : A} {b : B}
    (f : DF a b) (m : nat) (pre : approx A -> nat) (post : approx B -> nat) (n : nat)
  : Prop :=
  forall b' : approx B, b' `is_approx` b ->
    OTick_has_cost m (apply f b') pre (n + post b').

Definition has_cost {A B : AA} {a : A} {b : B}
    (f : DF a b) (pre : approx A -> nat) (post : approx B -> nat) (n : nat)
  : Prop :=
  has_cost_ f 0 pre post n.

Definition measure_plus {A B : Type} (f : A -> nat) (g : B -> nat) (xy : A * B) : nat :=
  f (fst xy) + g (snd xy).

Infix "+++" := measure_plus (at level 40).

Definition zero {A : Type} (_ : A) : nat := 0.

(* Amortized complexity of insert *)
Definition insert_budget := 3.

Class Subadditive {A : AA} (f : approx A -> nat) : Prop :=
  { subadditive_zero : forall x, f (bottom_of x) = 0
  ; subadditive_lub  : forall x y, f (lub x y) <= f x + f y
  }.

#[global]
Instance Subadditive_zero {A : AA} : Subadditive (A := A) zero.
Proof.
  constructor; reflexivity.
Qed.

#[global]
Instance Subadditive_measure_plus {A B : AA}
    (f : approx A -> nat) (g : approx B -> nat)
    `(!Subadditive f, !Subadditive g)
  : Subadditive (f +++ g).
Proof.
  constructor.
  - intros []; unfold measure_plus; cbn.
    rewrite 2 subadditive_zero. reflexivity.
  - intros x y. unfold measure_plus; cbn.
    rewrite 2 subadditive_lub. lia.
Qed.

#[global] Instance Proper_S_le : Proper (le ==> le) S.
Proof. exact le_n_S. Qed.

Lemma subadditive_sizeX' {a : Type} (n : nat) (xs ys : listA a)
  : sizeX' n (lub xs ys) <= sizeX' n xs + sizeX' n ys.
Proof.
  revert ys; induction xs as [ | x | x xs IH ]; intros [| y [] ]; cbn; try rewrite IH; lia.
Qed.

#[global]
Instance Subadditive_pot_list (A : AA)
  : Subadditive (A := AA_listA A) pot_list.
Proof.
  constructor.
  - reflexivity.
  - intros [] []; cbn; try rewrite subadditive_sizeX'; lia.
Qed.

Lemma let_cost {A B C : AA} {a : A} {b : B} {c : C} (f : DF a b) (g : DF (a, b) c)
    (pre : approx A -> nat) (mid : approx B -> nat) (post : approx C -> nat) (m0 m n : nat)
    `{!Subadditive pre}
    (_ : has_cost_ f m0 pre mid m)
    (_ : has_cost_ g m (pre +++ mid) post n)
  : has_cost_ (DF.let_ f g) m0 pre post n.
Proof.
Admitted.

(*
  f : G -> A

  g : G * A -> B

  n + post b'
  >=
  m + cost (g' b') + pre (fst (g' b')) + mid (snd (g' b'))
  >=
  m0 + cost (g' b') + cost (f' ...) + pre (fst (g' b')) + pre (f' ...)
  >=
  m0 + cost ... + pre (lub (fst (g' b')) (f' ...))
*)

Lemma tick_cost {A B : AA} {a : A} {b : B} (f : DF a b)
    m pre post n
  : has_cost_ f (S m) pre post n ->
    has_cost_ (DF.tick f) m pre post n.
Admitted.

Lemma match_list_nil_cost {G A B : AA} {P : list A -> B} {g : G}
    `{!AutoDF g []}
    (NIL : DF g (P []))
    (CONS : forall x ys, DF (g, x, ys) (P (x :: ys)))
    m pre post n
  : has_cost_ NIL m pre post n ->
    has_cost_ (match_list (var []) NIL CONS) m pre post n.
Admitted.

Definition measure_list_uncons {A  : AA} (x : A) (xs : list A) pot0 pot_hd pot_tl : Prop
  := forall (x' : approx A) (xs' : approx (AA_listA A)), x' `is_approx` x -> xs' `is_approx` xs ->
      pot0 (Thunk (ConsA (Thunk x') xs')) <= pot_hd x' + pot_tl xs'.

Lemma match_list_cons_cost {G A B : AA} {P : list A -> B} {g : G} (x : A) (xs : list A)
    `{!AutoDF g (x :: xs)}
    (NIL : DF g (P []))
    (CONS : forall x ys, DF (g, x, ys) (P (x :: ys)))
    m pre pot0 m' pot_hd pot_tl post n
  : has_cost_ (var (g := g) (x :: xs)) m pre pot0 m' ->
    measure_list_uncons x xs pot0 pot_hd pot_tl ->
    has_cost_ (CONS x xs) m ((pre +++ pot_hd) +++ pot_tl) post n ->
    has_cost_ (match_list (var (x :: xs)) NIL CONS) m pre post n.
Admitted.

Lemma pot_list_uncons {A : AA} (x : A) (xs : list A)
  : measure_list_uncons x xs pot_list (fun _ => 3) pot_list.
Proof.
  red. intros x' xs' Ax Axs; inv Axs; cbn; lia.
Qed.

Lemma consD_cost {G A : AA} {g : G} {x : A} {xs : list A}
    {xD : DF g x} {xsD : DF g xs} {m1 m2 m pre n}
    `{!Subadditive pre}
  : m1 + m2 <= m ->
    has_cost_ xD m1 pre zero 3 ->
    has_cost_ xsD m2 pre pot_list n ->
    has_cost_ (consD xD xsD) m pre pot_list n.
Admitted.

Lemma nilD_cost {G A : AA} {g : G} {pre n}
    `{!Subadditive pre}
  : has_cost_ (a := g) (nilD (a := A)) 0 pre pot_list n.
Proof.
Admitted.

Theorem insTree_cost (t : Tree) (ts : list Tree)
  : valid_Trees ts ->
    has_cost_ (insTreeDF t ts) 0 (zero +++ pot_list) pot_list insert_budget.
Proof.
  revert t; induction ts; intros t Vts.
  - unfold insTreeDF.
    apply tick_cost.
    apply match_list_nil_cost.
    apply (consD_cost (m1 := 1) (m2 := 0)).
    + lia.
    + admit.
    + apply nilD_cost.
  - unfold insTreeDF.
    apply tick_cost.
    apply match_list_cons_cost with (pot0 := pot_list) (pot_hd := fun _ => 3) (pot_tl := pot_list) (m' := 1).
    + admit.
    + apply pot_list_uncons.
    + apply let_cost with (mid := zero) (m := 0).
Admitted.

Lemma nodeD_cost_zero {r : AA} {s : r} (n x : nat) (ts : list Tree)
    {pre : approx r -> nat}
    `{!Subadditive pre}
    (nD : DF s n) (xD : DF s x) (tsD : DF s ts)
  : has_cost_ nD 0 pre zero 0 ->
    has_cost_ xD 0 pre zero 0 ->
    has_cost_ tsD 0 pre zero 0 ->
    has_cost_ (nodeD nD xD tsD) 0 pre zero 0.
Proof.
Admitted.

Theorem insert_cost (x : A) (h : Heap)
  : valid_Heap h ->
    has_cost_ (insertDF x h) 0 (zero +++ pot_heap) pot_heap insert_budget.
Proof.
  intros Vh.
  change insert_budget with (0 + insert_budget).
  apply let_cost with (mid := zero) (m := 0); [ admit | |].
  { apply nodeD_cost_zero.
    + admit.
    + admit.
    + admit.
    + admit. }
  change insert_budget with (0 + insert_budget).
  apply let_cost with (mid := zero) (m := 0); [ admit | |].
  { admit. }
  assert (HH : has_cost_ (insTreeDF (Node 0 x []) (trees h)) 0 (zero +++ pot_list) pot_list insert_budget).
  { apply insTree_cost. assumption. }
  admit.
Admitted.

(*
Below: TODO
*)

Fixpoint mergeAux (trs1 trs2 : list Tree) : list Tree :=
  match trs1 with
  | [] => trs2
  | t1 :: trs1' => let fix merge_trs1 trsR :=
    match trsR with
    | [] => trs1
    | t2 :: trs2' =>
      match Nat.compare (rank t1) (rank t2) with
      | Lt => t1 :: (mergeAux trs1' trsR)
      | Eq => insTree (link t1 t2) (mergeAux trs1' trs2')
      | Gt => t2 :: merge_trs1 trs2'
      end
    end in 
    merge_trs1 trs2
  end.

(*
Canonical AABComparison : AA :=
  {| carrier := comparison |}.

Definition if_ {a b : AA} {x : a} {cond : bool}
  {f : bool -> b}
  (i : DF x cond)
  (thn : DF x (f true))
  (els : DF x (f false))
  : DF x (f cond).
Proof. refine TODO. Defined.  

(* Encoding of [Nat.compare] *)
Definition natCompare {a b : AA} {c : a} {x y : nat} 
  {f : comparison -> b}
  (nats : DF c (x, y))
  (Lt_ : DF c (f Lt))
  (Eq_ : DF c (f Eq))
  (Gt_ : DF c (f Gt))
  : DF c (f (Nat.compare x y)).
Proof. refine TODO. Defined.

Fixpoint mergeAuxDF (trs1 trs2 : list Tree) : DF (trs1, trs2) (mergeAux trs1 trs2).
Proof.
  refine ((TODO : DF (trs1, trs2) (trs2, trs1)) >>>
    (match_list (f := fun trs => mergeAux trs trs2)
    _ (fun t1 trs1' => _))).
  - cbn. refine TODO.
  - refine ((TODO: DF (trs2, t1, trs1') (t1, trs1', trs2)) >>>
    match_list (f := fun trs => mergeAux _ trs)
    _ (fun t2 trs2' => _)).
    + cbn [mergeAux]. refine (consD TODO TODO).
    + cbn [mergeAux]. refine (natCompare 
      (f := fun c => match c with
        | Lt => _
        | Eq => _
        | Gt => _
        end)
        _
        _
        _ 
        _).
        * refine TODO.
        * refine TODO.
        * refine TODO.
        * refine TODO. 
Defined.

Definition merge (hp1 hp2 : Heap) : Heap :=
  MkHeap (mergeAux (trees hp1) (trees hp2)).

Definition mergeDF {hp1 hp2} : DF (hp1, hp2) (merge hp1 hp2).
Proof.
  refine (letDF (TODO >>> @treesD hp1) _).
  refine (letDF (TODO >>> @treesD hp2) _).
  refine (letDF (TODO >>> mergeAuxDF (trees hp1) (trees hp2)) _).
  refine (proj2DF >>> MkHeapD _).
Defined.

Fixpoint removeMinAux (ts : list Tree) := 
  match ts with
  | [] => None
  | t :: ts' => match removeMinAux ts' with
    | None => Some (t, [])
    | Some (t', ts'') => if leb (root t) (root t')
      then Some (t, ts')
      else Some (t', t :: ts'')
    end
  end.

Canonical AAoption (a : AA) : AA :=
  {| carrier := option a |}.

(* Encoding of match on options *)
Definition match_option {a b c : AA} {g : b} {f : option a -> c} {xM : option a}
    (NONE : DF g (f None))
    (SOME : forall x, DF (g, x) (f (Some x)))
  : DF (g, xM) (f xM) :=
  match xM with
  | None => TODO >>> NONE
  | Some x => TODO >>> (SOME x)
  end.

(* Encoding of None *)
Definition noneD {a b : AA} {x : a} : DF x (None (A := b)).
Proof. refine TODO. Defined.

(* Encoding of (Some _) *)
Definition someD {r a : AA} {s : r} {x : a} {xM : option a} (sD : DF s x)
  : DF s (Some x).
Proof. refine TODO. Defined.

Fixpoint removeMinAuxDF {ts} : DF ts (removeMinAux ts).
Proof.
  refine (TODO >>> 
    match_list (f := fun ts => removeMinAux ts) (g := ts) _ (fun t ts' => _)). (*TODO*)
  - cbn. refine TODO.
  - cbn. refine TODO.
Defined.

Definition removeMinTree (hp : Heap) 
  : option ((Tree) * (Heap)) :=
  match removeMinAux (trees hp) with
  | Some (t, ts) => Some (t, MkHeap ts)
  | None => None
  end.

Definition removeMinTreeDF {hp} : DF hp (removeMinTree hp).
Proof.
  refine (letDF (TODO >>> @treesD hp) _).
  refine (letDF (TODO >>> removeMinAuxDF) _).
  refine (TODO >>> match_option 
    (f := fun pM => match pM with
      | None => None
      | Some (t, ts) => Some (t, MkHeap ts) 
      end)
    (g := hp) (*TODO*)
    (xM := removeMinAux (trees hp))
    _ (fun x => _)). 
  - refine noneD.
  - refine TODO. Unshelve. cbn. apply trees. assumption. (*TODO*)
Defined.

Definition findMin (hp : Heap)
  : option A :=
  match removeMinTree hp with
  | None => None
  | Some (t, _) => Some (root t)
  end.

Definition findMindDF {hp} : DF hp (findMin hp).
Proof.
  refine (TODO >>> match_option 
    (f := fun pM => match pM with
      | None => None
      | Some (t, _) => Some (root t) 
  end)
  (g := hp) (*TODO*)
  (xM := removeMinTree hp)
  _ (fun x => _)). 
  - refine noneD.
  - refine TODO. (*TODO*)
Defined.

Definition deleteMin (hp : Heap)
  : Heap :=
  match removeMinTree hp with
  | None => MkHeap []
  | Some (Node r v c, ts) =>
    merge (MkHeap (rev c)) ts
  end.
  
Definition deleteMindDF {hp} : DF hp (deleteMin hp).
Proof.
  refine (TODO >>> match_option 
    (f := fun pM => match pM with
      | None => MkHeap []
      | Some (Node r v c, ts) =>
        merge (MkHeap (rev c)) ts
    end)
  (g := hp) (*TODO*)
  (xM := removeMinTree hp)
  _ (fun x => _)). 
  - refine TODO.
  - refine TODO. (*TODO*)
Defined.
*)
