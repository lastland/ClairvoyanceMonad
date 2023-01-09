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
From Clairvoyance Require Import Core Approx ApproxM List Misc BankersQueue Tick.

Record AA : Type :=
  { carrier :> Type
  (* ; approx : Type *)
  }.

Canonical AAProd (a b : AA) : AA :=
  {| carrier := (a * b)%type
  (* ;  approx :=(approx a * approx b)%type *)
  |}.

Canonical AAList (a : AA) : AA :=
  {| carrier := list a
  (* ;  approx := listA (approx a) *)
  |}.

Infix "**" := AAProd (at level 40).

Parameter TODO : forall {A : Type}, A.

Module Import DF.

Definition DF {a b : AA} (x' : a) (y' : b) : Type. Admitted.
Definition id {a : AA} {x' : a} : DF x' x'. Admitted.
Definition compose {a b c : AA} {x' : a} {y' : b} {z' : c}
  (f : DF x' y') (g : DF y' z') : DF x' z'.
Admitted.

Module Notations.

Declare Scope df_scope.
Delimit Scope df_scope with df.
Bind Scope df_scope with DF.

Infix ">>>" := compose (left associativity, at level 40) : df_scope.

End Notations.

Definition proj1DF {a b : AA} {xy' : a ** b} : DF xy' (fst xy'). Admitted.
Definition proj2DF {a b : AA} {xy' : a ** b} : DF xy' (snd xy'). Admitted.

Definition pairDF {a b c : AA} {x' : a} {y' : b} {z' : c} (f : DF x' y') (g : DF x' z')
  : DF x' (y', z'). Admitted.

(* let y := f x in
   g (x, y) *)
Definition letDF {a b c : AA} {x : a} {y : b} {z : c}
  : DF x y ->  (* f *)
    DF (x, y) z -> (* g *)
    DF x z.
Admitted.

Definition tickDF {a b : AA} {x' : a} {y' : b} : DF x' y' -> DF x' y'.
Admitted.

Definition nilD {a b : AA} {x : a} : DF x (nil (A := b)).
Admitted.

Definition consD {r a : AA} {s : r} {x : a} {xs : list a} (xD : DF s x) (xsD : DF s xs)
  : DF s (x :: xs).
Admitted.

End DF.

Import DF.Notations.

(* Pure implementation *)
Definition A := nat.

Inductive Tree : Type := 
  | Node : nat -> A -> list Tree -> Tree.

Canonical AAnat : AA :=
  {| carrier := nat |}.

Definition match_list {a b c : AA} {g : b} {f : list a -> c} {xs : list a}
    (NIL : DF g (f nil))
    (CONS : forall x xs', DF (g, x, xs') (f (cons x xs')))
  : DF (g, xs) (f xs) :=
  match xs with
  | nil => TODO >>> NIL
  | cons x xs' => TODO >>> (CONS x xs')
  end.

Canonical AAA : AA :=
  {| carrier := A |}.

Canonical AATree : AA :=
  {| carrier := Tree |}.

Definition nodeD {r : AA} {s : r} {n : nat} {x : A} {ts : list Tree}
    (nD : DF s n) (xD : DF s x) (tsD : DF s ts)
  : DF s (Node n x ts).
Admitted.

Definition match_Tree {a c : AA}
    {g : c} {t : Tree} {f : Tree -> a}
    (NODE : forall n x ts, DF (g, n, x, ts) (f (Node n x ts)))
  : DF (g, t) (f t) :=
  match t with
  | Node n x ts => TODO >>> NODE n x ts
  end.

Definition link (t1 t2 : Tree) : Tree :=
  match (t1, t2) with
  | (Node r1 v1 c1, Node r2 v2 c2) => if leb v1 v2
    then Node (r1 + 1) v1 (t2 :: c1)
    else Node (r2 + 1) v2 (t1 :: c2)
  end.

Canonical AABool : AA :=
  {| carrier := bool |}.

Definition if_ {a b : AA} {x : a} {cond : bool}
  {f : bool -> b}
  (i : DF x cond)
  (thn : DF x (f true))
  (els : DF x (f false))
  : DF x (f cond).
Admitted.

Definition le_ {x y : nat} : DF (x, y) (x <=? y).
Admitted.

Definition lt_ {x y : nat} : DF (x, y) (x <? y).
Admitted.

Definition add1 {x : nat} : DF x (x + 1).
Admitted.

#[local] Open Scope df.

Definition linkDF {t1 t2} : DF (t1, t2) (link t1 t2).
Proof.
  refine (
  (TODO : DF (t1, t2) (t2, t1)) >>>
  match_Tree (f := fun t1 => link t1 t2)
    (fun r1 v1 c1 =>
  (TODO : DF (t2, r1, v1, c1) (r1, v1, c1, t2)) >>>
  match_Tree (f := fun t2 => link _ t2)
    (fun r2 v2 c2 => _
  )))%df.
  cbn.
  refine (
    if_ (f := fun b => if b then _ else _)
        _
        _
        _).
  - refine (TODO >>> le_).
  - refine (nodeD _ _ _).
    + refine (TODO >>> add1).
    + refine TODO.
    + refine (consD _ _).
      * refine (nodeD _ _ _).
        ** refine TODO.
        ** refine TODO.
        ** refine TODO.
      * refine TODO.
  - refine (nodeD _ _ _).
    + refine (TODO >>> add1).
    + refine TODO.
    + refine (consD _ _).
      * refine (nodeD _ _ _).
        ** refine TODO.
        ** refine TODO.
        ** refine TODO.
      * refine TODO.
Defined.

Record Heap : Type := MkHeap
  { trees : list Tree }.

Canonical AAHeap : AA :=
  {| carrier := Heap |}.

Definition MkHeapD (ts : list Tree) : DF ts (MkHeap ts).
Admitted.

Definition treesD {h : Heap} : DF h (trees h).
Admitted.

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

Definition root (t : Tree) : A :=
  match t with
  | (Node r v c) => v
  end.

(*Assumes t has rank <= the rank of the first element of ts (if any).*)
Fixpoint insTreeAux (t : Tree) (ts : list Tree) : list Tree :=
  match ts with
  | [] => [t]
  | t' :: ts' => if rank t <? rank t'
    then t :: ts
    else insTreeAux (link t t') ts' (*t and t' should have the same rank*)
  end.

Fixpoint insTreeAuxDF (t : Tree) (ts : list Tree)
  : DF (t, ts) (insTreeAux t ts).
Proof.
  refine (match_list (f := fun ts => insTreeAux t ts)
    _ (fun t' ts' => _)).
  - cbn. refine (consD id nilD).
  - cbn [insTreeAux].
    refine (if_ (f := fun b => if b then _ else _)
              _ _ _).
    + refine (TODO >>> lt_).
    + refine (consD TODO (consD TODO TODO)).
    + refine (letDF (TODO >>> @linkDF t t') _).
      refine (TODO >>> insTreeAuxDF (link t t') ts').
Defined.

Definition insTree (t : Tree) (hp : Heap) : Heap :=
  MkHeap (insTreeAux t (trees hp)).

Definition insTreeDF {t hp} : DF (t, hp) (insTree t hp).
Proof.
  refine (letDF (TODO >>> @treesD hp) _).
  refine (letDF (TODO >>> insTreeAuxDF t (trees hp)) _).
  refine (proj2DF >>> MkHeapD _).
Defined.

Definition insert (x : A) (hp : Heap) 
  : Heap :=
  insTree (Node 0 x []) hp.

Definition insertDF {x hp} : DF (x, hp) (insert x hp).
Proof.
  refine (letDF (_ : DF _ (Node 0 x [])) _).
  - refine (nodeD TODO TODO nilD).
  - refine (TODO >>> insTreeDF).
Defined.

Fixpoint mergeAux (trs1 trs2 : list Tree) : list Tree :=
  match trs1 with
  | [] => trs2
  | t1 :: trs1' => let fix merge_trs1 trsR :=
    match trsR with
    | [] => trs1
    | t2 :: trs2' =>
      match Nat.compare (rank t1) (rank t2) with
      | Lt => t1 :: (mergeAux trs1' trsR)
      | Eq => trees (insTree (link t1 t2) (MkHeap (mergeAux trs1' trs2')))
      | Gt => t2 :: merge_trs1 trs2'
      end
    end in 
    merge_trs1 trs2
  end.

Definition merge (hp1 hp2 : Heap) : Heap :=
  MkHeap (mergeAux (trees hp1) (trees hp2)).

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

Definition removeMinTree (hp : Heap) 
  : option ((Tree) * (Heap)) :=
  match removeMinAux (trees hp) with
  | Some (t, ts) => Some (t, MkHeap ts)
  | None => None
  end.

Definition findMin (hp : Heap)
  : option A :=
  match removeMinTree hp with
  | None => None
  | Some (t, _) => Some (root t)
  end.

Definition deleteMin (hp : Heap)
  : Heap :=
  match removeMinTree hp with
  | None => MkHeap []
  | Some (Node r v c, ts) =>
    merge (MkHeap (rev c)) ts
  end. 

(* Monadic implementation *)

Inductive TreeA : Type := 
  | NodeA : nat -> A -> T (listA TreeA) -> TreeA.

Record HeapA : Type := MkHeapA
  { treesA : T (listA TreeA) }.

Definition mkHeapA (trs : T (listA TreeA)) : M HeapA :=
  ret (MkHeapA trs).

Definition emptyA : M HeapA :=
  mkHeapA (Thunk NilA).

Definition linkA (t1 t2 : T TreeA) : M TreeA :=
  tick >>
  let! t1' := force t1 in
  let! t2' := force t2 in
  match (t1', t2') with
  | (NodeA r1 v1 c1, NodeA r2 v2 c2) => if leb v1 v2
    then ret (NodeA (r1 + 1) v1 (Thunk (ConsA t2 c1)))
    else ret (NodeA (r2 + 1) v2 (Thunk (ConsA t1 c2)))
  end.

Definition rankA (t : T TreeA) : M nat :=
  let! tval := force t in
  match tval with
  | (NodeA r v c) => ret r
  end.

Definition rootA (t : T TreeA) : M A :=
  let! tval := force t in
  match tval with
  | (NodeA r v c) => ret v
  end.

Fixpoint insTreeAuxA (t1 : T TreeA) (ts : listA TreeA) : M (listA TreeA) :=
match ts with
 | NilA => ret ((ConsA t1 (Thunk NilA)))
 | ConsA t2 ts' => 
    let! r1 := rankA t1 in
    let! r2 := rankA t2 in
    if (r1 <? r2)
      then ret (ConsA t1 (Thunk ts))
      else
        let! linked := linkA t1 t2 in
        forcing ts' (fun ts'' =>
        insTreeAuxA (Thunk linked) ts'')
end.

Definition insTreeA (t : T TreeA) (hp : HeapA) : M HeapA :=
  let! trs := force (treesA hp) in
  bind (insTreeAuxA t trs) (fun ts => ret (MkHeapA (Thunk ts))).

Definition insertA (x : A) (hp : HeapA) : M HeapA :=
  insTreeA (Thunk (NodeA 0 x (Thunk (NilA)))) hp.

Fixpoint mergeAuxA (trs1 trs2 : listA TreeA) : M (listA TreeA) :=
  match trs1 with
  | NilA => ret trs2
  | ConsA t1 trs1' => let fix merge_trs1 trsR : M (listA TreeA):=
    match trsR with
    | NilA => ret trs1
    | ConsA t2 trs2' =>
      forcing t1 (fun t1' => forcing t2 (fun t2' =>
      let! r1 := rankA t1 in
      let! r2 := rankA t2 in
      forcing trs1' (fun trs1'' =>
      forcing trs2' (fun trs2'' =>
      match Nat.compare r1 r2 with
      | Lt => bind (mergeAuxA trs1'' trsR) (fun merged =>
        ret (ConsA t1 (Thunk merged)))
      | Eq => 
        bind (mergeAuxA trs1'' trs2'') (fun merged =>
        bind (linkA t1 t2) (fun linked =>
        bind (insTreeA (Thunk linked) (MkHeapA (Thunk merged))) (fun inserted => 
        forcing (treesA inserted) (fun trs =>
        ret trs))))
      | Gt => bind (merge_trs1 trs2'') (fun merged =>
        ret (ConsA t2 (Thunk merged)))
      end))))
    end in 
    merge_trs1 trs2
  end.

Definition mergeA (hp1 hp2 : HeapA) : M HeapA :=
  let! trs1 := force (treesA hp1) in
  let! trs2 := force (treesA hp2) in
  bind (mergeAuxA trs1 trs2) (fun trs => mkHeapA (Thunk trs)).

Definition removeMinTreeAuxA :
  T TreeA ->
  T (option ((T TreeA) * (HeapA))) ->
  M (option ((T TreeA) * (HeapA))) :=
  fun t => (fun acc => 
  let! accVal := force acc in
  match accVal with
  | None => ret (Some (t, MkHeapA (Thunk NilA)))
  | Some (t', hp) => 
    let! r := rootA t in
    let! r' := rootA t' in
    if r <? r'
      then bind (insTreeA t' hp) (fun hp' => ret (Some (t, hp')))
      else ret (Some (t', MkHeapA (Thunk (ConsA t (treesA hp)))))
  end).

Definition removeMinTreeA (hp : HeapA) : M (option ((T TreeA) * (HeapA))) :=
  foldrA removeMinTreeAuxA (Thunk None) (treesA hp).

Definition findMinA (hp : HeapA) : M (option A) :=
  let! minPair := removeMinTreeA hp in
  match minPair with
  | None => ret None
  | Some (t, _) => bind (rootA t) (fun x => ret (Some x))
  end.

Definition deleteMinA (hp : HeapA) : M (HeapA) :=
  let! minPair := removeMinTreeA hp in
  match minPair with
  | None => ret (MkHeapA (Thunk NilA))
  | Some (t, ts) =>
    let! (NodeA r v c) := force t in
    bind (revA c)
      (fun children => mergeA (MkHeapA (Thunk children)) ts)
  end.

(** * Approximation structure for [HeapA] *)

(** [less_defined], [exact], [lub] *)

#[global] Existing Instance LessDefined_list.
#[local] Existing Instance Exact_id | 1.
#[local] Existing Instance LessDefined_id | 100.
#[local] Existing Instance PreOrder_LessDefined_id | 100.
#[local] Existing Instance ExactMaximal_id | 100.
#[local] Existing Instance Exact_T | 100.
#[local] Existing Instance ExactMaximal_T | 100.

Inductive less_defined_TreeA : LessDefined TreeA :=
  | LessDefined_NodeA (r : nat)
    (v : A) (c1 c2 : T (listA TreeA)) : 
    c1 `less_defined` c2 ->
    less_defined_TreeA (NodeA r v c1) (NodeA r v c2).

#[local] Instance LessDefined_TreeA : LessDefined TreeA :=
  less_defined_TreeA.

Record less_defined_HeapA (hp1 hp2 : HeapA) : Prop :=
  { ld_trs : less_defined (treesA hp1) (treesA hp2) }.

#[global] Instance LessDefined_HeapA : LessDefined HeapA :=
  less_defined_HeapA.

#[global] Hint Constructors less_defined_TreeA : core.

#[global]
Instance Rep_HeapA : Rep HeapA (T (listA TreeA)) :=
  {| to_rep := fun hp => treesA hp
  ;  from_rep := fun trs => MkHeapA trs
  |}.

#[global] Instance RepLaw_HeapA : RepLaw HeapA _.
Proof.
  constructor.
  - intros trs; reflexivity.
  - intros []; reflexivity.
Qed.
  
#[global] Instance LessDefinedRep_HeapA : LessDefinedRep HeapA _.
Proof.
  intros [] []; cbn; firstorder.
Qed.

#[global] Instance PreOrder_HeapA : PreOrder (less_defined (a := HeapA)).
Proof. Admitted.

#[global] Instance PreOrder_TreeA : PreOrder (less_defined (a := TreeA)).
Proof. Admitted.

Fixpoint treeConvert (t : Tree) : TreeA :=
  match t with
  | (Node r v c) => NodeA r v (exact (map treeConvert c))
  end.

#[global] Instance Exact_Tree : Exact Tree TreeA :=
  treeConvert.

Definition treeListConvert (trs : list Tree) : listA TreeA :=
  match trs with
  | [] => NilA
  | t :: trs' => ConsA (Thunk (exact t)) (exact (map exact trs'))
  end.

#[global] Instance Exact_Maximal_TreeA : ExactMaximal TreeA Tree.
Proof. Admitted.

#[global] Instance Exact_ListTree : Exact (list Tree) (listA TreeA) :=
  treeListConvert.

#[global] Instance Exact_Heap : Exact Heap HeapA :=
  fun hp => MkHeapA (exact (trees hp)).

#[global] Instance ExactMaximal_HeapA : ExactMaximal HeapA Heap.
Proof. Admitted.

(*TODO: This is currently a shallow check but it should
  also check the trees.*)
#[global] Instance Lub_HeapA : Lub HeapA :=
  fun hp1 hp2 =>
    MkHeapA (lub_T (Lub_listA) (treesA hp1) (treesA hp2)).

#[global] Instance LubRep_HeapA : LubRep HeapA (T (listA TreeA)).
Proof.
  intros [] []; reflexivity.
Qed.
    
#[global] Instance LubLaw_HeapA : LubLaw HeapA.
Proof.
Admitted.

Lemma mkHeapA_mon (trs1 trs2 : T (listA TreeA)) :
    trs1 `less_defined` trs2 ->
    mkHeapA trs1 `less_defined` mkHeapA trs2.
Proof.
  intros; subst; unfold mkHeapA; solve_mon.
Qed.

#[global] Hint Resolve mkHeapA_mon : mon.

(*[TreeA], [HeapA], [linkA], [rankA], 
    [rootA], [insTreeA], [insertA], [mergeA], [removeMinTreeA], [findMinA], [deleteMinA]*)

(*Monotoicity*)

Lemma prod_mon {a b} `{LessDefined a} `{LessDefined b} (x x': a) (y y' : b) :
  x `less_defined` x' ->
  y `less_defined` y' ->
  (x, y) `less_defined` (x', y').
Proof.
  intros. solve_mon.
Qed.

Lemma insTreeAuxA_mon (t1 t1' : T TreeA) (ts ts' : listA TreeA) :
  t1 `less_defined` t1' ->
  ts `less_defined` ts' ->
  insTreeAuxA t1 ts `less_defined` insTreeAuxA t1' ts'.
Proof.
Admitted.

Lemma linkA_mon (t1A t1A' t2A t2A' : T TreeA)
  : t1A `less_defined` t1A' ->
    t2A `less_defined` t2A' ->
    t1A `less_defined` t2A' ->
    t2A `less_defined` t1A' ->
    linkA t1A t2A `less_defined` linkA t1A' t2A'.
    Proof. 
  intros. apply bind_mon; try reflexivity. intros.
  apply bind_mon. 
  (*Problem: bind_mon only gives us one assumption, need several*)
  - apply force_mon. assumption. 
  - intros. admit.
Admitted.

Import Tick.Notations.

(*Demand functions*)

Definition linkD (t1 t2 : Tree) (outD : TreeA) : Tick ((T TreeA) * (T TreeA)) :=
  Tick.tick >>
  match t1, t2, outD with
  | Node r1 v1 c1, Node r2 v2 c2, NodeA r1A v1A (Thunk (ConsA (Thunk (NodeA r2A v2A c2A)) cs1)) => 
    if (v1 <=? v2)
      then Tick.ret (Thunk (NodeA r1 v1 cs1), Thunk (NodeA r2 v2 c2A))
      else Tick.ret (Thunk (NodeA r1 v1 c2A), Thunk (NodeA r2 v2 cs1))
  | _,_,_ => bottom
  end.

Definition rankD (t : Tree) : Tick (T TreeA) :=
  Tick.tick >>
  match t with
  | Node r v c => Tick.ret (Thunk (NodeA r v Undefined))
  end.

Definition rootD (t : Tree) : Tick (T TreeA) :=
  Tick.tick >>
  match t with
  | Node r v c => Tick.ret (Thunk (NodeA r v Undefined))
  end.

(*(*Assumes t has rank <= the rank of the first element of ts (if any).*)
Fixpoint insTreeAux (t : Tree) (ts : list Tree) : list Tree :=
  match ts with
  | [] => [t]
  | t' :: ts' => if rank t <? rank t'
    then t :: ts
    else insTreeAux (link t t') ts' (*t and t' should have the same rank*)
  end.*)

Fixpoint insTreeAuxD (t : Tree) (trs : list Tree) (outD : listA TreeA) 
: Tick ((T TreeA) * (T (listA TreeA))) :=
  match t, trs, outD with 
  | Node r v c, [], ConsA (Thunk (NodeA rOut vOut cOut)) (Thunk NilA) =>
    Tick.ret (Thunk (NodeA r v cOut), Thunk NilA)
  | Node r v c, x :: xs, ConsA (Thunk (NodeA rOut vOut cOut)) (Thunk trsOut) => 
    if (r <=? (rank x))
    then Tick.ret (Thunk (NodeA r v cOut), (Thunk trsOut))
    else 
      match (insTreeAuxD (link t x) xs outD) with
      | Tick.MkTick _ (t', recTrs) =>
        let+ t'' := thunkD (linkD t x) t' in
        match t'' with
          | (t1, t2) => Tick.ret (t1, Thunk (ConsA t2 recTrs))
        end
      end
  | _, _, _ => bottom
  end.

(*Definition insTreeD (t : T TreeA) (outD : HeapA) : Tick ((T TreeA) * (T HeapA)) :=
  Tick.tick >>
  match t, (treesA outD) with
  | (Thunk t), (Thunk trs) => 
    let+ (t', trs') := insTreeAuxD t trs in
    Tick.ret (t', Thunk (MkHeapA trs'))
  | _, _ => bottom
  end.

Definition insertD (x : A) (outD : HeapA) :=
  insTreeD (Thunk (NodeA 0 x (Thunk (NilA)))) outD.*)

Fixpoint mergeAuxD (trs1 trs2 : listA TreeA ) (outD : listA TreeA)
  : Tick ((T (listA TreeA)) * (T (listA TreeA))) :=
  match trs1, trs2, outD with
  | NilA, _, _ => Tick.ret (Thunk NilA, Thunk outD)
  | _, NilA, _ => Tick.ret (Thunk outD, Thunk NilA)
  | ConsA (Thunk (NodeA r1 v1 c1)) trs1', ConsA (Thunk (NodeA r2 v2 c2)) trs2', ConsA o1 os1 =>
    match (Nat.compare r1 r2), os1, trs1', trs2' with
    | Eq, Thunk (ConsA o2 (Thunk os1')), Thunk trs1'', Thunk trs2'' => 
      Tick.bind (mergeAuxD trs1'' trs2'' os1') (fun rec =>
        match rec with
        | (rec1, rec2) => 
          Tick.ret (Thunk (ConsA (Thunk (NodeA r1 v1 c1)) rec1), Thunk (ConsA (Thunk (NodeA r2 v2 c2)) rec2))
        end)
    | Lt, Thunk os1', Thunk trs1'', _ =>
      Tick.bind (mergeAuxD trs1'' trs2 os1') (fun rec =>
      match rec with
      | (rec1, rec2) => Tick.ret (Thunk (ConsA (Thunk (NodeA r1 v1 c1)) rec1), Thunk (ConsA (Thunk (NodeA r2 v2 c2)) rec2))
      end)
    | Gt, Thunk os1', _, Thunk trs2'' =>
      Tick.bind (mergeAuxD trs1 trs2'' os1') (fun rec =>
        match rec with
        | (rec1, rec2) => Tick.ret (Thunk (ConsA (Thunk (NodeA r1 v1 c1)) rec1), Thunk (ConsA (Thunk (NodeA r2 v2 c2)) rec2))
        end)
    | _, _, _, _ => bottom
    end
  | _, _, _ => bottom
  end.

Definition mergeD (hp1 hp2 : HeapA) (outD : HeapA) : Tick ((T HeapA) * (T HeapA)) :=
  match treesA hp1, treesA hp2, treesA outD with
  | Thunk trs1, Thunk trs2, Thunk outTrs => 
    let+ (rec1, rec2) := mergeAuxD trs1 trs2 outTrs in
      Tick.ret (Thunk (MkHeapA rec1), Thunk (MkHeapA rec2))
  | Undefined, Undefined, Undefined => Tick.ret (Undefined, Undefined)
  | _, _, _ => bottom
  end.

(*TODO: does not use outD*)
Definition removeMinTreeD (hp : Heap) (outD : option ((T TreeA) * (HeapA))) : Tick HeapA :=
  Tick.ret (MkHeapA (Thunk (treeListConvert (trees hp)))). (* removeMin must traverse the whole heap. *)

(*TODO: does not use outD*)
Definition findMinD (hp : Heap) (outD : option A) : Tick HeapA :=
  Tick.tick >>
  Tick.ret (MkHeapA (Thunk (treeListConvert (trees hp)))). (* findMin must traverse the whole heap. *)

(*TODO: does not use outD*)
Definition deleteMinD (hp : Heap) (outD : HeapA) : Tick HeapA :=
  Tick.tick >>
  Tick.ret (MkHeapA (Thunk (treeListConvert (trees hp)))). (* deleteMin must traverse the whole heap. *)

Ltac invert_less_defined := match goal with
| H0: NodeA _ _ _ `less_defined` _ |- _ => inv H0
| H0: ?t `less_defined` _ |- context [match ?t with _ => _ end]
  => inv H0
end.

Lemma linkD_approx (t1 t2 : Tree) (outD : TreeA)
  : outD `is_approx` link t1 t2 -> 
  Tick.val (linkD t1 t2 outD) `is_approx` (t1, t2).
Proof.
  unfold link, linkD.
  intros Hout. 
  destruct outD eqn: HoutD; subst.
  destruct t1 eqn: Ht1; subst.
  destruct t2 eqn: Ht2; subst.
  destruct (a0 <=? a1) eqn: Ha; subst;
  inv Hout; repeat invert_less_defined; solve_approx.
Qed.

(*Fixpoint insTreeAuxD (t : TreeA) (outD : listA TreeA) 
: Tick ((T TreeA) * (T (listA TreeA))) :=
  match t, outD with 
  | NodeA r' v' c', ConsA (Thunk (NodeA r0 v0 c0)) trs' => 
    if (r0 =? r')
    then Tick.ret (Thunk t, trs')
    else match trs' with
      | Undefined => bottom
      | Thunk trs'' =>
        match (insTreeAuxD t trs'') with
        | Tick.MkTick _ (_, recTrs) =>
          Tick.ret (Thunk t, Thunk (ConsA (Thunk (NodeA r0 v0 c0)) recTrs))
        end
      end
  | _, _ => bottom
  end.*)

(*Lemma insTreeAuxD_approx (t : Tree) (ts : list Tree) (outD : listA TreeA)
  : outD `is_approx` insTreeAux t ts -> 
  Tick.val (insTreeAuxD t ts outD) `is_approx` (t, ts).
Proof.
  revert t outD.
  induction ts; simpl; intros t outD Hout.
  - inv Hout. destruct t eqn: Ht. simpl.
    repeat invert_less_defined.
    + solve_approx.
    + rewrite Nat.eqb_refl. solve_approx.
  - destruct (rank t <? rank a) eqn : Hrank.
    + inv Hout. simpl. destruct t eqn: Ht. 
      repeat invert_less_defined.
      * solve_approx.
      * rewrite Nat.eqb_refl. solve_approx.
      * rewrite Nat.eqb_refl. solve_approx.
    + apply IHts in Hout. 
      inv Hout. simpl in *.
      inv fst_rel.
      * admit.
      * apply linkD_approx in H1. 
        destruct t eqn: Ht.
        destruct outD eqn: HoutD.
      * solve_approx.
      * destruct x1 eqn: Hx1.
        -- destruct x eqn: Hx. 
  intros Hout. 
  destruct outD eqn: HoutD; subst.
  destruct t1 eqn: Ht1; subst.
  destruct t2 eqn: Ht2; subst.
  destruct (a0 <=? a1) eqn: Ha; subst;
  inv Hout; repeat invert_less_defined; solve_approx.
Qed.*)
