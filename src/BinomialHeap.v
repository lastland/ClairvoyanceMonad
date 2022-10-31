(* Overview

KNOWN
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

From Coq Require Import Arith List Lia Setoid Morphisms Orders.
Import ListNotations.
From Clairvoyance Require Import Core Approx ApproxM List Misc BankersQueue.

(* Pure implementation *)
Definition A := nat.

Inductive Tree : Type := 
  | Node : nat -> A -> list Tree -> Tree.

Record Heap : Type := MkHeap 
  { trees : list Tree }.

Definition link (t1 t2 : Tree) : Tree :=
  match (t1, t2) with
  | (Node r1 v1 c1, Node r2 v2 c2) => if leb v1 v2
    then Node r1 v1 (t2 :: c1)
    else Node r2 v2 (t1 :: c2)
  end.

Definition rank (t : Tree) : nat :=
  match t with
  | (Node r v c) => r
  end.

Definition root (t : Tree) : A :=
  match t with
  | (Node r v c) => v
  end.

Definition insTree (t : Tree) (hp : Heap) 
  : Heap :=
  match (trees hp) with
  | [] => MkHeap [t]
  | t' :: hp' => if rank t <? rank t' 
    then MkHeap (t :: (trees hp))
    else MkHeap ((link t t') :: hp')
  end.

Definition insert (x : A) (hp : Heap) 
  : Heap :=
  insTree (Node 0 x []) hp.

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
    then ret (NodeA r1 v1 (Thunk (ConsA t2 c1)))
    else ret (NodeA r2 v2 (Thunk (ConsA t1 c2)))
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

Definition insTreeA (t : T TreeA) (hp : HeapA) : M HeapA :=
  let! trs := force (treesA hp) in
  match trs with
  | NilA => mkHeapA (Thunk (ConsA t (Thunk NilA)))
  | ConsA t' hp' => 
    let! r := rankA t in
    let! r' := rankA t' in 
    if r <? r'
      then mkHeapA (Thunk (ConsA t (treesA hp)))
      else let~ linkedT := (linkA t t') in
        mkHeapA (Thunk (ConsA linkedT hp'))
  end.

Definition insertA (x : A) (hp : HeapA) : M HeapA :=
  insTreeA (Thunk (NodeA 0 x (Thunk (NilA)))) hp.

(*TODO*)
Fixpoint merge_ (trs1Val : listA TreeA) (trs2 : T (listA TreeA)) : M (listA TreeA) :=
  let! trs2Val := force trs2 in
  match trs1Val, trs2Val with
  | NilA, _ => ret trs2Val
  | _, NilA => ret trs1Val
  | ConsA t1 trs1', ConsA t2 trs2' =>
    let! r1 := rankA t1 in
    let! r2 := rankA t2 in
    if r1 <? r2 
      then
        let~ ts := (fun trsR => merge_ trsR trs2) $! trs1' in
        bind (insTreeA t1 (MkHeapA ts)) (fun hp => (force (treesA hp)))
      else 
        if r2 <? r1 then
          let~ ts := (fun trsR => merge_ trsR trs2') $! trs1' in
          bind (insTreeA t1 (MkHeapA ts))
          (fun ins1 => bind (insTreeA t2 ins1) (fun hp => (force (treesA hp))))
        else let~ ts := (fun trsR => merge_ trsR trs2') $! trs1' in
          let~ linked := linkA t1 t2 in
          bind (insTreeA linked (MkHeapA ts)) (fun hp => (force (treesA hp)))
  end.

Definition mergeA (hp1 hp2 : HeapA) : M HeapA :=
  let~ trsM := (fun trsR => merge_ trsR (treesA hp2)) $! (treesA hp1) in
  mkHeapA trsM.

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
  foldrA (ret None) removeMinTreeAuxA (treesA hp).

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
    bind (List.TakeCompare.revA c)
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

(*Definition less_defined_TreeA (t1 t2 : TreeA) : Prop :=
  match t1, t2 with
  | (NodeA r1 v1 c1), (NodeA r2 v2 c2) =>
    less_defined c1 c2
  end.

#[local] Instance LessDefined_TreeA : LessDefined TreeA :=
  less_defined_TreeA.*)

Record less_defined_HeapA (hp1 hp2 : HeapA) : Prop :=
  { ld_trs : less_defined (treesA hp1) (treesA hp2) }.

#[global] Instance LessDefined_HeapA : LessDefined HeapA :=
  less_defined_HeapA.

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
Proof. exact PreOrder_Rep. Qed.

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

#[global] Instance Exact_ListTree : Exact (list Tree) (listA TreeA) :=
  treeListConvert.

#[global] Instance Exact_Heap : Exact Heap HeapA :=
  fun hp => MkHeapA (exact (trees hp)).

#[global] Instance ExactMaximal_HeapA : ExactMaximal HeapA Heap.
Proof. Admitted.

(*TODO: should this be shallow or check the trees also?*)
(*TODO: Lub_listA should probably not be in BankersQueue.*)
#[global] Instance Lub_HeapA : Lub HeapA :=
  fun hp1 hp2 =>
    MkHeapA (lub_T (BankersQueue.Lub_listA) (treesA hp1) (treesA hp2)).

#[global] Instance LubRep_HeapA : LubRep HeapA (T (listA TreeA)).
Proof.
  intros [] []; reflexivity.
Qed.
    
#[global] Instance LubLaw_HeapA : LubLaw HeapA.
Proof.
  exact LubLaw_LubRep.
Qed.
