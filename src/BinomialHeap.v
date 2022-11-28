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

From Coq Require Import Arith List Lia Setoid Morphisms Orders Program.
Import ListNotations.
From Clairvoyance Require Import Core Approx ApproxM List Misc BankersQueue Tick.

(* Pure implementation *)
Definition A := nat.

Inductive Tree : Type := 
  | Node : nat -> A -> list Tree -> Tree.

Record Heap : Type := MkHeap 
  { trees : list Tree }.

Definition link (t1 t2 : Tree) : Tree :=
  match (t1, t2) with
  | (Node r1 v1 c1, Node r2 v2 c2) => if leb v1 v2
    then Node (r1 + 1) v1 (t2 :: c1)
    else Node (r2 + 1) v2 (t1 :: c2)
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

Definition insTree (t : Tree) (hp : Heap) : Heap :=
  MkHeap (insTreeAux t (trees hp)).

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

Definition insertHelper1 (t t' : T TreeA) (ts : T (listA TreeA)) : M (listA TreeA) :=
  let! r := rankA t in
  let! r' := rankA t' in
  if r <? r'
    then ret (ConsA t ts)
    else let~ linkedT := linkA t t' in
      ret (ConsA linkedT ts).

Definition insertHelper2 (t t' : T TreeA) (ts : listA TreeA) : M (listA TreeA) :=
  let! r := rankA t in
  let! r' := rankA t' in
  if r <? r'
    then ret (ConsA t (Thunk ts))
    else let~ linkedT := linkA t t' in
      ret (ConsA linkedT (Thunk ts)).

Fixpoint listA_rect {a : Type} 
  (C : listA a -> Type)
  (base : C NilA)
  (rec1 : forall (x : T a), C (ConsA x Undefined))
  (rec2 : forall (x : T a) (l' : listA a),
     C l' -> C (ConsA x (Thunk l')))
  (l : listA a)
  : C l :=
  match l with
  | NilA => base
  | ConsA x Undefined => rec1 x
  | ConsA x (Thunk l') => rec2 x l' (listA_rect C base rec1 rec2 l')
  end.

Definition lengthDefinedA {a : Type} (l : listA a) : nat :=
  let C := (fun t => nat) in
  let base := 0 in
  let rec1 := (fun xT => 1) in
  let rec2 := fun xT xsT =>
    fun recResult => recResult + 1 in
  listA_rect C base rec1 rec2 l.


Definition insTreeAuxA (t : T TreeA) (ts : listA TreeA) : M (listA TreeA) :=
  let C := (fun t => M (listA TreeA)) in
  let base := ret (ConsA t (Thunk NilA)) in
  let rec1 := (fun t' => insertHelper1 t t' Undefined) in
  let rec2 := fun t' ts => 
    fun recResult => (bind recResult
          (fun l => insertHelper2 t t' l)) in
  listA_rect C base rec1 rec2 ts.

Definition insTreeA (t : T TreeA) (hp : HeapA) : M HeapA :=
  let! trs := force (treesA hp) in
  bind (insTreeAuxA t trs) (fun ts => ret (MkHeapA (Thunk ts))).

Definition insertA (x : A) (hp : HeapA) : M HeapA :=
  insTreeA (Thunk (NodeA 0 x (Thunk (NilA)))) hp.

(*Program Fixpoint mergeTreeAuxA (trs1 trs2 : listA TreeA) 
  {measure ((lengthDefinedA trs1) + (lengthDefinedA trs2))} : M (listA TreeA)
  :=
  match (trs1, trs2) with
  | (NilA, _) => ret trs2
  | (_, NilA) => ret trs1
  | (ConsA t1 trs1T', ConsA t2 trs2T') =>
    let! r1 := rankA t1 in
    let! r2 := rankA t2 in
    if r1 <? r2 
      then let! trs1' := force trs1T' in
        bind (mergeTreeAuxA trs1' trs2)
        (fun t => ret (ConsA t1 (Thunk t)))
      else 
        let! trs2' := force trs2T' in
        if r2 <? r1
        then 
          bind (mergeTreeAuxA trs1 trs2')
          (fun t => ret (ConsA t2 (Thunk t)))
        else 
          let! trs1' := force trs1T' in
          bind (bind (linkA t1 t2)
          (fun linked => bind (mergeTreeAuxA trs1' trs2')
          (fun merged => insTreeA (Thunk linked) (MkHeapA (Thunk merged)))))
          (fun hp => force (treesA hp))
  end.*)

Definition mergeCasesA (t1 t2 : T TreeA) (mrg1p2 mrg12p mrg1p2p : M (listA TreeA)) : M (listA TreeA) :=
  let! r1 := rankA t1 in
  let! r2 := rankA t2 in
  if r1 <? r2
    then bind mrg1p2 (fun t => ret (ConsA t1 (Thunk t)))
    else if r2 <? r1
      then bind mrg12p (fun t => ret (ConsA t2 (Thunk t)))
      else bind (bind (linkA t1 t2) (fun x => bind mrg1p2p (fun t => (insTreeA (Thunk x) (MkHeapA (Thunk t))))))
        (fun h => force (treesA h)).

Definition mergeAuxA (trs1 trs2 : listA TreeA) : M (listA TreeA) :=
  let u := force Undefined in
  let C := (fun t => M (listA TreeA)) in
  let base := ret trs2 in
  let rec1 := fun t1 => (
    let base2 := ret (ConsA t1 Undefined) in
    let rec12 := (fun t2 => mergeCasesA t1 t2 u u u) in
    let rec22 := (fun t2 trs2' => (fun recResult2 =>
      mergeCasesA t1 t2 u recResult2 u )) in
    listA_rect C base2 rec12 rec22 trs2
  ) in
  let rec2 := fun t1 trs1' => (fun recResult1 => (
    let base2 := ret (ConsA t1 Undefined) in
    let rec12 := (fun t2 => mergeCasesA t1 t2 recResult1 u u) in
    let rec22 := (fun t2 trs2' => (fun recResult2 =>
      mergeCasesA t1 t2 recResult1 recResult2 recResult1)) in
    listA_rect C base2 rec12 rec22 trs2
  )) in
  listA_rect C base rec1 rec2 trs1.

Definition mergeA (hp1 hp2 : HeapA) : M HeapA :=
  let! trs1 := force (treesA hp1) in
  let! trs2 := force (treesA hp2) in
  bind (mergeAuxA trs1 trs2) (fun trs => mkHeapA (Thunk trs)).

(*trs1 = ConsA t1 Undefined*)
(*Definition mergeHelper1 (t1 : T TreeA) (trs2 : listA TreeA) : M (listA TreeA) :=
  let C := (fun t => M (listA TreeA)) in
  let base := ret (ConsA t1 Undefined) in
  let rec1 := fun t2 => (*trs2 = ConsA t2 Undefined*)
    let! r1 := rankA t1 in
    let! r2 := rankA t2 in
    if r1 <? r2
      then ret (ConsA t1 Undefined) (*TODO: (Thunk trs2)? Merge is constant because trs1' is undefined*)
      else if r2 <? r1
        then ret (ConsA t2 Undefined) (*TODO: (Thunk (ConsA t1 (Thunk NilA)))? Merge is constant because trs2' is undefined*)
        else bind (linkA t1 t2) (fun linked => ret (ConsA (Thunk linked) Undefined)) (*Merge is constant because trs1' and trs2' are undefined *) in
  let rec2 := fun t2 trs2' =>
    fun recResult =>
    let! r1 := rankA t1 in
    let! r2 := rankA t2 in
    if r1 <? r2
      then ret (ConsA t1 Undefined) (*TODO: Thunk trs2? Merge is constant because trs1' is undefined*)
      else if r2 <? r1
        then bind recResult (fun t => ret (ConsA t2 (Thunk t))) (*trs2' is defined*)
        else bind (linkA t1 t2) (fun linked => ret (ConsA (Thunk linked) (Thunk NilA))) (*TODO: trs2' ? Merge is constant because trs1' is undefined*) in
  listA_rect C base rec1 rec2 trs2.
(*
(*trs1 = ConsA t2 (Thunk trs1')*)
(*recResult1 = mergeTreeAuxA trs1' trs2*)
Definition mergeHelper2 (t1 : T TreeA) (trs1' : listA TreeA) (recResult1 : M listA TreeA) (trs2 : listA TreeA) : M (listA TreeA) :=
  let C := (fun t => M (listA TreeA)) in
  let base := ret (ConsA t1 (Thunk trs1')) in
  let rec1 := fun t2 => (*trs2 = ConsA t2 Undefined*)
    let! r1 := rankA t1 in
    let! r2 := rankA t2 in
    if r1 <? r2
      then ret (ConsA t1 recResult1)
      else if r2 <? r1
        then ret (ConsA t2 Undefined) (*Merge ConsA t2 (mergeTreeAuxA trs1 trs2') is constant because trs2' is undefined*)
        else bind (linkA t1 t2) (fun linked => ret (ConsA (Thunk linked) Undefined)) (*Merge is constant because trs1' and trs2' are undefined *) in
  let rec2 := fun t2 trs2' =>
    fun recResult2 => (*recResult2 = mergeTreeAux trs1' trs2'*)
    let! r1 := rankA t1 in
    let! r2 := rankA t2 in
    if r1 <? r2
      then ret (ConsA t1 (Thunk trs2)) (*Merge is constant because trs1' is undefined*)
      else if r2 <? r1
        then bind recResult (fun t => ret (ConsA t2 (Thunk t))) (*trs2' is defined*)
        else bind (linkA t1 t2) (fun linked => insTreeAuxA (Thunk linked) trs2') (*Merge is constant because trs1' is undefined*) in
  listA_rect C base rec1 rec2 trs2.

Definition mergeTreeAuxA (trs1 trs2 : listA TreeA) : M (listA TreeA) :=
  match trs1
  | (NilA, _) => ret trs2
  | (_, NilA) => ret trs1
  | (t1 :: trs1', t2 :: trs2') =>
    let! r1 := rank t1 in
    let! r2 := rank t2 in
    if r1 <? r2 
      then ConsA t1 (mergeTreeAuxA trs1' trs2)
      else if r2 <? r1
        then ConsA t2 (mergeTreeAuxA trs1 trs2')
        else insTreeA (linkA t1 t2) (mergeTreeAuxA trs1' trs2')
  end.
  let C := (fun t => M (listA TreeA)) in
  let base := ret (trs2) in
  let base2 := ret (trs1) in
  let rec1_1 := (fun x => )
  let rec1_2 :=
  let rec2_1 :=
  let rec2_2 :=
  in 

Definition mergeA (hp1 hp2 : HeapA) : M HeapA :=
  let~ trsM := (fun trsR => merge_ trsR (treesA hp2)) $! (treesA hp1) in
  mkHeapA trsM.*)*)

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

Import Tick.Notations.

(*Demand functions*)

(*Definition linkA (t1 t2 : T TreeA) : M TreeA :=
  tick >>
  let! t1' := force t1 in
  let! t2' := force t2 in
  match (t1', t2') with
  | (NodeA r1 v1 c1, NodeA r2 v2 c2) => if leb v1 v2
    then ret (NodeA (r1 + 1) v1 (Thunk (ConsA t2 c1)))
    else ret (NodeA (r2 + 1) v2 (Thunk (ConsA t1 c2)))
  end.*)

Definition linkD (outD : TreeA) : Tick ((T TreeA) * (T TreeA)) :=
  Tick.tick >>
  match outD with
  | NodeA r1 v1 (Thunk (ConsA (Thunk (NodeA r2 v2 c2)) cs1)) => 
    let tD1 := NodeA r1 v1 cs1 in
    let tD2 := NodeA r2 v2 c2 in
    if (Nat.ltb v2 v1)
      then Tick.ret (Thunk tD1, Thunk tD2)
      else Tick.ret (Thunk tD2, Thunk tD1)
  | _ => bottom
  end.

(*Definition rankA (t : T TreeA) : M nat :=
  let! tval := force t in
  match tval with
  | (NodeA r v c) => ret r
  end.*)

Definition rankD (t : Tree) : Tick (T TreeA) :=
  Tick.tick >>
  match t with
  | Node r v c => Tick.ret (Thunk (NodeA r v Undefined))
  end.

(*Definition rootA (t : T TreeA) : M A :=
  let! tval := force t in
  match tval with
  | (NodeA r v c) => ret v
  end.*)

Definition rootD (t : Tree) : Tick (T TreeA) :=
  Tick.tick >>
  match t with
  | Node r v c => Tick.ret (Thunk (NodeA r v Undefined))
  end.

(*
Definition insertHelper1 (t t' : T TreeA) (ts : T (listA TreeA)) : M (listA TreeA) :=
  let! r := rankA t in
  let! r' := rankA t' in
  if r <? r'
    then ret (ConsA t ts)
    else let~ linkedT := linkA t t' in
      ret (ConsA linkedT ts).

Definition insertHelper2 (t t' : T TreeA) (ts : listA TreeA) : M (listA TreeA) :=
  let! r := rankA t in
  let! r' := rankA t' in
  if r <? r'
    then ret (ConsA t (Thunk ts))
    else let~ linkedT := linkA t t' in
      ret (ConsA linkedT (Thunk ts)).

Definition insTreeAuxA (t : T TreeA) (ts : listA TreeA) : M (listA TreeA) :=
  let C := (fun t => M (listA TreeA)) in
  let base := ret (ConsA t (Thunk NilA)) in
  let rec1 := (fun t' => insertHelper1 t t' Undefined) in
  let rec2 := fun t' ts => 
    fun recResult => (bind recResult
          (fun l => insertHelper2 t t' l)) in
  listA_rect C base rec1 rec2 ts.*)

(*Definition insTreeA (t : T TreeA) (hp : HeapA) : M HeapA :=
  let! trs := force (treesA hp) in
  bind (insTreeAuxA t trs) (fun ts => ret (MkHeapA (Thunk ts))).*)

Definition insTreeD (t : T TreeA) (outD : HeapA) : Tick ((T TreeA) * (T HeapA)) :=
  (*Todo*) Tick.ret (Undefined, Undefined).

(*Definition insertA (x : A) (hp : HeapA) : M HeapA :=
  insTreeA (Thunk (NodeA 0 x (Thunk (NilA)))) hp.*)

Definition insertD (x : A) (outD : HeapA) :=
  insTreeD (Thunk (NodeA 0 x (Thunk (NilA)))) outD.

(*Definition removeMinTreeAuxA :
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
  foldrA (ret None) removeMinTreeAuxA (treesA hp).*)

(*TODO: does not use outD*)
Definition removeMinTreeD (hp : Heap) (outD : option ((T TreeA) * (HeapA))) : Tick HeapA :=
  Tick.tick >>
  Tick.ret (MkHeapA (Thunk (treeListConvert (trees hp)))). (* removeMin must traverse the whole heap. *)

(*Definition findMinA (hp : HeapA) : M (option A) :=
  let! minPair := removeMinTreeA hp in
  match minPair with
  | None => ret None
  | Some (t, _) => bind (rootA t) (fun x => ret (Some x))
  end.*)

(*TODO: does not use outD*)
Definition findMinD (hp : Heap) (outD : option A) : Tick HeapA :=
  Tick.tick >>
  Tick.ret (MkHeapA (Thunk (treeListConvert (trees hp)))). (* findMin must traverse the whole heap. *)

(*Definition deleteMinA (hp : HeapA) : M (HeapA) :=
  let! minPair := removeMinTreeA hp in
  match minPair with
  | None => ret (MkHeapA (Thunk NilA))
  | Some (t, ts) =>
    let! (NodeA r v c) := force t in
    bind (List.TakeCompare.revA c)
      (fun children => mergeA (MkHeapA (Thunk children)) ts)
  end.*)

(*TODO: does not use outD*)
Definition deleteMinD (hp : Heap) (outD : HeapA) : Tick HeapA :=
  Tick.tick >>
  Tick.ret (MkHeapA (Thunk (treeListConvert (trees hp)))). (* deleteMin must traverse the whole heap. *)