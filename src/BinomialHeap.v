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
From Clairvoyance Require Import Core Approx ApproxM List Misc BankersQueue Tick Demand.

(** Interface to construct demand functions *)

(* ApproxAlgebra records minimized with only the component relevant to use this interface.
   You can pretend that (a : AA) is really (a : Type).
   (I will probably change this to be a type class.)
 *)

 Record AA : Type :=
  { carrier :> Type
  (* ; approx : Type *)
  }.

(* Every type in your code must implement AA *)

(* Tuples *)
Canonical AAProd (a b : AA) : AA :=
  {| carrier := (a * b)%type
  (* ;  approx :=(approx a * approx b)%type *)
  |}.

(* List *)
Canonical AAList (a : AA) : AA :=
  {| carrier := list a
  (* ;  approx := listA (approx a) *)
  |}.

Canonical AAnat : AA :=
  {| carrier := nat |}.

Parameter TODO : forall {A : Type}, A.

Canonical AABool : AA :=
  {| carrier := bool |}.

Infix "**" := AAProd (at level 40).

(* Demand functions *)
Module Import DF.

(* Demand functions on input x and output y. *)
Definition DF {a b : AA} (x : a) (y : b) : Type. 
Admitted.

(* Identity *)
Definition id {a : AA} {x : a} : DF x x. 
Proof. refine TODO. Defined.

(* Sequential composition *)
Definition compose {a b c : AA} {x : a} {y : b} {z : c}
  (f : DF x y) (g : DF y z) : DF x z.
Proof. refine TODO. Defined.

Module Import Notations.

Declare Scope df_scope.
Delimit Scope df_scope with df.
Bind Scope df_scope with DF.

Infix ">>>" := compose (left associativity, at level 40) : df_scope.

End Notations.

(* Projections *)
Definition proj1DF {a b : AA} {xy' : a ** b} : DF xy' (fst xy').
Proof. refine TODO. Defined.

Definition proj2DF {a b : AA} {xy' : a ** b} : DF xy' (snd xy').
Proof. refine TODO. Defined.

(* Pairing *)
Definition pairDF {a b c : AA} {x' : a} {y' : b} {z' : c} (f : DF x' y') (g : DF x' z')
  : DF x' (y', z').
Proof. refine TODO. Defined.

(* The [letDF] combinator lets us compute an
   intermediate result and "push" it in the context.

   It encodes [let]:

     Given f : X -> Y
       and g : (X * Y) -> Z

     they can be composed as

     let y := f x in
     g (x, y) *)
Definition letDF {a b c : AA} {x : a} {y : b} {z : c}
  : DF x y ->  (* f *)
    DF (x, y) z -> (* g *)
    DF x z.
Proof. refine TODO. Defined.

(* Increment the cost by 1 *)
Definition tickDF {a b : AA} {x' : a} {y' : b} : DF x' y' -> DF x' y'.
Proof. refine TODO. Defined.

(* Encoding of [] *)
Definition nilD {a b : AA} {x : a} : DF x (nil (A := b)).
Proof. refine TODO. Defined.

(* Encoding of (_ :: _) *)
Definition consD {r a : AA} {s : r} {x : a} {xs : list a} (xD : DF s x) (xsD : DF s xs)
  : DF s (x :: xs).
Proof. refine TODO. Defined.

(* Encoding of match on lists *)
Definition match_list {a b c : AA} {g : b} {f : list a -> c} {xs : list a}
    (NIL : DF g (f nil))
    (CONS : forall x xs', DF (g, x, xs') (f (cons x xs')))
  : DF (g, xs) (f xs) :=
  match xs with
  | nil => TODO >>> NIL
  | cons x xs' => TODO >>> (CONS x xs')
  end.

(* Encoding of [if] *)
Definition if_ {a b : AA} {x : a} {cond : bool}
  {f : bool -> b}
  (i : DF x cond)
  (thn : DF x (f true))
  (els : DF x (f false))
  : DF x (f cond).
Proof. refine TODO. Defined.

End DF.

(* Encoding of operators *)

Definition le_ {x y : nat} : DF (x, y) (x <=? y).
Proof. refine TODO. Defined.

Definition lt_ {x y : nat} : DF (x, y) (x <? y).
Proof. refine TODO. Defined.

Definition add1 {x : nat} : DF x (x + 1).
Proof. refine TODO. Defined.

Import DF.Notations.
#[local] Open Scope df.

(* Pure implementation *)
Definition A := nat.

Canonical AAA : AA :=
  {| carrier := A |}.

Inductive Tree : Type :=
  | Node : nat -> A -> list Tree -> Tree.

(* ApproximationAlgebra for Tree *)
Canonical AATree : AA :=
  {| carrier := Tree |}.

(* Encoding of Node *)
Definition nodeD {r : AA} {s : r} {n : nat} {x : A} {ts : list Tree}
    (nD : DF s n) (xD : DF s x) (tsD : DF s ts)
  : DF s (Node n x ts).
Proof. refine TODO. Defined.

(* Encoding of match on Tree *)
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
Proof. refine TODO. Defined.

Definition treesD {h : Heap} : DF h (trees h).
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

Definition rankDF {t} : DF t (rank t).
Proof.
  refine (TODO >>> match_Tree (f := fun t => rank t) (g := t) (*TODO*)
    (fun r1 v1 c1 => _)).
  cbn. refine TODO.
Defined. 

Definition root (t : Tree) : A :=
  match t with
  | (Node r v c) => v
  end.

Definition rootDF {t} : DF t (root t).
Proof.
  refine (TODO >>> match_Tree (f := fun t => root t) (g := t) (*TODO*)
    (fun r1 v1 c1 => _)).
  cbn. refine TODO.
Defined. 

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
  
