From Equations Require Import Equations.

From Coq Require Import Arith List Lia Setoid Morphisms Orders.
Import ListNotations.
From Clairvoyance Require Import Core Approx ApproxM List Misc BankersQueue Tick BinomialHeap.

Definition tree0 : Tree := Node 2 30 [(Node 1 31 [(Node 0 32 [])]); (Node 0 33 [])].

Definition tree1 : Tree := Node 2 40 [(Node 1 41 [(Node 0 42 [])]); (Node 0 43 [])].
  
Definition tree2 : Tree := Node 1 50 [(Node 0 51 [])].
  
Definition tree3 : Tree := Node 0 60 [].  

(*link*)
Compute ((link tree0 tree1) = ((Node 3 30 [(Node 2 40 [(Node 1 41 [(Node 0 42 [])]); (Node 0 43 [])]); (Node 1 31 [(Node 0 32 [])]); (Node 0 33 [])]))).

(*rank*)
Compute (andb (rank tree0 =? 2) (andb (rank tree1 =? 2)  (andb (rank tree2 =? 1) (rank tree3 =? 0)))).

(*root*)
Compute (andb (root tree0 =? 30) (andb (root tree1 =? 40)  (andb (root tree2 =? 50) (root tree3 =? 60)))).

(*insTree*)
Compute ((insTree tree3 (MkHeap [tree2; tree1])) 
  = (MkHeap [tree3; tree2; tree1])).

Compute ((insTree tree2 (MkHeap [tree2; tree1])) 
  = (MkHeap 
    [(Node 3 40 [
      (Node 2 50 [
        Node 1 50 [
          (Node 0 51 [])
          ];
        Node 0 51 []
        ]
      );
      (Node 1 41 [
        Node 0 42 []
        ]
      );
      Node 0 43 []
      ])])).

(*insert*)
Compute ((insert 70 (MkHeap [tree2; tree1])) = (MkHeap [(Node 0 70 []); tree2; tree1])).

Compute (link tree1 tree0).

(*merge*)
Compute ((merge (MkHeap [tree2; tree1]) (MkHeap [tree3; tree0]))
  = (MkHeap [tree3; tree2; 
    (Node 3 30
      [Node 2 40 [
        Node 1 41 [
          (Node 0 42 [])];
        (Node 0 43 [])];
      Node 1 31 [
        (Node 0 32 [])];
      (Node 0 33 [])])])).

(*removeMinTree*)
Compute ((removeMinTree (MkHeap [tree3; tree2; tree1])) = (Some (tree1, MkHeap [tree3; tree2]))).

Compute (removeMinTree (MkHeap []) = None).

(*findMin*)
Compute ((findMin (MkHeap [tree3; tree2; tree1])) = (Some 40)).

Compute (findMin (MkHeap []) = None).

(*deleteMin*)
Compute ((deleteMin (MkHeap [tree3; tree2; tree0])) 
  = MkHeap (
      [(Node 1 33 
        [(Node 0 60 [])]);
      (Node 2 31 
        [Node 1 50 
          [(Node 0 51 [])];
        (Node 0 32 [])])])).

Definition mkTA (r : nat) (v : nat) (c : list TreeA) : TreeA :=
  let comb tA lTA := ConsA (Thunk tA) (Thunk lTA) in
    let acc := NilA in
      NodeA r v (Thunk (List.CaseStudyFolds.foldr acc comb c)).

Definition treeA0 : TreeA := mkTA 2 30 [(mkTA 1 31 [(mkTA 0 32 [])]); (mkTA 0 33 [])].

Definition treeA1 : TreeA := mkTA 2 40 [(mkTA 1 41 [(mkTA 0 42 [])]); (mkTA 0 43 [])].
        
Definition treeA2 : TreeA := mkTA 1 50 [(mkTA 0 51 [])].
        
Definition treeA3 : TreeA := mkTA 0 60 [].