(* Clairvoyance monad with executable nondeterminism *)
(* A poor man's crystal ball *)

From Coq Require Import List Arith.

Set Implicit Arguments.
Set Contextual Implicit.
Set Maximal Implicit Insertion.

Inductive trie (a : Type) : Type :=
| Empty
| Node (l : trie a) (m : option a) (r : trie a)
.

Fixpoint lookup {a} (p : list bool) (t : trie a) : option a :=
  match t with
  | Empty => None
  | Node l m r =>
    match p with
    | nil => m
    | true :: p => lookup p l
    | false :: p => lookup p r
    end
  end.

Fixpoint insert {a} (p : list bool) (x : a) (t : trie a) : trie a :=
  match t, p with
  | Empty, nil => Node Empty (Some x) Empty
  | Empty, true :: p => Node (insert p x Empty) None Empty
  | Empty, false :: p => Node Empty None (insert p x Empty)
  | Node l m r, nil => Node l (Some x) r
  | Node l m r, true :: p => Node (insert p x l) m r
  | Node l m r, false :: p => Node l m (insert p x r)
  end.

Module Import Blind.

Definition ThunkId := list bool.

Definition tid_eqb (x y : ThunkId) : bool :=
  if list_eq_dec Bool.bool_dec x y then true else false.

Inductive T (a : Type) : Type :=
| Undefined (n : ThunkId)
| Defined (x : a)
.

Inductive N (a : Type) : Type :=
| Ret (_ : a)
| Thunk {b} (_ : N b) (_ : T b -> N a)
| Thonk (n : ThunkId)  (* Forced an undefined thunk *)
.

Record M (a : Type) : Type := MkM
  { unM : forall r, (a -> nat -> N r) -> N r }. 

(* StateT (trie bool) Cont (T a) *)
Fixpoint _runN {r a} (u : N a) (tid : ThunkId) (t : trie unit)
    (k : trie unit -> a -> trie unit * T r) : trie unit * T r :=
  match u with
  | Ret x => k t x
  | Thunk v h =>
    let run_forced t :=
           _runN v (true :: tid) t (fun t x =>
           _runN (h (Defined x)) (false :: tid) t k) in
    match lookup tid t with
    | None =>
      match _runN (h (Undefined tid)) (false :: tid) t k with
      | (_, Defined _) as r => r
      | (t, Undefined tid') as r =>
          if tid_eqb tid tid' then
            run_forced (insert tid tt t)
          else
            r
      end
    | Some _ => run_forced t
    end
  | Thonk tid' => (t, Undefined tid')
  end.

Definition runN {a} (u : N a) : T a := snd (_runN u nil Empty (fun t y => (t, Defined y))).

Fixpoint incr (xs : ThunkId) : ThunkId :=
  match xs with
  | nil => false :: nil
  | false :: xs => true :: xs
  | true :: xs => false :: incr xs
  end.

Definition memo : Type := trie (option ThunkId * option ThunkId * bool).
Definition Parent : Type := ThunkId * bool.

Definition insert' (k : Parent) (tid : ThunkId) (t : memo) : memo :=
  let '(k, b) := k in
  let '(l, r, f) :=
    match lookup k t with
    | Some lrf => lrf
    | None => (None, None, false)
    end in
  insert k (if b then (l, Some tid, f) else (Some tid, r, f)) t.

Definition lookup' (k : Parent) (t : memo) : option ThunkId :=
  let '(k, b) := k in
  match lookup k t with
  | Some (l, r, _) => if b then r else l
  | None => None
  end.

Definition set_forced (k : ThunkId) (t : memo) : memo :=
  let '(l, r) :=
    match lookup k t with
    | Some (l, r, _) => (l, r)
    | None => (None, None)
    end in
  insert k (l, r, true) t.

Definition get_forced (k : ThunkId) (t : memo) : bool :=
  match lookup k t with
  | Some (_, _, f) => f
  | None => false
  end.

Definition check_thunk (fresh : ThunkId) (parent : Parent) (t : memo)
  : ThunkId * ThunkId * bool * memo :=
  match lookup' parent t with
  | Some tid => (fresh, tid, get_forced tid t, t)
  | None => (incr fresh, fresh, false, insert' parent fresh t)
  end.

(* A variant of runN that allocates ThunkId more parsimoniously *)
Fixpoint _runN' {r a} (u : N a) (fresh : ThunkId) (parent : Parent) (t : memo)
    (k : ThunkId -> memo -> a -> ThunkId * memo * T r)
  : ThunkId * memo * T r :=
  match u with
  | Ret x => k fresh t x
  | Thunk v h =>
    let '(fresh, tid, forced, t) := check_thunk fresh parent t in
    let run_forced fresh tid t :=
      _runN' v fresh (tid, false) t (fun fresh t x =>
      _runN' (h (Defined x)) fresh (tid, true) t k)
    in
    if forced then run_forced fresh tid t
    else
      match _runN' (h (Undefined tid)) fresh (tid, true) t k with
      | (_, _, Defined _) as r => r
      | (fresh, t, Undefined tid') as r =>
        if tid_eqb tid tid' then
          run_forced fresh tid (set_forced tid t)
        else
          r
      end
  | Thonk tid' => (fresh, t, Undefined tid')
  end.

Definition runN' {a} (u : N a) : T a :=
  snd (_runN' u (false :: nil) (nil, true) Empty (fun fresh t y => (fresh, t, Defined y))).

Definition runM {a} (u : M a) : T (a * nat) := runN' (unM u (fun x y => Ret (x, y))).

Definition ret {a} (x : a) : M a :=
  MkM (fun _ c => c x 0).

Definition bind {a b} (u : M a) (k : a -> M b) : M b :=
  MkM (fun _ c => unM u (fun x n => unM (k x) (fun y m => c y (n + m)))).

Definition tick : M unit :=
  MkM (fun _ c => c tt 1).

Definition thunk {a} (u : M a) : M (T a) :=
  MkM (fun _ c => Thunk (unM u (fun x n => Ret (x, n))) (fun tx =>
    match tx with
    | Undefined tid => c (Undefined tid) 0
    | Defined (x, n) => c (Defined x) n
    end)).

Definition force {a} (tx : T a) : M a :=
  MkM (fun _ c =>
    match tx with
    | Undefined n => Thonk n
    | Defined x => c x 0
    end).

Definition forcing {a b} (tx : T a) (f : a -> M b) : M b :=
  bind (force tx) f.

End Blind.

Notation "t >> s" := (bind t (fun _ => s)) (at level 61, left associativity).

Notation "'let!' x' ':=' t 'in' s" := (bind t (fun x' => s)) (x' pattern, at level 200).
Notation "'let~' x  ':=' t 'in' s" := (bind (thunk t) (fun x => s)) (x pattern, at level 200).
Notation "f $! x" := (forcing x f) (at level 61, left associativity).

Unset Elimination Schemes.

(* The [listA] type discussed in Fig. 7 in Section 4. *)
Inductive listA (a : Type) : Type :=
  NilA | ConsA (x1 : T a) (x2 : T (listA a)).

Set Elimination Schemes.

Fixpoint append_ {a : Type} (xs' : listA a) (ys : T (listA a)) : M (listA a) :=
  tick >>
  match xs' with
  | NilA => force ys
  | ConsA x xs1 =>
    let~ t := (fun xs1' => append_ xs1' ys) $! xs1 in
    ret (ConsA x t)    
  end.

Definition appendA {a : Type} (xs ys : T (listA a)) : M (listA a) :=
  (fun xs' => append_ xs' ys) $! xs.

Fixpoint take_ {a : Type} (n : nat) (xs' : listA a) : M (listA a) :=
  tick >>
  match n, xs' with
  | O, _ => ret NilA
  | S _, NilA => ret NilA
  | S n1, ConsA x xs1 =>
    let~ t := take_ n1 $! xs1 in
    ret (ConsA x t)  
  end.

Definition takeA {a : Type} (n : nat) (xs : T (listA a)) : M (listA a) :=
  take_ n $! xs.

Fixpoint drop_ {a} (n : nat) (xs' : listA a) : M (listA a) :=
  tick >>
  match n, xs' with
  | O, _ => ret xs'
  | S _, NilA => ret NilA
  | S n, ConsA _ xs => drop_ n $! xs
  end.

Definition drop {a : Type} (n : nat) (xs : T (listA a)) : M (listA a) :=
  drop_ n $! xs.

Definition pA {a} (n : nat) (xs ys : T (listA a)) : M (listA a) :=
  tick >>
  let~ t := appendA xs ys in
  takeA n t.

Fixpoint exact_list {a} (xs : list a) : T (listA a) :=
  Defined match xs with
  | nil => NilA
  | x :: xs => ConsA (Defined x) (exact_list xs)
  end.

(*
Compute runM
  (let~ z := pA 6 (exact_list (seq 0 10)) (exact_list (seq 11 20)) in
   drop 3 z).
*)

Fixpoint revA_ {a : Type} (xs' : listA a) (ys : T (listA a)) : M (listA a) :=
  match xs' with
  | NilA => force ys
  | ConsA x xs1 =>
    let~ ys1 := ret (ConsA x ys) in
    (fun xs1' => revA_ xs1' ys1) $! xs1
  end.

Definition revA {a : Type} (xs : T (listA a)) : M (listA a) :=
  let~ ys := ret NilA in
  (fun xs' => revA_ xs' ys) $! xs.

Record QueueA (a : Type) : Type := MkQueueA
  { nfrontA : nat
  ; frontA : T (listA a)
  ; nbackA : nat
  ; backA : T (listA a)
  }.

Definition mkQueueA {a} (fn : nat) (f : T (listA a)) (bn : nat) (b : T (listA a)) : M (QueueA a) :=
  tick >>
  if fn <? bn then
    let~ b' := revA b in
    let~ f' := appendA f b' in
    ret (MkQueueA (fn + bn) f' 0 (Defined NilA))
  else
    ret (MkQueueA fn f bn b).

Definition emptyA {a} : M (QueueA a) :=
  ret (MkQueueA 0 (Defined NilA) 0 (Defined NilA)).

Definition pushA {a} (q : T (QueueA a)) (x : T a) : M (QueueA a) :=
  tick >>
  let! q := force q in
  mkQueueA (nfrontA q) (frontA q) (S (nbackA q)) (Defined (ConsA x (backA q))).

Definition popA {a} (q : T (QueueA a)) : M (option (T a * T (QueueA a))) :=
  tick >>
  let! q := force q in
  let! f := force (frontA q) in
  match f with
  | NilA => ret None
  | ConsA x f =>
    let~ q := mkQueueA (pred (nfrontA q)) f (nbackA q) (backA q) in
    ret (Some (x, q))
  end.

Definition ex1 :=
  fold_left (fun qM x =>
    let~ q := qM in
    pushA q (Defined x)) (seq 0 100) emptyA.

Definition ex2 :=
  let~ q := ex1 in
  fold_right (fun _ k q =>
    let! r := popA q in
    match r with
    | None => ret (nil, q)
    | Some (x, q) =>
      let! (xs, q) := k q in
      ret (x :: xs, q)
    end) (fun q => ret (nil, q)) (seq 0 100) q.

(*
Compute (runM ex1).
Compute (runM ex2).
*)
