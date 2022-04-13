(** Another monad for laziness, based on
    "A natural semantics for lazy evaluation", by Launchbury
    https://citeseerx.ist.psu.edu/viewdoc/download?doi=10.1.1.35.2016&rep=rep1&type=pdf *)

From Coq Require Import List.
Import ListNotations.
From Clairvoyance Require Core.

Set Primitive Projections.
Set Implicit Arguments.
Set Contextual Implicit.
Set Maximal Implicit Insertion.

Inductive LF (t m : Type -> Type) (a : Type) : Type :=
| Ret (r : a)
| Bind {b : Type} (u : m b) (k : b -> m a)
| LetLazy {b : Type} (u : m b) (k : t b -> m a)
| Force (th : t a)
| Tick (u : m a)
.
(* Replacing LetLazy with Lazy : m a -> LF m (R a) would make LF an indexed type
   and annoyingly require dependently-typed programming in the definition of [eval]. *)

CoInductive L (t : Type -> Type) (a : Type) : Type := Step
  { exec : LF t (L t) a }.

(* L for Lazy and for Launchbury *)
Module Import L.

Definition ret {t a} (x : a) : L t a :=
  Step (Ret x).

Definition bind {t a b} (u : L t a) (k : a -> L t b) : L t b :=
  Step (Bind u k).

Definition let_lazy {t a b} (u : L t a) (k : t a -> L t b) : L t b :=
  Step (LetLazy u k).

Definition force {t a} (th : t a) : L t a :=
  Step (Force th).

Definition tick {t} : L t unit := Step (Tick (Step (Ret tt))).

Module Notations.
Notation "'let^' x ':=' t 'in' s" := (bind t (fun x => s)) (x as pattern, at level 90).
Notation "'let^~' x  ':=' t 'in' s" := (let_lazy t (fun x => s)) (x as pattern, at level 90).
End Notations.

End L.

Import L.Notations.

(* Big step semantics *)
Record R (a : Type) : Type := Ref
  { deref : nat }.

Inductive thunk : Type :=
| Val {a : Type} (x : a)
| Thunk {a : Type} (u : L R a).

Definition heap : Type := list thunk.

Definition empty_heap : heap := [].

Definition N (a : Type) : Type := heap -> heap -> nat -> a -> Prop.

Module N.
Definition ret {a} (x : a) : N a := fun h h' n x' =>
  h = h' /\ x = x' /\ n = 0.

Definition bind {a b} (u : N a) (k : a -> N b) : N b := fun h h'' n y =>
  exists h' m x m',
    u h h' m x /\ k x h' h'' m' y /\ n = m + m'.

Definition lazy {a} (u : L R a) : N (R a) := fun h h' n x =>
  h' = h ++ [Thunk u] /\ n = 0 /\ x = {| deref := List.length h |}.

Inductive force_ (_evalF : forall {a : Type}, L R a -> N a)
  {a} (t : R a) (h h' : heap) (n : nat) (x : a) : Prop :=
| ForceVal :
    nth_error h (deref t) = Some (Val x) -> h = h' -> n = 0 -> force_ (@_evalF) t h h' n x
| ForceThunk u :
    nth_error h (deref t) = Some (Thunk u) -> _evalF u h h' n x -> force_ (@_evalF) t h h' n x.

Definition force _evalF {a} : R a -> N a := force_ _evalF.

Definition tick : N unit := fun h h' n _ =>
  h = h' /\ n = 1.
 
End N.

Definition evalF (_evalF : forall {a : Type}, L R a -> N a) {a} (u : L R a) : N a :=
  match exec u with
  | Ret r => N.ret r
  | Bind u k => N.bind (_evalF u) (fun x => _evalF (k x))
  | LetLazy u k => N.bind (N.lazy u) (fun t => _evalF (k t))
  | Force th => N.force (@_evalF) th
  | Tick u => N.bind N.tick (fun _ => _evalF u)
  end.

Module Fix6.
Section Fix6.
Context {b : Type -> Type} {c d e : Type}.
Notation Pred := (forall (a : Type), b a -> c -> d -> e -> a -> Prop).
Definition imp (P Q : Pred) : Prop :=
  forall a xb xc xd xe x, P a xb xc xd xe x -> Q a xb xc xd xe x.
Hint Unfold imp : core.
Infix "-->" := imp (at level 90).
Inductive F (gf : Pred -> Pred) (a : Type) xb xc xd xe x : Prop :=
| InF {Q : Pred} (_ : gf Q a xb xc xd xe x) (_ : Q --> F gf)
.

Definition monotone (gf : Pred -> Pred) : Prop :=
  forall P Q : Pred, (P --> Q) -> (gf P --> gf Q).

Theorem fold (gf : Pred -> Pred) : gf (@F gf) --> @F gf.
Proof.
  red; intros * Hgf. apply (InF (Q := @F gf)); auto.
Qed.

Theorem unfold (gf : Pred -> Pred) (MON : monotone gf) : @F gf --> gf (@F gf).
Proof.
  red; intros * Hfix; destruct Hfix.
  revert H; apply MON. auto.
Qed.

Theorem induction (gf : Pred -> Pred) (MON : monotone gf)
  : forall P : Pred, (gf P --> P) -> (@F gf --> P).
Proof.
  intros P alg. red. fix SELF 7. intros * [Q Hgf Hext].
  apply alg. revert Hgf; apply MON. auto.
Qed.
End Fix6.
End Fix6.

Definition eval {a : Type} : L R a -> N a := Fix6.F evalF.

Variant listF (t : Type -> Type) (a : Type) (list_ : Type) : Type :=
| NilF
| ConsF (x : t a) (xs : t list_).

Class Data (dF : Type -> Type) : Type :=
  { d_ : Type
  ; des : d_ -> dF d_
  ; con : dF d_ -> d_
  }.

Coercion d_ : Data >-> Sortclass.

#[global] Hint Mode Data ! : typeclass_instances.

Inductive listL (a : Type) : Type :=
| NilL
| ConsL (x : R a) (xs : R (listL a))  (* not actually recursive: R (listL a) = nat *)
.

#[global] Instance Data_listL {a} : Data (listF R a) :=
  {| d_ := listL a
  ; des x := match x with ConsL x xs => ConsF x xs | NilL => NilF end
  ; con x := match x with ConsF x xs => ConsL x xs | NilF => NilL end
  |}.

CoFixpoint appendL {t : Type -> Type} {list_ : forall a, Data (listF t a)}
    {a} (xs ys : t (list_ a)) : L t (list_ a) :=
  let^ xs := force xs in
  match des xs return L t (list_ a) with
  | NilF => force ys
  | ConsF x xs => let^~ zs := appendL xs ys in ret (con (ConsF x zs))
  end.

Module Fix4.
Section Fix4.
Context {b : Type -> Type} {c : Type}.
Notation Pred := (forall (a : Type), b a -> a -> c -> Prop).
Definition imp (P Q : Pred) : Prop :=
  forall a xb xc x, P a xb xc x -> Q a xb xc x.
Hint Unfold imp : core.
Infix "-->" := imp (at level 90).
Inductive F (gf : Pred -> Pred) (a : Type) xb xc x : Prop :=
| InF {Q : Pred} (_ : gf Q a xb xc x) (_ : Q --> F gf)
.

Definition monotone (gf : Pred -> Pred) : Prop :=
  forall P Q : Pred, (P --> Q) -> (gf P --> gf Q).

Theorem fold (gf : Pred -> Pred) : gf (@F gf) --> @F gf.
Proof.
  red; intros * Hgf. apply (InF (Q := @F gf)); auto.
Qed.

Theorem unfold (gf : Pred -> Pred) (MON : monotone gf) : @F gf --> gf (@F gf).
Proof.
  red; intros * Hfix; destruct Hfix.
  revert H; apply MON. auto.
Qed.

Theorem induction (gf : Pred -> Pred) (MON : monotone gf)
  : forall P : Pred, (gf P --> P) -> (@F gf --> P).
Proof.
  intros P alg. red. fix SELF 5. intros * [Q Hgf Hext].
  apply alg. revert Hgf; apply MON. auto.
Qed.
End Fix4.
End Fix4.

Import Clairvoyance.Core.

Definition evalMF (_evalMF : forall {a : Type}, L T a -> M a) {a} (u : L T a) : M a :=
  match exec u with
  | Ret r => ret r
  | Bind u k => bind (_evalMF u) (fun x => _evalMF (k x))
  | LetLazy u k => bind (Core.thunk (_evalMF u)) (fun t => _evalMF (k t))
  | Force th => force th
  | Tick u => bind tick (fun _ => _evalMF u)
  end.

Definition evalM {a} : L T a -> M a := Fix4.F evalMF.
