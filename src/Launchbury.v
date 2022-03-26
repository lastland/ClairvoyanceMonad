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

Record T (a : Type) : Type := Ref
  { deref : nat }.

Inductive LF (m : Type -> Type) (a : Type) : Type :=
| Ret (r : a)
| LetLazy {b : Type} (u : m b) (k : T b -> m a)
| LetForce {b : Type} (t : T b) (k : b -> m a)
| Tick (u : m a)
.

CoInductive L (a : Type) : Type := Step
  { exec : LF L a }.

Definition ret {a} (x : a) : L a :=
  Step (Ret x).

Definition subst {a b} (k : a -> L b) : L a -> L b :=
  cofix subst_k (u : L a) : L b := Step
    match exec u with
    | Ret r => exec (k r)
    | LetLazy u h => LetLazy u (fun x => subst_k (h x))
    | LetForce u h => LetForce u (fun x => subst_k (h x))
    | Tick u => Tick (subst_k u)
    end.

Definition bind {a b} (u : L a) (k : a -> L b) : L b := subst k u.

Definition let_lazy {a b} (u : L a) (k : T a -> L b) : L b :=
  Step (LetLazy u k).

Definition let_force {a b} (t : T a) (k : a -> L b) : L b :=
  Step (LetForce t k).

Definition tick : L unit := Step (Tick (Step (Ret tt))).

(* Big step semantics *)
Inductive thunk : Type :=
| Val {a : Type} (x : a)
| Thunk {a : Type} (u : L a).

Definition heap : Type := list thunk.

Definition N (a : Type) : Type := heap -> heap -> nat -> a -> Prop.

Module N.
Definition ret {a} (x : a) : N a := fun h h' n x' =>
  h = h' /\ x = x' /\ n = 0.

Definition bind {a b} (u : N a) (k : a -> N b) : N b := fun h h'' n y =>
  exists h' m x m',
    u h h' m x /\ k x h' h'' m' y /\ n = m + m'.

Definition lazy {a} (u : L a) : N (T a) := fun h h' n x =>
  h' = h ++ [Thunk u] /\ n = 0 /\ x = {| deref := List.length h |}.

Inductive force_ (_evalF : forall {a : Type}, L a -> N a)
  {a} (t : T a) (h h' : heap) (n : nat) (x : a) : Prop :=
| ForceVal :
    nth_error h (deref t) = Some (Val x) -> h = h' -> n = 0 -> force_ (@_evalF) t h h' n x
| ForceThunk u :
    nth_error h (deref t) = Some (Thunk u) -> _evalF u h h' n x -> force_ (@_evalF) t h h' n x.

Definition force _evalF {a} : T a -> N a := force_ _evalF.

Definition tick : N unit := fun h h' n _ =>
  h = h' /\ n = 1.
 
End N.

Definition evalF (_evalF : forall {a : Type}, L a -> N a) {a} (u : L a) : N a :=
  match exec u with
  | Ret r => N.ret r
  | LetLazy u k => N.bind (N.lazy u) (fun t => _evalF (k t))
  | LetForce u k => N.bind (N.force (@_evalF) u) (fun x => _evalF (k x))
  | Tick u => N.bind N.tick (fun _ => _evalF u)
  end.

Section Fix.
Context {b : Type -> Type} {c d e : Type}.
Notation Pred := (forall (a : Type), b a -> c -> d -> e -> a -> Prop).
Definition imp (P Q : Pred) : Prop :=
  forall a xb xc xd xe x, P a xb xc xd x xe -> Q a xb xc xd x xe.
Hint Unfold imp : core.
Infix "-->" := imp (at level 90).
Inductive fix6 (gf : Pred -> Pred) (a : Type) xb xc xd xe x : Prop :=
| InFix6 {Q : Pred} (_ : gf Q a xb xc xd xe x) (_ : Q --> fix6 gf)
.

Definition monotone6 (gf : Pred -> Pred) : Prop :=
  forall P Q : Pred, (P --> Q) -> (gf P --> gf Q).

Theorem fix6_fold (gf : Pred -> Pred) : gf (@fix6 gf) --> @fix6 gf.
Proof.
  red; intros * Hgf. apply (InFix6 (Q := @fix6 gf)); auto.
Qed.

Theorem fix6_unfold (gf : Pred -> Pred) (MON : monotone6 gf) : @fix6 gf --> gf (@fix6 gf).
Proof.
  red; intros * Hfix; destruct Hfix.
  revert H; apply MON. auto.
Qed.

Theorem fix6_induction (gf : Pred -> Pred) (MON : monotone6 gf)
  : forall P : Pred, (gf P --> P) -> (@fix6 gf --> P).
Proof.
  intros P alg. red. fix SELF 7. intros * [Q Hgf Hext].
  apply alg. revert Hgf; apply MON. auto.
Qed.
End Fix.

Definition eval {a : Type} : L a -> N a := fix6 evalF.

Inductive listL (a : Type) : Type :=
| NilL
| ConsL (x : T a) (xs : T (listL a))  (* not actually recursive: T (listL a) = nat *)
.
