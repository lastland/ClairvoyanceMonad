(** A formalization of the Section 4 of the paper [Reasoning about the
garden of forking paths].

Semantics:
- [BigStep]: Hackett & Hutton's Clairvoyant CBV (operational semantics)
- [eval]: our monadic semantics

Equivalence:
- [soundness]: [BigStep] semantics are a subset of [eval] semantics.
- [adequacy]: [eval] semantics are a subset of [BigStep] semantics.

Putting those together, the equivalence is made explicit in
[soundness_and_adequacy].
 *)

Set Implicit Arguments.
Set Contextual Implicit.

From Coq Require Import Arith Psatz Setoid Morphisms.

From Clairvoyance Require Import Clairvoyance.

(** * Axioms

We use functional and propositional extensionality. *)

From Coq Require Import FunctionalExtensionality.

(* Propositional extensionality *)
Axiom prop_ext : forall P Q, (P <-> Q) -> P = Q.

(* We spent some effort to minimize the dependency on axioms,
   that's why you'll see us defining some extensional equality relations
   explicitly, even though they're equivalent to Leibniz equality [eq]
   under those two axioms. *)

Declare Scope ctx_scope.

(** * Helper functions. *)

(** The [fmap] function for the thunk datatype [T]. *)
Definition mapT {a b} (f : a -> b) (t : T a) : T b :=
  match t with
  | Undefined => Undefined
  | Thunk x => Thunk (f x)
  end.

Definition T_prop {a} (f : a -> Prop) (t : T a) : Prop :=
  match t with
  | Undefined => True
  | Thunk x => f x
  end.

(** * Extensional equality and inequality on [M]. *)

(** Two sets [u] and [v] are equal when they have the same elements.
    Since we've assumed functional and propositional extensionality,
    this is equivalent to Leibniz equality [eq]. Otherwise we would have
    to sprinkle [eq_M] all over the place. *)
Definition eq_M {a} (u v : M a) : Prop := forall x n, u x n <-> v x n.

(** A set [t], viewed as a computation, "costs less" than another computation
    [t'] when it can produce (at least) all same results as [t] for less.
    This is only used for facts about "simplifying ticks" (Section 4.4),
    unrelated to soundness and adequacy. *)
Definition le_M {a} (t t' : M a) : Prop :=
  forall x n, t' x n -> exists n', t x n' /\ n' <= n.

Declare Scope M_scope.
Delimit Scope M_scope with M.

Infix "<=" := le_M : M_scope.
Infix "=" := eq_M : M_scope.

(** The extensional equality [eq_M] is reflexive. *)
Lemma Reflexive_eq_M {a} (u : M a) : eq_M u u.
Proof. firstorder. Qed.

(** The extensional equality [eq_M] is symmetric. *)
Lemma Symmetric_eq_M {a} (u v : M a) : eq_M u v -> eq_M v u.
Proof. firstorder. Qed.

(** [le_M] is reflexive. *)
Lemma Reflexive_le_M {a} (u : M a) : (u <= u)%M.
Proof.
  red; firstorder.
Qed.

(** * Lemmas for [eq_M]. *)

(** Respectfulness lemmas: [eq_M] is preserved by the
    various operations we've defined on [M]. *)

(** A reasoning rule for extensional equality on [M]: if [u1] and [u2] are
    equal, and [k1] and [k2] are equal, then [bind u1 k1] and [bind u2 k2] are
    also equal. *)
Lemma eq_M_bind {a b} (u1 u2 : M a) (k1 k2 : a -> M b)
  : (u1 = u2)%M ->
    (forall x, (k1 x = k2 x)%M) ->
    (bind u1 k1 = bind u2 k2)%M.
Proof.
  unfold eq_M. firstorder.
  repeat eexists; eauto. apply H; eauto. apply H0; eauto.
  repeat eexists; eauto. apply H; eauto. apply H0; eauto.
Qed.

(** Similar to the above theorem but for [thunk]s. *)
Lemma eq_M_thunk {a} (u1 u2 : M a) :
  (u1 = u2)%M -> (thunk u1 = thunk u2)%M.
Proof.
  intros H [] ?; cbn; auto. reflexivity.
Qed.

(** Similar to the above theorem but for [ret]s. *)
Lemma eq_M_ret {a} (x1 x2 : a) :
  x1 = x2 -> (ret x1 = ret x2)%M.
Proof.
  unfold eq_M. firstorder congruence.
Qed.

(** * Lemmas for [le_M]. *)

Lemma bind_le {a b} (u1 u2 : M a) (k1 k2 : a -> M b)
  : (u1 <= u2)%M ->
    (forall x, k1 x <= k2 x)%M ->
    (bind u1 k1 <= bind u2 k2)%M.
Proof.
  intros Hu Hk y n (x & mx & my & Hu2 & Hk2 & Hn).
  apply Hu in Hu2; apply Hk in Hk2.
  destruct Hu2 as (mx1 & ? & ?).
  destruct Hk2 as (my1 & ? & ?).
  exists (mx1 + my1). split; [ | lia ].
  exists x, mx1, my1; eauto.
Qed.

Lemma bind_eq_le {a b} (u : M a) (k1 k2 : a -> M b)
  : (forall x, k1 x <= k2 x)%M ->
    ((bind u k1) <= (bind u k2))%M.
Proof.
  apply bind_le. apply Reflexive_le_M.
Qed.

Lemma bind_le_r {a b} (u : M a) (u1 u2 : M b)
  : (u1 <= u2)%M -> (u1 <= bind u (fun _ => u2))%M.
Proof.
  intros H y n (x & mx & my2 & Hx & Hy2 & Hn).
  apply H in Hy2. destruct Hy2 as (my1 & ? & ?).
  exists my1; split; [ auto | lia ].
Qed.

Lemma thunk_le {a} (u1 u2 : M a)
  : (u1 <= u2)%M -> (thunk u1 <= thunk u2)%M.
Proof.
  intros H [y | ] n; cbn; eauto.
Qed.

Lemma forcing_le {a b} (x : T a) (k1 k2 : a -> M b)
  : T_prop (fun x => k1 x <= k2 x)%M x -> (forcing x k1 <= forcing x k2)%M.
Proof.
  destruct x; cbn; [ auto | ].
  unfold le_M. contradiction.
Qed.

(** * Simplifying ticks.
    
    The theorems justify the rewrite rules discussed in Section 4.4.
    This is unrelated to soundness and adequacy, which are
    the main results of this file. *)

Lemma bind_tick {a b} (t : M a) (k : a -> M b)
  : (bind t (fun x => tick >> k x) = tick >> bind t k)%M.
Proof.
  unfold bind, tick, eq_M. firstorder.
  - eexists tt, 1, _. split; auto.
    split; [ eexists _, _, _; split; eauto |]. lia.
  - eexists _, _, _; split; [ eauto | ].
    split; [ eexists tt, _, _; split; eauto |]. lia.
Qed.

Lemma thunk_tick {a} (u : M a)
  : (thunk (tick >> u) <= tick >> thunk u)%M.
Proof.
  unfold thunk, bind, tick, le_M; firstorder.
  destruct x.
  - eexists; split; [ | constructor ]. exists tt. eauto.
  - exists 0; split; auto. lia.
Qed.


Module Lambda.

(** * The calculus with folds. *)

(** * Fig. 6. *)  

(** Types.
    
    Our formalization of the calculus slightly generalizes what we present in
    the paper. In particular, (1) we add a product type, and (2) we generalize
    the [unit] type of Fig. 6 to an arbitrary set of base types. *)
Inductive Ty : Type :=
| Arr  : Ty -> Ty -> Ty  (* Functions *)
| Prod : Ty -> Ty -> Ty  (* Products *)
| List : Ty -> Ty  (* A basic recursive data type: List a = Unit + a * List a *)
| Base : Type -> Ty  (* Base types are arbitrary types of the host language (Coq) *)
.

(** Context.

    We are using a nameless representation adapted from de Bruijn indices here.
    
    Learn more about de Bruijn indices here:
    [https://en.wikipedia.org/wiki/De_Bruijn_index]

    Instead of using natural numbers as in de Bruijn indices, we index
    variables by the context they belong to, ensuring that variables are
    always well-scoped by construction. *)

(** A context is a list of types. *)
Inductive Ctx : Type :=
| NilCtx
| ConsCtx : Ctx -> Ty -> Ctx
.

Infix ":,:" := ConsCtx (at level 50).

(** A variable is an index into a context.
    Its type parameters associate it to the context it indexes into,
    and the type it points to. It is essentially a natural number (de Bruijn
    index) but with type information embedded in it.
    [n : V g u] means that the [n]-th element in [g] is [u]. *)
Inductive V : Ctx -> Ty -> Type :=
| Here g x : V (g :,: x) x
| There g x y : V g y -> V (g :,: x) y
.

(** Terms. *)

Inductive Tm (g : Ctx) : Ty -> Type :=
| Let a b : Tm g a -> Tm (g :,: a) b -> Tm g b
| App a b : Tm g (Arr a b) -> V g a -> Tm g b
| Var a : V g a -> Tm g a
| Fun a b : Tm (g :,: a) b -> Tm g (Arr a b)
| Pair a b : V g a -> V g b -> Tm g (Prod a b)
| Fst a b : V g (Prod a b) -> Tm g a
| Snd a b : V g (Prod a b) -> Tm g b
| Nil a : Tm g (List a)
| Cons a : V g a -> V g (List a) -> Tm g (List a)
| Foldr a b : Tm g b -> Tm (g :,: a :,: b) b -> V g (List a) -> Tm g b
| Bas (b : Type) : b -> Tm g (Base b)
.

(* ---------------------- Denotational semantics (our contribution) ---------------------- *)

(** * The approximation of [List]s. *)
Unset Elimination Schemes.

Inductive ListA (a : Type) : Type :=
| NilA : ListA a
| ConsA : T a -> T (ListA a) -> ListA a
.

(* For [ListA], we need to define our own induction principle because Coq cannot
   generate the correct induction principles for nested inductive datatypes.

   See the [Nested Inductive Types] section in CPDT
   (http://adam.chlipala.net/cpdt/html/Cpdt.InductiveTypes.html). *)
Definition ListA_ind {a} (P : ListA a -> Prop)
    (H_NilA : P NilA)
    (H_ConsA : forall x xs, T_prop P xs -> P (ConsA x xs))
  : forall xs, P xs.
Proof.
  fix SELF 1; intros [].
  - apply H_NilA.
  - apply H_ConsA; destruct t0; cbn; [ apply SELF | auto].
Qed.

Set Elimination Schemes.

(** * The type translation. *)

(** * Fig. 7 *)

(** We translate the types in the calculus with folds to the types in
    Gallina. *)
Fixpoint toType (u : Ty) : Type :=
  match u with
  | Arr u1 u2 => T (toType u1) -> M (toType u2)
  | Prod u1 u2 => (T (toType u1) * T (toType u2))%type
  | List a => ListA (toType a)
  | Base b => b
  end.

(** We translate contexts to environments, which are heterogeneous lists
    of elements whose types are given by the context (a list of types).
    Concretely, this heterogeneous list is represented by left-nested tuples.
    The context binds thunks, hence each component is wrapped in [T]. *)
Fixpoint env (g : Ctx) : Type :=
  match g with
  | NilCtx => unit
  | ConsCtx g1 u => env g1 * T (toType u)
  end.

(** As a variable [v : V g u] is an index into a context [g],
    it can be used to look up the corresponding element in a heterogeneous list
    indexed by [g], which must have type [T (toType u)] by definition of [env g]. *)
Fixpoint lookup {g u} (v : V g u) : env g -> T (toType u) :=
  match v with
  | Here => fun ex => snd ex
  | There v1 => fun ex => lookup v1 (fst ex)
  end.

(** * Fig. 9 *)

(** * Definitions of [foldrA]. *)

Fixpoint foldrA' {a b} (n : M b) (c : T a -> T b -> M b) (x' : ListA a)
  : M b :=
  let! _ := tick in
  match x' with
  | NilA => n
  | ConsA x1 x2 =>
    let! y2 := thunk (foldrA' n c $! x2) in
    c x1 y2
  end.

Definition foldrA {a b} (n : M b) (c : T a -> T b -> M b)
    (x : T (ListA a)) : M b :=
  foldrA' n c $! x.

(** * Fig. 8 *)

(** * The term translation, aka. a denotational semantics.

    The [eval]uation of a term [t] in some environment [e : env g]
    is a computation (in the monad [M]) producing a value of type [toType u]. *)
Fixpoint eval {g u} (t : Tm g u) : env g -> M (toType u) := fun e =>
  match t with
  | Let t1 t2 => fun e =>
    tick >>
    let! x := thunk (eval t1 e) in
    eval t2 (e, x)
  | App t1 v => fun e =>
    tick >>
    let! f := eval t1 e in
    f (lookup v e)
  | Var v => fun e => tick >> force (lookup v e)
  | Fun f => fun e => ret (fun x => eval f (e, x))
  | Pair v1 v2 => fun e =>
    ret (lookup v1 e, lookup v2 e)
  | Fst v => fun e => tick >>
    let! x := force (lookup v e) in force (fst x)
  | Snd v => fun e => tick >>
    let! x := force (lookup v e) in force (snd x)
  | Nil => fun _ => ret NilA
  | Cons v1 v2 => fun e => ret (ConsA (lookup v1 e) (lookup v2 e))
  | Foldr n c v1 => fun e =>
    foldrA
      (eval n e)
      (fun x1 y2 => eval c (e, x1, y2))
      (lookup v1 e)
  | Bas b => fun _ => ret b
  end e.

(** Example: append

    This is an [appendA] we translate from [append] written in the calculus with
    folds. For code presented in Fig. 10, which is a translation from the code
    written in Gallina in Fig. 1, refer to the [Clairvoyance.v] file. *)
Notation V0 := Here.
Notation V1 := (There Here).

Definition append {a} : Tm (NilCtx :,: List a :,: List a) (List a) :=
  Foldr (Var V0) (Cons V1 V0) V1.

(* Manually translated with simplifications (fewer ticks; see discussion from Section 4.3). *)

Fixpoint appendA_ {a} (xs : ListA a) (ys : T (ListA a)) : M (ListA a) :=
  tick >>
  match xs with
  | NilA => force ys
  | ConsA x xs =>
    let! zs := thunk ((fun xs => appendA_ xs ys) $! xs) in
    ret (ConsA x zs)
  end.

Definition appendA {a} (xs ys : T (ListA a)) : M (ListA a) :=
  (fun xs => appendA_ xs ys) $! xs.

(** The costs of [append] and [appendA] are asymptotically equivalent. Informally:
    cost(appendA) <= cost(append) <= 2 * cost(appendA)

    The two main theorems are [appendA_le_append] and [append_le_appendA].
*)
Lemma appendA_le_append_ {a} (xs : ListA (toType a)) (ys : T (ListA (toType a)))
  : (appendA_ xs ys <= eval (Foldr (g := NilCtx :,: _ :,: _) (Var V0) (Cons V1 V0) V1) (tt, Thunk xs, ys))%M.
Proof.
  induction xs; intros; cbn.
  - apply bind_eq_le; intros _. apply bind_le_r, Reflexive_le_M.
  - apply bind_eq_le; intros _. apply bind_le.
    + apply thunk_le. apply forcing_le.
      destruct xs; cbn in *; eauto.
    + intros. apply Reflexive_le_M.
Qed.

(** [appendA] costs at most as much as the denotation of [append]. *)
Theorem appendA_le_append {a} (xs ys : T (ListA (toType a)))
  : (appendA xs ys <= eval append (tt, xs, ys))%M.
Proof.
  apply forcing_le; destruct xs; cbn; [ | auto ].
  eapply appendA_le_append_.
Qed.

(** Multiply the cost of a computation [u] by a constant [c]. *)
Definition costMul {a} (c : nat) (u : M a) : M a :=
  fun x n => exists m, u x m /\ c * m = n.

Definition le_costMul {a} (c : nat) (u1 u2 : M a)
  : u2 {{ fun x2 n2 => u1 [[ fun x1 n1 => x2 = x1 /\ n1 <= c * n2 ]] }} ->
    (u1 <= costMul c u2)%M.
Proof.
  intros H x n (ndiv & Hx & Hn).
  apply H in Hx. destruct Hx as (y & ny & Hy & <- & Hny).
  eexists; split; [ eauto | lia ].
Qed.

Lemma append_le_appendA_ {a} (xs : ListA (toType a)) (ys : T (ListA (toType a)))
  : (appendA_ xs ys)
      {{ fun x2 n2 =>
           (eval (Foldr (g := NilCtx :,: _ :,: _) (Var V0) (Cons V1 V0) V1) (tt, Thunk xs, ys))
             [[ fun x1 n1 => x2 = x1 /\ n1 <= 2 * n2 ]] }}.
Proof.
  induction xs as [ | x xs IH]; cbn; intros; mgo'.
  - destruct x0; cbn in *.
    + mgo'. apply optimistic_thunk_go. mgo'.
    + intros ? ?. inversion 1; subst. mgo'.
      apply optimistic_thunk_go. relax. apply (IH x0 n). apply H.
      intros; mgo'. destruct H1; subst. intuition.
  - apply optimistic_skip. mgo'.
Qed.

(** The denotation of [append] costs at most twice as much as [appendA]. *)
Theorem append_le_appendA {a} (xs ys : T (ListA (toType a)))
  : (eval append (tt, xs, ys) <= costMul 2 (appendA xs ys))%M.
Proof.
  apply le_costMul.
  unfold appendA; cbn; unfold foldrA.
  destruct xs.
  - cbn. apply append_le_appendA_.
  - intros ? ? [].
Qed.

(** * Operational semantics of Hackett & Hutton (2019).

    In this part, we formalize the operational semantics presented in Fig. 3 of
    Hackett & Hutton (2019). The paper can be found at:
    [https://dl.acm.org/doi/10.1145/3341718] *)

(** Syntactic values.

    Syntactic values are closures and base values. *)
Variant Vl (g : Ctx) : Ty -> Type :=
| VLam a b : Tm (g :,: a) b -> Vl g (Arr a b)
| VPair a b : V g a -> V g b -> Vl g (Prod a b)
| VNil a : Vl g (List a)
| VCons a : V g a -> V g (List a) -> Vl g (List a)
| VBas b : b -> Vl g (Base b)
.

(** Heaps are lists of syntactic values. *)
Inductive Heap : Ctx -> Type :=
| HNil : Heap NilCtx
| HCons g a : Heap g -> T (Vl g a) -> Heap (g :,: a)
.

Infix ":*:" := HCons (at level 40).

(** General operations on syntax *)

(** Append contexts *)
Fixpoint app_Ctx (g g' : Ctx) : Ctx :=
  match g' with
  | NilCtx => g
  | ConsCtx g' u => ConsCtx (app_Ctx g g') u
  end.

Infix "++" := app_Ctx : ctx_scope.

Bind Scope ctx_scope with Ctx.

(** The first element of a non-empty heap. *)
Definition here {g u} (e : Heap (g :,: u)) : T (Vl g u) :=
  match e in Heap g0 return
    match g0 with
    | NilCtx => True
    | (_ :,: u) => T (Vl _ u)
    end with
  | HNil => I
  | HCons _ h => h
  end.

(** The tail of a non-empty heap. *)
Definition there {g u} (e : Heap (g :,: u)) : Heap g :=
  match e in Heap g0 return
    match g0 with
    | NilCtx => True
    | (g :,: _) => Heap g
    end with
  | HNil => I
  | HCons t _ => t
  end.

(** Renaming from context [g] to context [g'] (a substitution whose codomain is
    variables). *)
Definition Rnm (g g' : Ctx) := forall a, V g a -> V g' a.

(** An eliminator for [V], when the context is explicitly of the form [g :,: a]. *)
Definition elimV {g a b} (v : V (g :,: a) b) {r : Ty -> Type} : (V g b -> r b) -> r a -> r b :=
  match v in V g_ b_ return
    match g_ with
    | (g :,: a) => _
    | _ => False
    end with
  | Here => fun _ y => y
  | There v => fun x _ => x v
  end.

(** Extend a renaming with a variable (renamed to itself). *)
Definition shift {g g' : Ctx} (s : Rnm g g') {a} : Rnm (g :,: a) (g' :,: a) :=
  fun _ v => elimV v (fun v => There (s _ v)) Here.

(** Helper renaming for the operational semantics of [Foldr].
    Given [fcons] in context [g1 :,: a :,: b], we rename it by
    1. looking up [a] in the context [g1];
    2. applying some substitution on [g2]. *)
Definition shiftAlgCons {g1 g2 a b} (v1 : V g1 a) (s : Rnm g1 g2)
  : Rnm (g1 :,: a :,: b) (g2 :,: b) :=
  shift (fun _ v => s _ (elimV v (fun v => v) v1)).

(** Restriction of a renaming, forgetting one variable in the original context. *)
Definition restr {g g' : Ctx} {a} (s : Rnm (g :,: a) g') : Rnm g g' :=
  fun _ v => s _ (There v).

(** Rename a term. *)
Fixpoint rename {g g'} (s : Rnm g g') {a} (t : Tm g a) : Tm g' a :=
  match t with
  | Let t1 t2 => Let (rename s t1) (rename (shift s) t2)
  | App t1 v => App (rename s t1) (s _ v)
  | Var v => Var (s _ v)
  | Fun t1 => Fun (rename (shift s) t1)
  | Pair v1 v2 => Pair (s _ v1) (s _ v2)
  | Fst v => Fst (s _ v)
  | Snd v => Snd (s _ v)
  | Nil => Nil
  | Cons v1 v2 => Cons (s _ v1) (s _ v2)
  | Foldr t1 t2 v => Foldr (rename s t1) (rename (shift (shift s)) t2) (s _ v)
  | Bas b => Bas b
  end.

(** Rename a value. *)
Definition renameVl {g g'} (s : Rnm g g') {a} (t : Vl g a) : Vl g' a :=
  match t with
  | VLam t1 => VLam (rename (shift s) t1)
  | VPair v1 v2 => VPair (s _ v1) (s _ v2)
  | VNil => VNil
  | VCons v1 v2 => VCons (s _ v1) (s _ v2)
  | VBas b => VBas b
  end.

Definition id_Rnm {g} : Rnm g g :=
  fun _ v => v.

Definition cat_Rnm {g g' g''} : Rnm g g' -> Rnm g' g'' -> Rnm g g'' :=
  fun s1 s2 _ v => s2 _ (s1 _ v).

Infix ">>>" := cat_Rnm (at level 40).

(** Look up a value in a heap indexed by a variable [v] and rename the result.
    This is equivalent to a composition of [lookup'] and [renameVl],
    except this function is needed to define [lookup'] in the first place. *)
Fixpoint lookup_' {g g' u} (v : V g u) : Rnm g g' -> Heap g -> T (Vl g' u) :=
  match v with
  | Here => fun s e => mapT (renameVl (restr s)) (here e)
  | There v1 => fun s gx => lookup_' v1 (restr s) (there gx)
  end.

(** Look up a value in a heap indexed by a variable [v]. *)
Definition lookup' {g u} (v : V g u) : Heap g -> T (Vl g u) :=
  lookup_' v id_Rnm.

(** A helper for factoring the rules for [Foldr], which involves nondeterminism like [Let].
    Either run a computation (according to the given [BigStep_] relation,
    wrapping the result in a [Thunk]), or do nothing (returning [Undefined]). *)
Inductive LazyStep g u (e : Heap g) (BigStep_ : forall g', Rnm g g' -> Heap g' -> Vl g' u -> nat -> Prop)
  : forall g', Rnm g g' -> Heap g' -> T (Vl g' u) -> nat -> Prop :=
| LazyStep_SKIP : LazyStep e BigStep_ id_Rnm e Undefined 0
| LazyStep_STEP g' (s' : Rnm g g') e' r n
  : BigStep_ g' s' e' r n ->
    LazyStep e BigStep_ s' e' (Thunk r) n
.

Definition vthere {g a} : Rnm g (g :,: a) := fun _ v => There v.

(* A helper for [BigStep]'s induction principle.
   Monotonicity of [LazyStep] as a function on relations. *)
Lemma LazyStep_mon g u (e : Heap g)
    (BigStep_ BigStep_' : forall g', Rnm g g' -> Heap g' -> Vl g' u -> nat -> Prop)
  : (forall g' (s' : Rnm g g') (e' : Heap g') (v : Vl g' u) (n : nat),
       BigStep_ g' s' e' v n -> BigStep_' g' s' e' v n) ->
    forall g' (s' : Rnm g g') (e' : Heap g') (v : T (Vl g' u)) (n : nat),
      LazyStep e BigStep_ s' e' v n -> LazyStep e BigStep_' s' e' v n.
Proof.
  intros H * []; constructor; [ apply H; assumption ].
Defined.

Unset Elimination Schemes.

(** [and] lifted to relations. *)
Definition andBS {g u}
    (BigStep_ BigStep_' : forall g', Rnm g g' -> Heap g' -> Vl g' u -> nat -> Prop) :=
  fun g' s' e' v n => BigStep_ g' s' e' v n /\ BigStep_' g' s' e' v n.

(** [BigStep t1 e1 s2 e2 v2 n2]:
The term [t1] in heap [e1] evaluates to value [v2] in heap [e2] in time [n2],
and [s2] is a mapping from locations in [e1] to locations in [e2].

The extra complexity is mainly due to our intrinsically typed syntax,
for which we have to rename to evaluate some terms in a modified heap. *)
Inductive BigStep : forall g u, Tm g u -> Heap g -> forall g', Rnm g g' -> Heap g' -> Vl g' u -> nat -> Prop :=
| BigStep_Let_SKIP g a b (t1 : Tm g a) (t2 : Tm (g :,: a) b) (e : Heap g) g' (s' : Rnm _ g') e' r n
  : BigStep t2 (e :*: Undefined) (g' := g') s' e' r n ->
    BigStep (Let t1 t2) e (restr s') e' r (S n)
| BigStep_Let_STEP g a b (t1 : Tm g a) (t2 : Tm (g :,: a) b) (e : Heap g)
    g1 (s1 : Rnm _ g1) e1 r1 n1
    g2 (s2 : Rnm _ g2) e2 r2 n2
  : BigStep t1 e s1 e1 r1 n1 ->
    BigStep (rename (shift s1) t2) (e1 :*: Thunk r1) s2 e2 r2 n2 ->
    BigStep (Let t1 t2) e (s1 >>> restr s2) e2 r2 (S (n1 + n2))
| BigStep_App g a b (t : Tm g (Arr a b)) (v : V g a) e
    g1 (s1 : Rnm _ g1) (e1 : Heap g1) r1 n1
    g2 (s2 : Rnm _ g2) (e2 : Heap g2) r2 n2
  : BigStep t e s1 e1 (VLam r1) n1 ->
    BigStep r1 (e1 :*: lookup' (s1 _ v) e1) s2 e2 r2 n2 ->
    BigStep (App t v) e (s1 >>> restr s2) e2 r2 (S (n1 + n2))
| BigStep_Var g a (v : V g a) e r
  : Thunk r = lookup' v e ->
    BigStep (Var v) e id_Rnm e r 1
| BigStep_Fun g a b (t : Tm (g :,: a) b) e
  : BigStep (Fun t) e id_Rnm e (VLam t) 0
| BigStep_Pair g a b (v1 : V g a) (v2 : V g b) e
  : BigStep (Pair v1 v2) e id_Rnm e (VPair v1 v2) 0
| BigStep_Fst g a b (v : V g (Prod a b)) e v1 v2 r1
  : Thunk (VPair v1 v2) = lookup' v e ->
    Thunk r1 = lookup' v1 e ->
    BigStep (Fst v) e id_Rnm e r1 1
| BigStep_Snd g a b (v : V g (Prod a b)) e v1 v2 r2
  : Thunk (VPair v1 v2) = lookup' v e ->
    Thunk r2 = lookup' v2 e ->
    BigStep (Snd v) e id_Rnm e r2 1
| BigStep_Nil g a (e : Heap g)
  : BigStep (@Nil _ a) e id_Rnm e VNil 0
| BigStep_Cons g a (v1 : V g a) (v2 : V g (List a)) e
  : BigStep (Cons v1 v2) e id_Rnm e (VCons v1 v2) 0
| BigStep_Foldr_Nil g a b (fnil : Tm g b) fcons (v : V g (List a)) e
    g1 (s1 : Rnm _ g1) (e1 : Heap g1) r1 n1
  : Thunk VNil = lookup' v e ->
    BigStep fnil e s1 e1 r1 n1 ->
    BigStep (Foldr fnil fcons v) e s1 e1 r1 (S n1)
| BigStep_Foldr_Node g a b (fnil : Tm g b) (fcons : Tm (g :,: a :,: b) b) v e v1 v2
    g1 (s1 : Rnm _ g1) (e1 : Heap g1) r1 n1
    g2 (s2 : Rnm _ g2) (e2 : Heap g2) r2 n2
  : Thunk (VCons v1 v2) = lookup' v e ->
    LazyStep e (@BigStep g b (Foldr fnil fcons v2) e) s1 e1 r1 n1 ->
    BigStep (rename (shiftAlgCons v1 s1) fcons) (e1 :*: r1) s2 e2 r2 n2 ->
    BigStep (Foldr fnil fcons v) e (s1 >>> restr s2) e2 r2 (S (n1 + n2))
| BigStep_Base g b (x : b) e
  : BigStep (Bas (g := g) x) e id_Rnm e (VBas x) 0
.

(** [BigStep] is a nested inductive type, so we must again define its
induction principle by hand (this is mostly copy-pasted from the wrong
induction principle generated by Coq, and fixing the [BigStep_Foldr_Node] case. *)
Definition BigStep_ind :
forall
  P : forall (g : Ctx) (u : Ty),
      Tm g u ->
      Heap g -> forall g' : Ctx, Rnm g g' -> Heap g' -> Vl g' u -> nat -> Prop,
(forall (g : Ctx) (a b : Ty) (t1 : Tm g a) (t2 : Tm (g :,: a) b)
   (e : Heap g) (g' : Ctx) (s' : Rnm (g :,: a) g')
   (e' : Heap g') (r : Vl g' b) (n : nat),
 BigStep t2 (e :*: Undefined) s' e' r n ->
 P (g :,: a) b t2 (e :*: Undefined) g' s' e' r n ->
 P g b (Let t1 t2) e g' (restr s') e' r (S n)) ->
(forall (g : Ctx) (a b : Ty) (t1 : Tm g a) (t2 : Tm (g :,: a) b)
   (e : Heap g) (g1 : Ctx) (s1 : Rnm g g1) (e1 : Heap g1)
   (r1 : Vl g1 a) (n1 : nat) (g2 : Ctx) (s2 : Rnm (g1 :,: a) g2)
   (e2 : Heap g2) (r2 : Vl g2 b) (n2 : nat),
 BigStep t1 e s1 e1 r1 n1 ->
 P g a t1 e g1 s1 e1 r1 n1 ->
 BigStep (rename (shift s1) t2) (e1 :*: Thunk r1) s2 e2 r2 n2 ->
 P (g1 :,: a) b (rename (shift s1) t2) (e1 :*: Thunk r1) g2 s2 e2 r2 n2 ->
 P g b (Let t1 t2) e g2 (s1 >>> restr s2) e2 r2 (S (n1 + n2))) ->
(forall (g : Ctx) (a b : Ty) (t : Tm g (Arr a b))
   (v : V g a) (e : Heap g) (g1 : Ctx) (s1 : Rnm g g1)
   (e1 : Heap g1) (r1 : Tm (g1 :,: a) b) (n1 : nat)
   (g2 : Ctx) (s2 : Rnm (g1 :,: a) g2) (e2 : Heap g2)
   (r2 : Vl g2 b) (n2 : nat),
 BigStep t e s1 e1 (VLam r1) n1 ->
 P g (Arr a b) t e g1 s1 e1 (VLam r1) n1 ->
 BigStep r1 (e1 :*: lookup' (s1 a v) e1) s2 e2 r2 n2 ->
 P (g1 :,: a) b r1 (e1 :*: lookup' (s1 a v) e1) g2 s2 e2 r2 n2 ->
 P g b (App t v) e g2 (s1 >>> restr s2) e2 r2 (S (n1 + n2))) ->
(forall (g : Ctx) (a : Ty) (v : V g a) (e : Heap g) (r : Vl g a),
 Thunk r = lookup' v e -> P g a (Var v) e g id_Rnm e r 1) ->
(forall (g : Ctx) (a b : Ty) (t : Tm (g :,: a) b) (e : Heap g),
 P g (Arr a b) (Fun t) e g id_Rnm e (VLam t) 0) ->
(forall (g : Ctx) (a b : Ty) (v1 : V g a) (v2 : V g b) (e : Heap g),
 P g (Prod a b) (Pair v1 v2) e g id_Rnm e (VPair v1 v2) 0) ->
(forall (g : Ctx) (a b : Ty) (v : V g (Prod a b))
   (e : Heap g) (v1 : V g a) (v2 : V g b) (r1 : Vl g a),
 Thunk (VPair v1 v2) = lookup' v e ->
 Thunk r1 = lookup' v1 e -> P g a (Fst v) e g id_Rnm e r1 1) ->
(forall (g : Ctx) (a b : Ty) (v : V g (Prod a b))
   (e : Heap g) (v1 : V g a) (v2 : V g b) (r2 : Vl g b),
 Thunk (VPair v1 v2) = lookup' v e ->
 Thunk r2 = lookup' v2 e -> P g b (Snd v) e g id_Rnm e r2 1) ->
(forall (g : Ctx) (a : Ty) (e : Heap g), P g (List a) Nil e g id_Rnm e VNil 0) ->
(forall (g : Ctx) (a : Ty) (v1 : V g a) (v2 : V g (List a)) (e : Heap g),
 P g (List a) (Cons v1 v2) e g id_Rnm e (VCons v1 v2) 0) ->
(forall (g : Ctx) (a b : Ty) (fnil : Tm g b)
   (fcons : Tm ((g :,: a) :,: b) b)
   (v : V g (List a)) (e : Heap g) (g1 : Ctx) (s1 : Rnm g g1)
   (e1 : Heap g1) (r1 : Vl g1 b) (n1 : nat),
 Thunk VNil = lookup' v e ->
 BigStep fnil e s1 e1 r1 n1 ->
 P g b fnil e g1 s1 e1 r1 n1 -> P g b (Foldr fnil fcons v) e g1 s1 e1 r1 (S n1)) ->
(forall (g : Ctx) (a b : Ty) (fnil : Tm g b)
   (fcons : Tm ((g :,: a) :,: b) b)
   (v : V g (List a)) (e : Heap g) (v1 : V g a) (v2 : V g (List a)) (g1 : Ctx)
   (s1 : Rnm g g1) (e1 : Heap g1) (r1 : T (Vl g1 b))
   (n1 : nat) (g2 : Ctx) (s2 : Rnm (g1 :,: b) g2) (e2 : Heap g2)
   (r2 : Vl g2 b) (n2 : nat),
 Thunk (VCons v1 v2) = lookup' v e ->
 LazyStep e (andBS (BigStep (Foldr fnil fcons v2) e) (P _ _ (Foldr fnil fcons v2) e)) s1 e1 r1 n1 ->
 BigStep (rename (shiftAlgCons v1 s1) fcons) (e1 :*: r1) s2 e2 r2 n2 ->
 P (g1 :,: b) b (rename (shiftAlgCons v1 s1) fcons)
   (e1 :*: r1) g2 s2 e2 r2 n2 ->
 P g b (Foldr fnil fcons v) e g2 (s1 >>> restr s2) e2 r2 (S (n1 + n2))) ->
(forall (g : Ctx) (b : Type) (x : b) (e : Heap g),
 P g (Base b) (Bas x) e g id_Rnm e (VBas x) 0) ->
forall (g : Ctx) (u : Ty) (t : Tm g u) (e : Heap g)
  (g' : Ctx) (r : Rnm g g') (e0 : Heap g') (v : Vl g' u)
  (n : nat), BigStep t e r e0 v n -> P g u t e g' r e0 v n.
Proof.
  intros P.
  fix SELF 23; intros;
    lazymatch goal with
    | [ H : BigStep _ _ _ _ _ _ |- _ ] => destruct H
    end.
  - apply H; auto.
  - eapply H0; eauto.
  - eapply H1; eauto.
  - eapply H2; eauto.
  - eapply H3; eauto.
  - eapply H4; eauto.
  - eapply H5; eauto.
  - eapply H6; eauto.
  - eapply H7; eauto.
  - eapply H8; eauto.
  - eapply H9; eauto.
  - eapply H10; eauto.
    revert H13; apply LazyStep_mon; constructor; auto.
  - eapply H11; eauto.
Qed.

(** * Correspondence between the two semantics *)

(** Auxiliary evaluation functions on syntactic values and heaps. *)

(** Evaluation of a syntactic value [t] in environment [e],
    to a (semantic) value of type [toType u]. *)
Definition evalVl {g u} (e : env g) (t : Vl g u) : toType u :=
  match t with
  | VLam t => fun (x : T (toType _)) => eval t (e, x)
  | VPair x y => (lookup x e, lookup y e)
  | VNil => NilA
  | VCons x1 x2 => ConsA (lookup x1 e) (lookup x2 e)
  | VBas b => b
  end.

(** Evaluation of heap [e] to an environment. *)
Fixpoint evalHeap {g} (e : Heap g) : env g :=
  match e with
  | HNil => tt
  | HCons e1 v => (evalHeap e1, mapT (evalVl (evalHeap e1)) v)
  end.

(** Rename an environment. Environment are (heterogeneous) lists,
    which are mappings from indices to values, whereas renamings
    are mappings between indices, hence they act contravariantly
    on environments. *)
Fixpoint renameEnv {g g' : Ctx} : Rnm g g' -> env g' -> env g :=
  match g with
  | NilCtx => fun _ _ => tt
  | ConsCtx g a => fun s e => (renameEnv (restr s) e, lookup (s _ Here) e)
  end.

(** Proofs (soundness, then adequacy). *)

(** The main theorems are [soundness], [adequacy], and
    [soundness_and_adequacy], which is a trivial combination of the two.

    A big intermediate lemma is [BigStep_heap_increasing], which says
    that the heap only ever grows by adding new mappings (never by
    mutating old ones).

    The other lemmas are mostly small equations,
    "commutative diagrams" equating different ways to obtain the same
    result using the above functions.
*)

(** [T] is also a functor on relations. *)
Inductive eq_T {a b} (r : a -> b -> Prop) : T a -> T b -> Prop :=
| eq_T_Discarded : eq_T r Undefined Undefined
| eq_T_Thunk x y : r x y -> eq_T r (Thunk x) (Thunk y)
.

Ltac lucky_forward1 :=
  lazymatch goal with
  | [ H : optimistic (?t _) _ |- optimistic (?t _) _ ] => eapply optimistic_mon with (1 := H); intros ? ? [<- ->]
  | [ H : forall _ _, optimistic (?t _) _ |- optimistic (?t _) _ ] => eapply optimistic_mon with (1 := H _ _); intros ? ? []
  end.

Ltac lucky_forward :=
  repeat (mforward idtac + lucky_forward1).

(** Eta rule for heaps. *)
Lemma eta_Heap g a (e : Heap (g :,: a))
  : e = HCons (there e) (here e).
Proof.
  refine
   match e in Heap g' return
     match g' with (_ :,: _) => fun e => _ | NilCtx => fun _ => True end e
   with
   | HNil => I
   | HCons _ _ => _
   end. reflexivity.
Qed.

(** Elimination principle for variables. *)
Lemma V_split {g a} (P : forall b, V (g :,: a) b -> Prop)
  : (forall b v, P b (There v)) -> P a Here ->
    forall b (v : V (g :,: a) b), P b v.
Proof.
  intros H1 H2 b v; revert P H1 H2.
  refine
    match v in V g b return
      match g with
      | NilCtx => fun _ => False
      | g :,: a => fun v => forall (P : forall b, V (g :,: a) b -> Prop), _ -> _ -> P b v
      end v with
    | Here => _
    | There v => _
    end; eauto.
Qed.

(** Extensional equality is Leibniz equality (assuming functional and
    propositional extensionality). *)
Lemma eq_M_eq {a} (u1 u2 : M a) : eq_M u1 u2 -> u1 = u2.
Proof.
  intros H. do 2 (apply functional_extensionality; intros). apply prop_ext. auto.
Qed.

(** Indexing into a renamed environment is equivalent to
    renaming the index first then indexing into the original environment. *)
Lemma lookup_renameEnv {g g'} (s : Rnm g g') (e : env g') {a} (v : V g a)
  : lookup v (renameEnv s e) = lookup (s _ v) e.
Proof.
  induction v; cbn.
  - reflexivity.
  - apply IHv.
Qed.

(** [renameEnv] commutes with composition (of renamings vs of functions). *)
Lemma renameEnv_cat {g g' g''} (s : Rnm g g') (s' : Rnm g' g'') (e : env g'')
  : renameEnv (s >>> s') e = renameEnv s (renameEnv s' e).
Proof.
  induction g; cbn.
  - reflexivity.
  - f_equal.
    + apply (IHg (fun _ v => s _ (There v))).
    + unfold cat_Rnm. symmetry; apply lookup_renameEnv.
Qed.

(** The above two lemmas make [(env, renameEnv)] a functor... *)

(** A specialized formulation of an extensionality principle environments ("two
    environments are equal if they produce the same results by indexing/lookup"). *)
Lemma renameEnv_ext {g g'} (s : Rnm g g') e e'
  : (forall a v, lookup (s a v) e = lookup v e') ->
    renameEnv s e = e'.
Proof.
  induction g; cbn; intros H.
  - destruct e'; reflexivity.
  - destruct e'; f_equal.
    + apply IHg. intros; apply H.
    + apply H.
Qed.

(** Renaming with the identity renaming is the identity function on environments. *)
Lemma renameEnv_id {g} (e : env g) : renameEnv id_Rnm e = e.
Proof.
  apply renameEnv_ext. reflexivity.
Qed.

(** The heap only ever grows by adding new bindings.
    Existing bindings persist. So if we restrict the new heap to the domain
    of the old heap, then it should coincide with the old heap.
    We eventually only care about the denotations of the heap,
    so that's what we compare here. (We could try to prove the actual
    equality on heaps, but it's just more work.)  *)
Theorem BigStep_heap_increasing' : forall g u (t : Tm g u) (e : Heap g) g' (s' : Rnm g g') (e' : Heap g') (v : Vl g' u) (n : nat),
  BigStep t e s' e' v n ->
  evalHeap e = renameEnv s' (evalHeap e').
Proof.
  intros * H; induction H; cbn [eval evalHeap renameEnv] in *; intros.
  all: try solve [symmetry; apply renameEnv_id].
  - apply (f_equal fst) in IHBigStep; cbn in IHBigStep.
    apply IHBigStep.
  - rewrite IHBigStep1.
    apply (f_equal fst) in IHBigStep2. cbn in IHBigStep2. rewrite IHBigStep2.
    symmetry; apply renameEnv_cat.
  - rewrite IHBigStep1.
    apply (f_equal fst) in IHBigStep2. cbn in IHBigStep2. rewrite IHBigStep2.
    symmetry; apply renameEnv_cat.
  - auto.
  - apply (f_equal fst) in IHBigStep; cbn in IHBigStep.
    destruct H0 as [ | ? ? ? ? ? [] ]; cbn in IHBigStep.
    + assumption.
    + rewrite H2.
      rewrite renameEnv_cat. f_equal. assumption.
Qed.

(** A variant of the previous lemma composed with applications of [lookup]. *)
Theorem BigStep_heap_increasing : forall g u (t : Tm g u) (e : Heap g) g' (s' : Rnm g g') (e' : Heap g') (v : Vl g' u) (n : nat),
  BigStep t e s' e' v n ->
  forall a (v : _ a), lookup (s' _ v) (evalHeap e') = lookup v (evalHeap e).
Proof.
  intros * W a v; apply BigStep_heap_increasing' in W.
  rewrite W; auto using lookup_renameEnv.
Qed.

(** Respectfulness of [foldrA']. Helper for [eq_M_foldrA]. *)
Lemma eq_M_foldrA' {a b} (fnil fnil' : M b) (fcons fcons' : T a -> T b -> M b)
    (xs : ListA a)
  : eq_M fnil fnil' ->
    (forall x y, eq_M (fcons x y) (fcons' x y)) ->
    eq_M (foldrA' fnil fcons xs) (foldrA' fnil' fcons' xs).
Proof.
  intros J1 J2; induction xs; cbn.
  - apply eq_M_bind; [ apply Reflexive_eq_M | intros _; auto ].
  - apply eq_M_bind; [ apply Reflexive_eq_M | intros _ ].
    apply eq_M_bind; [ | auto ].
    apply eq_M_thunk.
    destruct xs; cbn; [ | apply Reflexive_eq_M ].
    apply H.
Qed.

(** Respectfulness of [foldrA]. *)
Lemma eq_M_foldrA {a b} (fnil fnil' : M b) (fcons fcons' : T a -> T b -> M b)
    (xs : T (ListA a))
  : eq_M fnil fnil' ->
    (forall x y, eq_M (fcons x y) (fcons' x y)) ->
    eq_M (foldrA fnil fcons xs) (foldrA fnil' fcons' xs).
Proof.
  intros J1 J2; destruct xs; cbn; [ apply eq_M_foldrA'; auto | apply Reflexive_eq_M ].
Qed.

(** Renaming lemma: denotations ([eval]) are invariant under renamings.
    Environments must be renamed too, [e = renameEnv s e'],
    but we use a more readily available phrasing of that equality. *)
Lemma evalRnm {g g'} u (t : Tm g u) (s : Rnm g g') (e : env g) (e' : env g')
  : (forall a v, lookup (s a v) e' = lookup v e) ->
    eq_M (eval t e) (eval (rename s t) e').
Proof.
  revert g' s e'; induction t; intros g' s e' Hs; cbn.
  all: try (apply eq_M_bind; [ apply Reflexive_eq_M | intros _ ]).
  - apply eq_M_bind; intros.
    { apply eq_M_thunk. apply IHt1. auto. }
    { apply IHt2 with (s := (shift s)); cbn.
      apply V_split; eauto. }
  - apply eq_M_bind; intros.
    { apply IHt. auto. }
    rewrite Hs. apply Reflexive_eq_M.
  - rewrite Hs. apply Reflexive_eq_M.
  - apply eq_M_ret.
    apply functional_extensionality; intros ?.
    apply eq_M_eq.
    apply IHt. apply V_split; eauto.
  - apply eq_M_ret. congruence.
  - apply eq_M_bind.
    + rewrite Hs. apply Reflexive_eq_M.
    + intros. apply Reflexive_eq_M.
  - apply eq_M_bind.
    + rewrite Hs. apply Reflexive_eq_M.
    + intros. apply Reflexive_eq_M.
  - apply Reflexive_eq_M.
  - rewrite 2 Hs; apply Reflexive_eq_M.
  - rewrite Hs. apply eq_M_foldrA; auto.
    intros; eapply IHt2.
    apply V_split; auto.
    apply V_split; auto.
  - apply Reflexive_eq_M.
Qed.

(** Equal computations satisfy the same specifications. *)
Lemma eq_M_optim {a} (u1 u2 : M a) r
  : eq_M u1 u2 -> u1 [[ r ]] -> u2 [[ r ]].
Proof.
  unfold optimistic, eq_M. firstorder eauto.
Qed.

(** Renaming lemma for syntactic values: their denotations are invariant under
    renaming. *)
Lemma evalVl_renameVl g a (e : Heap g) (v : Vl g a) g' (s : Rnm g g') (e' : Heap g')
  : (forall a v, lookup (s a v) (evalHeap e') = lookup v (evalHeap e)) ->
    evalVl (evalHeap e) v = evalVl (evalHeap e') (renameVl s v).
Proof.
  destruct v; cbn; intros; auto.
  - apply functional_extensionality; intros.
    apply eq_M_eq.
    apply evalRnm.
    apply V_split; cbn; [ | reflexivity ].
    auto.
  - f_equal; auto.
  - f_equal; auto.
Qed.

(** Helper for [lookup_evalHeap]. *)
Lemma lookup_evalHeap_ g a (e : Heap g) (v : V g a) g' (s : Rnm g g') (e' : Heap g')
  : (forall a v, lookup (s a v) (evalHeap e') = lookup v (evalHeap e)) ->
    lookup (s _ v) (evalHeap e') = mapT (evalVl (evalHeap e')) (lookup_' v s e).
Proof.
  intros H; rewrite H.
  revert e g' s e' H; induction v; cbn; intros.
  - rewrite eta_Heap in *; cbn. destruct (here e); cbn; f_equal.
    apply evalVl_renameVl.
    intros ? ?. apply H.
  - rewrite eta_Heap; cbn. apply IHv.
    intros ? vv. specialize (H _ (There vv)). cbn in H. rewrite eta_Heap in H; apply H.
Qed.

(** Evaluating the heap, then indexing it, is equivalent to
    indexing it then evaluating the result. *)
Lemma lookup_evalHeap g a (e : Heap g) (v : V g a)
  : lookup v (evalHeap e) = mapT (evalVl (evalHeap e)) (lookup' v e).
Proof.
  apply lookup_evalHeap_ with (s := id_Rnm).
  reflexivity.
Qed.

(** * Theorem 4.1

    The backward direction: (2) -> (1). *)

(** If [t] evaluates to value-cost pair [(v, n)] in the [BigStep] simantics
(Hacket & Hutton's Clairvoyant CBV), then [t] evaluates to [(evalVl _ v, n)]
in the [eval] semantics.
(Recall [m [[ r ]]] means "there exists a pair [(x0, n0)] in [m] satisfying the postcondition [r]") *)
Theorem soundness : forall g u (t : Tm g u) (e : Heap g) g' (s' : Rnm g g') (e' : Heap g') (v : Vl g' u) (n : nat),
  BigStep t e s' e' v n ->
  (eval t (evalHeap e)) [[ fun x0 n0 => evalVl (evalHeap e') v = x0 /\ n = n0 ]].
Proof.
  intros * H; induction H; cbn [eval evalHeap] in *; intros; lucky_forward.
  - apply optimistic_skip.
    lucky_forward. firstorder.
  - apply optimistic_thunk_go. lucky_forward.
    eapply eq_M_optim; [ | relax; [ eapply IHBigStep2 | ] ].
    + apply Symmetric_eq_M, evalRnm.
      apply V_split; cbn.
      { revert H. apply BigStep_heap_increasing. }
      { reflexivity. }
    + firstorder.
  - cbn [evalVl].
    rewrite <- (BigStep_heap_increasing H).
    rewrite lookup_evalHeap. cbn.
    lucky_forward. firstorder.
  - rewrite lookup_evalHeap, <- H; cbn.
    mforward idtac; firstorder.
  - firstorder.
  - cbn. firstorder.
  - rewrite lookup_evalHeap, <- H.
    cbn; lucky_forward.
    rewrite 2 lookup_evalHeap, <- H0; cbn.
    cbn; lucky_forward. firstorder.
  - rewrite lookup_evalHeap, <- H.
    cbn. lucky_forward.
    rewrite 2 lookup_evalHeap, <- H0; cbn.
    cbn; lucky_forward. firstorder.
  - firstorder.
  - firstorder.
  - rewrite lookup_evalHeap, <- H; cbn. lucky_forward. firstorder.
  - rewrite lookup_evalHeap, <- H; cbn. lucky_forward.
    destruct H0 as [ | ? ? ? ? ? [] ].
    + apply optimistic_skip.
      eapply eq_M_optim; [ | relax; [ eapply IHBigStep | ] ].
      * eapply Symmetric_eq_M, evalRnm.
        apply V_split; cbn; auto.
        apply V_split; cbn; auto.
      * cbn. intros ? ? []; auto.
    + apply optimistic_thunk_go.
      relax. apply H2.
      intros ? ? [].
      eapply eq_M_optim; [ | relax; [ eapply IHBigStep | ] ].
      * eapply Symmetric_eq_M, evalRnm.
        apply V_split; cbn; [ | f_equal; auto ].
        apply V_split; cbn; auto.
        all: apply (BigStep_heap_increasing H0).
      * cbn. intros ? ? []; auto.
  - firstorder.
Qed.

(** Next, we will prove adequacy *)

(** More preliminaries, facts about renamings. *)

(* Decompose existentials and conjunctions. *)
Ltac decomp H :=
  lazymatch type of H with
  | (exists x_, _) => let x := fresh x_ in destruct H as [x H]; decomp H
  | (_ /\ _) =>
    let H1 := fresh H in
    destruct H as [H1 H]; decomp H
  | _ => idtac
  end.

(* Prove the premise of an implication. *)
Ltac prove_assum H :=
  lazymatch type of H with
  | (?T -> _) =>
    let w := fresh in
    assert (w : T); [ | specialize (H w); clear w ]
  end.

(** Extensional equality of renamings. *)
Definition eq_Rnm g g' (s1 s2 : Rnm g g') : Prop :=
  forall a v, s1 a v = s2 a v.

Declare Scope rnm_scope.
Delimit Scope rnm_scope with rnm.
Infix "=" := eq_Rnm : rnm_scope.

(** Transitivity of [eq_Rnm]. *)
Lemma Transitive_eq_Rnm g g' (s1 s2 s3 : Rnm g g')
  : (s1 = s2)%rnm -> (s2 = s3)%rnm -> (s1 = s3)%rnm.
Proof. unfold eq_Rnm; etransitivity; eauto. Qed.

(** [eq_Rnm] is an equivalence relation. *)
Instance Equivalence_eq_Rnm g g' : Equivalence (@eq_Rnm g g').
Proof.
  constructor; red; unfold eq_Rnm; [reflexivity | symmetry | etransitivity]; eauto.
Qed.

(** [shift] commutes with [>>>] (composition of renamings) and [id_Rnm].
    (i.e., [shift] is a functor.) *)
Lemma shift_cat_Rnm g1 g2 g3 (s1 : Rnm g1 g2) (s2 : Rnm g2 g3) (a : Ty)
  : (shift (a := a) (s1 >>> s2) = shift s1 >>> shift s2)%rnm.
Proof.
  red; apply V_split; cbn; auto.
Qed.

Lemma shift_id g a : (shift (a := a) (id_Rnm (g := g)) = id_Rnm)%rnm.
Proof.
  red; apply V_split; cbn; auto.
Qed.

Arguments shift_id : clear implicits.

Lemma Proper_shift g g' (s1 s2 : Rnm g g') (a : Ty)
  : (s1 = s2)%rnm -> (shift (a := a) s1 = shift s2)%rnm.
Proof.
  intros; red; apply V_split; cbn; auto.
  intros; f_equal; apply H.
Qed.

Lemma Proper_rename g g' (s1 s2 : Rnm g g') a (t : Tm g a)
  : (s1 = s2)%rnm -> rename s1 t = rename s2 t.
Proof.
  revert g' s1 s2; induction t; intros * Es; cbn; f_equal; eauto using Proper_shift.
Qed.

(** [rename] commutes with composition (of renamings vs of functions) *)
Lemma rename_cat_Rnm g1 g2 g3 (s1 : Rnm g1 g2) (s2 : Rnm g2 g3) (a : Ty) (t : Tm g1 a)
  : rename (s1 >>> s2) t = rename s2 (rename s1 t).
Proof.
  revert g2 g3 s1 s2; induction t; cbn; intros; f_equal; auto.
  all: etransitivity; [ apply Proper_rename; try apply shift_cat_Rnm | ]; auto.
  eapply Transitive_eq_Rnm; [ apply Proper_shift | ]; apply shift_cat_Rnm.
Qed.

(** Renaming with the identity renaming is the identity function on terms. *)
Lemma rename_id g a (t : Tm g a) : rename id_Rnm t = t.
Proof.
  induction t; cbn; intros; f_equal; auto.
  all: etransitivity; [ apply Proper_rename; try apply shift_id | ]; eauto.
  etransitivity; [ apply Proper_shift |]; apply shift_id.
Qed.

(** [restr] is kinda the oopposite of [shift]. *)
Lemma renameEnv_restr_shift g g' (s : Rnm g g') e a (v : T (toType a))
  : renameEnv (restr (shift s)) (e, v) = renameEnv s e.
Proof.
  apply renameEnv_ext; intros; rewrite lookup_renameEnv; reflexivity.
Qed.

Definition eq_T' {a b : Type} (r : a -> b -> Prop) (x : T a) (y : T b) : Prop :=
  match x, y with
  | Undefined, Undefined => True
  | Thunk x, Thunk y => r x y
  | _, _ => False
  end.

Lemma eq_T_mon a b (r r' : a -> b -> Prop)
  : (forall x y, r x y -> r' x y) -> forall x y, eq_T' r x y -> eq_T' r' x y.
Proof.
  intros H [] []; cbn; auto.
Qed.

(** Inversion principle for [Vl] (a more predictable technique than using [inversion]). *)
Lemma inv_Vl g u (v : Vl g u)
  : match u return Vl g u -> Prop with
    | Arr u1 u2 => fun v => exists t, v = VLam t
    | Prod u1 u2 => fun v => exists x1 x2, v = VPair x1 x2
    | List u => fun v => v = VNil \/ exists x1 x2, v = VCons x1 x2
    | Base _ => fun _ => True
    end v.
Proof.
  destruct v; cbn; eauto.
Qed.

(** * Theorem 4.1

    The forward direction: (1) -> (2). *)

(** Proof by induction on cost, which is luckily available already (otherwise we'd have
to redefine the interpreter with fuel). *)
Theorem adequacy_ : forall n g u (t : Tm g u) (f : env g),
    (eval t f) {{ fun (x0 : toType u) n0 =>
      n = n0 ->
      forall g0 (s0 : Rnm g g0) (e0 : Heap g0),
        f = renameEnv s0 (evalHeap e0) ->
        exists g' (s' : Rnm g0 g') (e' : Heap g') (v' : Vl g' u),
          evalVl (evalHeap e') v' = x0 /\
          BigStep (rename s0 t) e0 s' e' v' n0 }}.
Proof.
  induction n as [n IH] using lt_wf_ind; intros *; destruct t; cbn; lucky_forward.
  - intros y1 n1 Hy1 y2 n2 Hy2 -> * Hf.
    assert (IH1 := IH n1 ltac:(lia) _ _ _ _ _ _ Hy1 eq_refl _ s0 e0 Hf).
    decomp IH1.
    assert (IH2 := IH n2 ltac:(lia) _ _ _ _ _ _ Hy2 eq_refl _ (shift (cat_Rnm s0 s')) (HCons e' (Thunk v'))).
    prove_assum IH2.
    { cbn; f_equal; [ | f_equal; auto].
      rewrite Hf.
      apply renameEnv_ext; intros; rewrite lookup_renameEnv.
      apply symmetry, (BigStep_heap_increasing IH1). }
    decomp IH2.
    eexists _, _, _, _. split; [ eassumption | ].
    econstructor 2; [ eassumption | ].
    let H00 := IH2 in lazymatch type of H00 with
    | BigStep ?t _ _ _ _ _ =>
      let w := fresh in
      evar (w : ltac:(let t := type of t in exact t)); replace t with w in H00; cycle 1; subst w;
        [ symmetry | ]
    end.
    { etransitivity; [ apply Proper_rename, shift_cat_Rnm | apply rename_cat_Rnm]. }
    eassumption.
  - intros y2 n2 Hy2 -> * Hf.
    specialize (IH n2 ltac:(simpl; lia)  _ _ _ _ _ _ Hy2 eq_refl _ (shift s0) (e0 :*: Undefined)).
    prove_assum IH; [ cbn; f_equal; subst f; solve [auto using renameEnv_restr_shift] | ].
    decomp IH.
    eexists _, _, _, _. split; [ eassumption | ].
    constructor; eassumption.
  - intros y1 n1 Hy1 y2 n2 Hy2 -> * Hf.
    assert (IH1 := IH n1 ltac:(lia) _ _ _ _ _ _ Hy1 eq_refl _ s0 e0 Hf).
    decomp IH1.
    assert (Hv := inv_Vl v'); cbn in Hv; destruct Hv as [t' ->].
    rewrite <- IH0 in Hy2; cbn in Hy2.
    assert (IH2 := IH n2 ltac:(lia) _ _ _ _ _ _ Hy2 eq_refl _ id_Rnm (e' :*: lookup' (s' _ (s0 _ v)) e') ).
    prove_assum IH2.
    { rewrite renameEnv_id. cbn. f_equal.
      rewrite Hf. rewrite lookup_renameEnv, <- lookup_evalHeap.
      rewrite (BigStep_heap_increasing IH1).
      reflexivity. }
    decomp IH2.
    rewrite rename_id in IH2.
    eexists _, _, _, _. split; [ eassumption | ].
    econstructor; try eassumption.
  - intros ? H -> * Hf.
    rewrite Hf in H.
    rewrite lookup_renameEnv, lookup_evalHeap in H.
    destruct (lookup' _ _) eqn:Elookup in H; cbn in H; [ | discriminate ].
    injection H; intros J.
    eexists _, _, _, _. split; [ eassumption | ].
    constructor; auto.
  - intros -> * Hf.
    eexists _, id_Rnm, _, (VLam (rename (shift s0) t)).
    split.
    { cbn. apply functional_extensionality; intros.
      symmetry; apply eq_M_eq.
      apply evalRnm.
      apply V_split; cbn; intros; [ | reflexivity ].
      { rewrite Hf, lookup_renameEnv; reflexivity. } }
    constructor.
  - intros -> * Hf.
    eexists _, _, _, (VPair (s0 _ v) (s0 _ v0)).
    split.
    { cbn. rewrite Hf, 2 lookup_renameEnv; reflexivity. }
    constructor.
  - intros ? Hv. mforward idtac. intros ? Hfst.
    intros -> * Hf.
    rewrite Hf, lookup_renameEnv, lookup_evalHeap in Hv.
    destruct (lookup' _ _) eqn:Hlookup in Hv; cbn in Hv; [ | discriminate ].
    injection Hv; clear Hv; intros Hv.
    assert (Hv' := inv_Vl x1); cbn in Hv'; destruct Hv' as (X1 & X2 & ->).
    cbn in Hv; rewrite <- Hv in Hfst; cbn in Hfst.
    rewrite lookup_evalHeap in Hfst.
    destruct (lookup' _ _) eqn:Hlookup2 in Hfst; cbn in Hfst; [ | discriminate ].
    injection Hfst; clear Hfst; intros Hfst.
    eexists _, _, _, x1.
    split; [ eassumption | ].
    econstructor; try eauto.
  - intros ? Hv. mforward idtac. intros ? Hfst.
    intros -> * Hf.
    rewrite Hf, lookup_renameEnv, lookup_evalHeap in Hv.
    destruct (lookup' _ _) eqn:Hlookup in Hv; cbn in Hv; [ | discriminate ].
    injection Hv; clear Hv; intros Hv.
    assert (Hv' := inv_Vl x1); cbn in Hv'; destruct Hv' as (X1 & X2 & ->).
    cbn in Hv; rewrite <- Hv in Hfst; cbn in Hfst.
    rewrite lookup_evalHeap in Hfst.
    destruct (lookup' _ _) eqn:Hlookup2 in Hfst; cbn in Hfst; [ | discriminate ].
    injection Hfst; clear Hfst; intros Hfst.
    eexists _, _, _, x1.
    split; [ eassumption | ].
    econstructor; try eauto.
  - intros -> * Hf.
    eexists _, _, _, VNil.
    split; [ reflexivity | ].
    constructor.
  - intros -> * Hf.
    eexists _, _, _, (VCons (s0 _ v) (s0 _ v0)).
    split.
    { cbn. rewrite Hf, 2 lookup_renameEnv; reflexivity. }
    constructor.
  - destruct (lookup v f) eqn:Hvf; cbn; [ | mforward idtac].
    intros y1 n1 Hy1 En * Hf.
    rewrite Hf in Hvf.
    rewrite lookup_renameEnv, lookup_evalHeap in Hvf.
    destruct (lookup' _ _) eqn:Hvf' in Hvf; cbn in Hvf; [ | discriminate ].
    injection Hvf; clear Hvf; intros Hvf.
    assert (Hv := inv_Vl x0); cbn in Hv;
      destruct Hv as [-> | (? & ? & ->)]; cbn in Hvf; rewrite <- Hvf in Hy1; cbn in Hy1.
    all: revert y1 n1 Hy1 En.
    all: lazymatch goal with
      | [ |- forall (_ : ?u) (_ : nat), ?t _ _ -> _ ] =>
        let r := fresh "r" in
        evar (r : u -> nat -> Prop);
        enough (t {{ r }}); subst r; [ exact H | ]
      end.
    all: lucky_forward.
    + intros y1 n1 Hy1 ->.
      assert (IH1 := IH n1 ltac:(lia) _ _ _ _ _ _ Hy1 eq_refl _ _ _ Hf).
      decomp IH1.
      eexists _, _, _, _.
      split; [ eassumption |].
      constructor; eauto.
    + intros. intros y1 n1 Hy1. intros y2 n2 Hy2 ->.
      assert (IH1 := IH n1 ltac:(lia) _ _ (Foldr (rename s0 t1) (rename (shift (shift s0)) t2) x2) (evalHeap e0) y1 n1).
      prove_assum IH1.
      { cbn; unfold foldrA. rewrite H. cbn. revert Hy1. subst.
        apply eq_M_foldrA'.
        + apply Symmetric_eq_M. apply evalRnm. intros. rewrite lookup_renameEnv.
          reflexivity.
        + intros. apply Symmetric_eq_M, evalRnm.
          apply V_split; [ apply V_split | ]; intros; cbn; try reflexivity.
          rewrite lookup_renameEnv. reflexivity. }
      specialize (IH1 eq_refl _ id_Rnm e0).
      prove_assum IH1; [ rewrite renameEnv_id; reflexivity | ].
      decomp IH1; rewrite rename_id in IH1.
      specialize (IH n2 ltac:(lia) _ _ t2 _ _ _ Hy2 eq_refl _ (shift (shift s0) >>> shiftAlgCons x1 s')).
      specialize (IH (e' :*: Thunk v')).
      prove_assum IH.
      { symmetry; apply renameEnv_ext. apply V_split; [ apply V_split |]; cbn.
        - intros; rewrite Hf, lookup_renameEnv; auto.
          rewrite (BigStep_heap_increasing IH1). reflexivity.
        - rewrite (BigStep_heap_increasing IH1). reflexivity.
        - f_equal; auto. }
      decomp IH.
      eexists _, _, _, _.  split; [ eauto | ].
      eapply BigStep_Foldr_Node; eauto.
      { constructor. eassumption. }
      { rewrite rename_cat_Rnm in IH. eassumption. }
    + intros y1 n1 Hy1 ->.
      assert (IH1 := IH n1 ltac:(simpl; lia) _ _ _ _ _ _ Hy1 eq_refl).
      specialize (IH1 _ (shift (shift s0) >>> shiftAlgCons x1 id_Rnm) (e0 :*: Undefined)).
      prove_assum IH1.
      { symmetry; apply renameEnv_ext; apply V_split; [ apply V_split | ]; intros; cbn.
        - rewrite Hf, lookup_renameEnv. reflexivity.
        - reflexivity.
        - reflexivity. }
      decomp IH1.
      eexists _, _, _, _.
      split; [ eassumption |].
      eapply BigStep_Foldr_Node; eauto.
      { constructor. }
      { rewrite rename_cat_Rnm in IH1. eassumption. }
  - intros -> * Hf.
    eexists _, _, _, (VBas _). split; [ reflexivity |].
    constructor.
Qed.

(** Converse of [soundness]: every pair [(x', n')] in the [eval] semantics
of [t] corresponds to a pair [(v', n')] in the [BigStep] semantics,
where [v'] is a (syntactic) value which evaluates to [x'].
(Recall [pessim m r] means "all pairs in [m] satisfy the postcondition [r]".) *)
Theorem adequacy g u (t : Tm g u) (e : Heap g)
  : (eval t (evalHeap e))
      {{ fun (x' : toType u) n' => exists g' (s' : Rnm g g') (e' : Heap g') (v' : Vl g' u),
             evalVl (evalHeap e') v' = x' /\
             BigStep t e s' e' v' n' }}.
Proof.
  intros y0 n0 Hy0.
  assert (AQ := adequacy_ t Hy0 eq_refl id_Rnm ltac:(rewrite renameEnv_id; reflexivity)).
  rewrite rename_id in AQ. assumption.
Qed.

Definition elem {a} (z : M a) (x : a) (n : nat) : Prop := z x n.

(** This theorem combines soundness and adequacy to make the equivalence more
explicit using [<->]. *)
Theorem soundess_and_adequacy g u (t : Tm g u) (e : Heap g) (x : toType u) (n : nat)
  : elem (eval t (evalHeap e)) x n
  <-> exists g' (s' : Rnm g g') (e' : Heap g') (v' : Vl g' u),
        evalVl (evalHeap e') v' = x /\
        BigStep t e s' e' v' n.
Proof.
  split; [ apply adequacy | ].
  intros H; decomp H; apply soundness in H. red in H; decomp H.
  red. subst; auto.
Qed.

End Lambda.
