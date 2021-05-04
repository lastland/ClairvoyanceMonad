(** A formalization of "Call-by-need is Clairvoyant Call-by-value".

Semantics:
- [BigStep]: Hackett & Hutton's Clairvoyant CBV (operational semantics)
- [eval]: our monadic semantics

Equivalence:
- [soundness]: [BigStep] semantics are a subset of [eval] semantics.
- [adequacy]: [eval] semantics are a subset of [BigStep] semantics.

Putting those together, the equivalence is made explicit in
[soundness_and_adequacy].
 *)

(** Many of the definitions here duplicate with those in
    [Clairvoyance.v]. To skip to the part related to Section 4 of the
    paper, skip to the [Lambda] module. *)

(* AXIOMS: We use functional and propositional extensionality.
We can probably avoid them with more setoid-based reasoning. *)

From Coq Require Import FunctionalExtensionality.

(* Propositional extensionality *)
Axiom prop_ext : forall P Q, (P <-> Q) -> P = Q.

(**)

From Coq Require Import
     Arith Psatz Omega Setoid Morphisms.

Require Import Clairvoyance.

Set Implicit Arguments.
Set Contextual Implicit.

Declare Scope ctx_scope.

Definition mapT {a b} (f : a -> b) (t : T a) : T b :=
  match t with
  | Undefined => Undefined
  | Thunk x => Thunk (f x)
  end.

Definition T_prop {a} (f : a -> Prop) : T a -> Prop :=
  fun t => match t with
           | Undefined => True
           | Thunk x => f x
        end.

Definition le_M {a} (t t' : M a) : Prop :=
  forall x n, t' x n -> exists n', t x n' /\ n' <= n.

Definition eq_M {a} (u v : M a) : Prop := forall x n, u x n <-> v x n.

Declare Scope M_scope.
Delimit Scope M_scope with M.

Infix "<=" := le_M : M_scope.
Infix "=" := eq_M : M_scope.

Lemma eq_M_bind {a b} (u1 u2 : M a) (k1 k2 : a -> M b)
  : eq_M u1 u2 ->
    (forall x, eq_M (k1 x) (k2 x)) ->
    eq_M (bind u1 k1) (bind u2 k2).
Proof.
  unfold eq_M. firstorder.
  repeat eexists; eauto. apply H; eauto. apply H0; eauto.
  repeat eexists; eauto. apply H; eauto. apply H0; eauto.
Qed.

Lemma eq_M_forcing {a b} (x1 x2 : T a) (k1 k2 : a -> M b)
  : x1 = x2 ->
    (forall x, eq_M (k1 x) (k2 x)) ->
    eq_M (forcing x1 k1) (forcing x2 k2).
Proof.
  intros <- H; destruct x1; cbn; auto.
  firstorder.
Qed.

Lemma eq_M_thunk {a} (u1 u2 : M a) : eq_M u1 u2 -> eq_M (thunk u1) (thunk u2).
Proof.
  intros H [] ?; cbn; auto. reflexivity.
Qed.

Lemma eq_M_ret {a} (x1 x2 : a) : x1 = x2 -> eq_M (ret x1) (ret x2).
Proof.
  unfold eq_M. firstorder congruence.
Qed.

Lemma Reflexive_eq_M {a} (u : M a) : eq_M u u.
Proof. firstorder. Qed.

Lemma Symmetric_eq_M {a} (u v : M a) : eq_M u v -> eq_M v u.
Proof. firstorder. Qed.

Lemma Reflexive_le_M {a} (u : M a) : (u <= u)%M.
Proof.
  red; firstorder.
Qed.

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

Lemma bind_tick {a b} (u : M a) (k : a -> M b)
  : (bind u (fun x => bind tick (fun _ => k x)) = bind tick (fun _ => bind u k))%M.
Proof.
  unfold bind, tick, eq_M. firstorder.
  - eexists tt, 1, _. split; auto.
    split; [ eexists _, _, _; split; eauto |]. lia.
  - eexists _, _, _; split; [ eauto | ].
    split; [ eexists tt, _, _; split; eauto |]. lia.
Qed.

Lemma thunk_tick {a} (u : M a)
  : (thunk (bind tick (fun _ => u)) <= bind tick (fun _ => thunk u))%M.
Proof.
  unfold thunk, bind, tick, le_M; firstorder.
  destruct x.
  - eexists; split; [ | constructor ]. exists tt. eauto.
  - exists 0; split; auto. lia.
Qed.


Module Lambda.

(** Syntax *)

Inductive Ty : Type :=
| Arr  : Ty -> Ty -> Ty  (* Functions *)
| Prod : Ty -> Ty -> Ty  (* Products *)
| List : Ty -> Ty  (* A basic recursive data type: List a = Unit + a * List a *)
| Base : Type -> Ty  (* Base types are arbitrary types of the host language (Coq) *)
.

Inductive Ctx : Type :=
| NilCtx
| ConsCtx : Ctx -> Ty -> Ctx
.

Infix ":,:" := ConsCtx (at level 50).

Inductive V : Ctx -> Ty -> Type :=
| Here g x : V (g :,: x) x
| There g x y : V g y -> V (g :,: x) y
.

(* A lambda calculus with primitive fold. *)

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

(** Denotational semantics (our contribution) *)

Unset Elimination Schemes.
Inductive ListA (a : Type) : Type :=
| NilA : ListA a
| ConsA : T a -> T (ListA a) -> ListA a
.

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

Fixpoint toType (u : Ty) : Type :=
  match u with
  | Arr u1 u2 => T (toType u1) -> M (toType u2)
  | Prod u1 u2 => (T (toType u1) * T (toType u2))%type
  | List a => ListA (toType a)
  | Base b => b
  end.

Fixpoint env (g : Ctx) : Type :=
  match g with
  | NilCtx => unit
  | ConsCtx g1 u => env g1 * T (toType u)
  end.

Fixpoint lookup {g u} (v : V g u) : env g -> T (toType u) :=
  match v with
  | Here => fun ex => snd ex
  | There v1 => fun ex => lookup v1 (fst ex)
  end.

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

(** Example: append *)

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

Theorem appendA_le_append {a} (xs ys : T (ListA (toType a)))
  : (appendA xs ys <= eval append (tt, xs, ys))%M.
Proof.
  apply forcing_le; destruct xs; cbn; [ | auto ].
  eapply appendA_le_append_.
Qed.

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

Theorem append_le_appendA {a} (xs ys : T (ListA (toType a)))
  : (eval append (tt, xs, ys) <= costMul 2 (appendA xs ys))%M.
Proof.
  apply le_costMul.
  unfold appendA; cbn; unfold foldrA.
  destruct xs.
  - cbn. apply append_le_appendA_.
  - intros ? ? [].
Qed.

(** Operational semantics (from the paper, Figure 3) *)

Unset Elimination Schemes.

(* Syntactic values are closures and base values. *)
Inductive Vl (g : Ctx) : Ty -> Type :=
| VLam a b : Tm (g :,: a) b -> Vl g (Arr a b)
| VPair a b : V g a -> V g b -> Vl g (Prod a b)
| VNil a : Vl g (List a)
| VCons a : V g a -> V g (List a) -> Vl g (List a)
| VBas b : b -> Vl g (Base b)
.

(*
Definition Vl_ind {g} (P : forall a, Vl g a -> Prop)
  : (forall a b t1, P (Arr a b) (VLam t1)) ->
    (forall a b t1 t2, T_prop (P a) t1 -> T_prop (P b) t2 -> P (Prod a b) (VPair t1 t2)) ->
    P Tree VLeaf ->
    (forall t1 t2, T_prop (P Tree) t1 -> T_prop (P Tree) t2 -> P Tree (VNode t1 t2)) ->
    (forall b x, P (Base b) (VBas x)) ->
    (forall a v, P a v).
Proof.
  intros A B Lf Nd C. fix SELF 2; intros ? [].
  - apply A.
  - apply B; lazymatch goal with [ |- _ _ ?t ] => destruct t end; cbn; constructor + auto.
  - apply Lf.
  - apply Nd; lazymatch goal with [ |- _ _ ?t ] => destruct t end; cbn; constructor + auto.
  - apply C.
Qed.
*)

Set Elimination Schemes.

Inductive Env : Ctx -> Type :=
| ENil : Env NilCtx
| ECons g a : Env g -> T (Vl g a) -> Env (g :,: a)
.

Infix ":*:" := ECons (at level 40).

(** General operations on syntax *)

Fixpoint app_Ctx (g g' : Ctx) : Ctx :=
  match g' with
  | NilCtx => g
  | ConsCtx g' u => ConsCtx (app_Ctx g g') u
  end.

Infix "++" := app_Ctx : ctx_scope.

Bind Scope ctx_scope with Ctx.

Definition here {g u} (e : Env (g :,: u)) : T (Vl g u) :=
  match e in Env g0 return
    match g0 with
    | NilCtx => True
    | (_ :,: u) => T (Vl _ u)
    end with
  | ENil => I
  | ECons _ h => h
  end.

Definition there {g u} (e : Env (g :,: u)) : Env g :=
  match e in Env g0 return
    match g0 with
    | NilCtx => True
    | (g :,: _) => Env g
    end with
  | ENil => I
  | ECons t _ => t
  end.

(** Renaming from context [g] to context [g'] *)
Definition Rnm (g g' : Ctx) := forall a, V g a -> V g' a.

Definition elimV {g a b} (v : V (g :,: a) b) {r : Ty -> Type} : (V g b -> r b) -> r a -> r b :=
  match v in V g_ b_ return
    match g_ with
    | (g :,: a) => _
    | _ => False
    end with
  | Here => fun _ y => y
  | There v => fun x _ => x v
  end.

Definition shift {g g' : Ctx} (s : Rnm g g') {a} : Rnm (g :,: a) (g' :,: a) :=
  fun _ v => elimV v (fun v => There (s _ v)) Here.

(** Given [fcons] in context [g1 :,: a :,: b], we rename it by
  1. looking up [a] in the context [g1];
  2. applying some substitution on [g2]. *)
Definition shiftAlgCons {g1 g2 a b} (v1 : V g1 a) (s : Rnm g1 g2)
  : Rnm (g1 :,: a :,: b) (g2 :,: b) :=
  shift (fun _ v => s _ (elimV v (fun v => v) v1)).

Definition restr {g g' : Ctx} {a} (s : Rnm (g :,: a) g') : Rnm g g' :=
  fun _ v => s _ (There v).

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

Definition renameVl {g g'} (s : Rnm g g') {a} (t : Vl g a) : Vl g' a :=
  match t with
  | VLam t1 => VLam (rename (shift s) t1)
  | VPair v1 v2 => VPair (s _ v1) (s _ v2)
  | VNil => VNil
  | VCons v1 v2 => VCons (s _ v1) (s _ v2)
  | VBas b => VBas b
  end.

Fixpoint lookup_' {g g' u} (v : V g u) : Rnm g g' -> Env g -> T (Vl g' u) :=
  match v with
  | Here => fun s e => mapT (renameVl (restr s)) (here e)
  | There v1 => fun s gx => lookup_' v1 (restr s) (there gx)
  end.

Definition id_Rnm {g} : Rnm g g :=
  fun _ v => v.

Definition cat_Rnm {g g' g''} : Rnm g g' -> Rnm g' g'' -> Rnm g g'' :=
  fun s1 s2 _ v => s2 _ (s1 _ v).

Infix ">>>" := cat_Rnm (at level 40).

Definition lookup' {g u} (v : V g u) : Env g -> T (Vl g u) :=
  lookup_' v id_Rnm.

Inductive LazyStep g u (e : Env g) (BigStep_ : forall g', Rnm g g' -> Env g' -> Vl g' u -> nat -> Prop)
  : forall g', Rnm g g' -> Env g' -> T (Vl g' u) -> nat -> Prop :=
| LazyStep_SKIP : LazyStep e BigStep_ id_Rnm e Undefined 0
| LazyStep_STEP g' (s' : Rnm g g') e' r n
  : BigStep_ g' s' e' r n ->
    LazyStep e BigStep_ s' e' (Thunk r) n
.

Definition vthere {g a} : Rnm g (g :,: a) := fun _ v => There v.

(* Must be Defined for the BigStep fixpoint... *)
Lemma LazyStep_mon g u (e : Env g)
    (BigStep_ BigStep_' : forall g', Rnm g g' -> Env g' -> Vl g' u -> nat -> Prop)
  : (forall g' (s' : Rnm g g') (e' : Env g') (v : Vl g' u) (n : nat),
       BigStep_ g' s' e' v n -> BigStep_' g' s' e' v n) ->
    forall g' (s' : Rnm g g') (e' : Env g') (v : T (Vl g' u)) (n : nat),
      LazyStep e BigStep_ s' e' v n -> LazyStep e BigStep_' s' e' v n.
Proof.
  intros H * []; constructor; [ apply H; assumption ].
Defined.

Unset Elimination Schemes.

Definition andBS {g u}
    (BigStep_ BigStep_' : forall g', Rnm g g' -> Env g' -> Vl g' u -> nat -> Prop) :=
  fun g' s' e' v n => BigStep_ g' s' e' v n /\ BigStep_' g' s' e' v n.

(** [BigStep t1 e1 s2 e2 v2 n2]:
The term [t1] in heap [e1] evaluates to value [v2] in heap [e2] in time [n2],
and [s2] is a mapping from locations in [e1] to locations in [e2].

The extra complexity is mainly due to our intrinsically typed syntax,
which we have to rename to evaluate under a modified heap/env.
 *)
Inductive BigStep : forall g u, Tm g u -> Env g -> forall g', Rnm g g' -> Env g' -> Vl g' u -> nat -> Prop :=
| BigStep_Let_SKIP g a b (t1 : Tm g a) (t2 : Tm (g :,: a) b) (e : Env g) g' (s' : Rnm _ g') e' r n
  : BigStep t2 (e :*: Undefined) (g' := g') s' e' r n ->
    BigStep (Let t1 t2) e (restr s') e' r (S n)
| BigStep_Let_STEP g a b (t1 : Tm g a) (t2 : Tm (g :,: a) b) (e : Env g)
    g1 (s1 : Rnm _ g1) e1 r1 n1
    g2 (s2 : Rnm _ g2) e2 r2 n2
  : BigStep t1 e s1 e1 r1 n1 ->
    BigStep (rename (shift s1) t2) (e1 :*: Thunk r1) s2 e2 r2 n2 ->
    BigStep (Let t1 t2) e (s1 >>> restr s2) e2 r2 (S (n1 + n2))
| BigStep_App g a b (t : Tm g (Arr a b)) (v : V g a) e
    g1 (s1 : Rnm _ g1) (e1 : Env g1) r1 n1
    g2 (s2 : Rnm _ g2) (e2 : Env g2) r2 n2
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
| BigStep_Nil g a (e : Env g)
  : BigStep (@Nil _ a) e id_Rnm e VNil 0
| BigStep_Cons g a (v1 : V g a) (v2 : V g (List a)) e
  : BigStep (Cons v1 v2) e id_Rnm e (VCons v1 v2) 0
| BigStep_Foldr_Nil g a b (fnil : Tm g b) fcons (v : V g (List a)) e
    g1 (s1 : Rnm _ g1) (e1 : Env g1) r1 n1
  : Thunk VNil = lookup' v e ->
    BigStep fnil e s1 e1 r1 n1 ->
    BigStep (Foldr fnil fcons v) e s1 e1 r1 (S n1)
| BigStep_Foldr_Node g a b (fnil : Tm g b) (fcons : Tm (g :,: a :,: b) b) v e v1 v2
    g1 (s1 : Rnm _ g1) (e1 : Env g1) r1 n1
    g2 (s2 : Rnm _ g2) (e2 : Env g2) r2 n2
  : Thunk (VCons v1 v2) = lookup' v e ->
    LazyStep e (@BigStep g b (Foldr fnil fcons v2) e) s1 e1 r1 n1 ->
    BigStep (rename (shiftAlgCons v1 s1) fcons) (e1 :*: r1) s2 e2 r2 n2 ->
    BigStep (Foldr fnil fcons v) e (s1 >>> restr s2) e2 r2 (S (n1 + n2))
| BigStep_Base g b (x : b) e
  : BigStep (Bas (g := g) x) e id_Rnm e (VBas x) 0
.

Definition BigStep_ind :
forall
  P : forall (g : Ctx) (u : Ty),
      Tm g u ->
      Env g -> forall g' : Ctx, Rnm g g' -> Env g' -> Vl g' u -> nat -> Prop,
(forall (g : Ctx) (a b : Ty) (t1 : Tm g a) (t2 : Tm (g :,: a) b)
   (e : Env g) (g' : Ctx) (s' : Rnm (g :,: a) g')
   (e' : Env g') (r : Vl g' b) (n : nat),
 BigStep t2 (e :*: Undefined) s' e' r n ->
 P (g :,: a) b t2 (e :*: Undefined) g' s' e' r n ->
 P g b (Let t1 t2) e g' (restr s') e' r (S n)) ->
(forall (g : Ctx) (a b : Ty) (t1 : Tm g a) (t2 : Tm (g :,: a) b)
   (e : Env g) (g1 : Ctx) (s1 : Rnm g g1) (e1 : Env g1)
   (r1 : Vl g1 a) (n1 : nat) (g2 : Ctx) (s2 : Rnm (g1 :,: a) g2)
   (e2 : Env g2) (r2 : Vl g2 b) (n2 : nat),
 BigStep t1 e s1 e1 r1 n1 ->
 P g a t1 e g1 s1 e1 r1 n1 ->
 BigStep (rename (shift s1) t2) (e1 :*: Thunk r1) s2 e2 r2 n2 ->
 P (g1 :,: a) b (rename (shift s1) t2) (e1 :*: Thunk r1) g2 s2 e2 r2 n2 ->
 P g b (Let t1 t2) e g2 (s1 >>> restr s2) e2 r2 (S (n1 + n2))) ->
(forall (g : Ctx) (a b : Ty) (t : Tm g (Arr a b))
   (v : V g a) (e : Env g) (g1 : Ctx) (s1 : Rnm g g1)
   (e1 : Env g1) (r1 : Tm (g1 :,: a) b) (n1 : nat)
   (g2 : Ctx) (s2 : Rnm (g1 :,: a) g2) (e2 : Env g2)
   (r2 : Vl g2 b) (n2 : nat),
 BigStep t e s1 e1 (VLam r1) n1 ->
 P g (Arr a b) t e g1 s1 e1 (VLam r1) n1 ->
 BigStep r1 (e1 :*: lookup' (s1 a v) e1) s2 e2 r2 n2 ->
 P (g1 :,: a) b r1 (e1 :*: lookup' (s1 a v) e1) g2 s2 e2 r2 n2 ->
 P g b (App t v) e g2 (s1 >>> restr s2) e2 r2 (S (n1 + n2))) ->
(forall (g : Ctx) (a : Ty) (v : V g a) (e : Env g) (r : Vl g a),
 Thunk r = lookup' v e -> P g a (Var v) e g id_Rnm e r 1) ->
(forall (g : Ctx) (a b : Ty) (t : Tm (g :,: a) b) (e : Env g),
 P g (Arr a b) (Fun t) e g id_Rnm e (VLam t) 0) ->
(forall (g : Ctx) (a b : Ty) (v1 : V g a) (v2 : V g b) (e : Env g),
 P g (Prod a b) (Pair v1 v2) e g id_Rnm e (VPair v1 v2) 0) ->
(forall (g : Ctx) (a b : Ty) (v : V g (Prod a b))
   (e : Env g) (v1 : V g a) (v2 : V g b) (r1 : Vl g a),
 Thunk (VPair v1 v2) = lookup' v e ->
 Thunk r1 = lookup' v1 e -> P g a (Fst v) e g id_Rnm e r1 1) ->
(forall (g : Ctx) (a b : Ty) (v : V g (Prod a b))
   (e : Env g) (v1 : V g a) (v2 : V g b) (r2 : Vl g b),
 Thunk (VPair v1 v2) = lookup' v e ->
 Thunk r2 = lookup' v2 e -> P g b (Snd v) e g id_Rnm e r2 1) ->
(forall (g : Ctx) (a : Ty) (e : Env g), P g (List a) Nil e g id_Rnm e VNil 0) ->
(forall (g : Ctx) (a : Ty) (v1 : V g a) (v2 : V g (List a)) (e : Env g),
 P g (List a) (Cons v1 v2) e g id_Rnm e (VCons v1 v2) 0) ->
(forall (g : Ctx) (a b : Ty) (fnil : Tm g b)
   (fcons : Tm ((g :,: a) :,: b) b)
   (v : V g (List a)) (e : Env g) (g1 : Ctx) (s1 : Rnm g g1)
   (e1 : Env g1) (r1 : Vl g1 b) (n1 : nat),
 Thunk VNil = lookup' v e ->
 BigStep fnil e s1 e1 r1 n1 ->
 P g b fnil e g1 s1 e1 r1 n1 -> P g b (Foldr fnil fcons v) e g1 s1 e1 r1 (S n1)) ->
(forall (g : Ctx) (a b : Ty) (fnil : Tm g b)
   (fcons : Tm ((g :,: a) :,: b) b)
   (v : V g (List a)) (e : Env g) (v1 : V g a) (v2 : V g (List a)) (g1 : Ctx)
   (s1 : Rnm g g1) (e1 : Env g1) (r1 : T (Vl g1 b))
   (n1 : nat) (g2 : Ctx) (s2 : Rnm (g1 :,: b) g2) (e2 : Env g2)
   (r2 : Vl g2 b) (n2 : nat),
 Thunk (VCons v1 v2) = lookup' v e ->
 LazyStep e (andBS (BigStep (Foldr fnil fcons v2) e) (P _ _ (Foldr fnil fcons v2) e)) s1 e1 r1 n1 ->
 BigStep (rename (shiftAlgCons v1 s1) fcons) (e1 :*: r1) s2 e2 r2 n2 ->
 P (g1 :,: b) b (rename (shiftAlgCons v1 s1) fcons)
   (e1 :*: r1) g2 s2 e2 r2 n2 ->
 P g b (Foldr fnil fcons v) e g2 (s1 >>> restr s2) e2 r2 (S (n1 + n2))) ->
(forall (g : Ctx) (b : Type) (x : b) (e : Env g),
 P g (Base b) (Bas x) e g id_Rnm e (VBas x) 0) ->
forall (g : Ctx) (u : Ty) (t : Tm g u) (e : Env g)
  (g' : Ctx) (r : Rnm g g') (e0 : Env g') (v : Vl g' u)
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

(** Correspondence between the two semantics *)

(** Auxiliary evaluation functions. *)

Definition evalVl {g u} (e : env g) (t : Vl g u) : toType u :=
  match t with
  | VLam t => fun (x : T (toType _)) => eval t (e, x)
  | VPair x y => (lookup x e, lookup y e)
  | VNil => NilA
  | VCons x1 x2 => ConsA (lookup x1 e) (lookup x2 e)
  | VBas b => b
  end.

Fixpoint evalEnv {g} (e : Env g) : env g :=
  match e with
  | ENil => tt
  | ECons e1 v => (evalEnv e1, mapT (evalVl (evalEnv e1)) v)
  end.

(** Proof (soundness, then adequacy). *)

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

Lemma eta_Env g a (e : Env (g :,: a))
  : e = ECons (there e) (here e).
Proof.
  refine
   match e in Env g' return
     match g' with (_ :,: _) => fun e => _ | NilCtx => fun _ => True end e
   with
   | ENil => I
   | ECons _ _ => _
   end. reflexivity.
Qed.

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

Lemma eq_M_eq {a} (u1 u2 : M a) : eq_M u1 u2 -> u1 = u2.
Proof.
  intros H. do 2 (apply functional_extensionality; intros). apply prop_ext. auto.
Qed.

Fixpoint renameCtx {g g' : Ctx} : Rnm g g' -> env g' -> env g :=
  match g with
  | NilCtx => fun _ _ => tt
  | ConsCtx g a => fun s e => (renameCtx (restr s) e, lookup (s _ Here) e)
  end.

Fixpoint forCtx (g : Ctx) : (forall a : Ty, V g a -> T (toType a)) -> env g :=
  match g return (forall a, V g a -> T _)  -> env g with
  | NilCtx => fun _ => tt
  | ConsCtx g a => fun f => (forCtx (fun b v => f b (There v)), f a Here)
  end.

Lemma Proper_forCtx {g} (f f' : forall a : Ty, V g a -> T (toType a))
  : (forall a v, f a v = f' a v) ->
    forCtx f = forCtx f'.
Proof.
  induction g; cbn; intros H.
  - reflexivity.
  - f_equal; [ apply IHg; auto | apply H ].
Qed.

Lemma lookup_renameCtx {g g'} (s : Rnm g g') (e : env g') {a} (v : V g a)
  : lookup v (renameCtx s e) = lookup (s _ v) e.
Proof.
  induction v; cbn.
  - reflexivity.
  - apply IHv.
Qed.

Lemma renameCtx_cat {g g' g''} (s : Rnm g g') (s' : Rnm g' g'') (e : env g'')
  : renameCtx (s >>> s') e = renameCtx s (renameCtx s' e).
Proof.
  induction g; cbn.
  - reflexivity.
  - f_equal.
    + apply (IHg (fun _ v => s _ (There v))).
    + unfold cat_Rnm. symmetry; apply lookup_renameCtx.
Qed.

Fixpoint sub {g g'} : Rnm g (g ++ g') :=
  match g' with
  | NilCtx => id_Rnm
  | ConsCtx g' _ => fun _ v => There (sub v)
  end.

Fixpoint dropCtx {g g'} : env (g ++ g') -> env g :=
  match g' with
  | NilCtx => fun e => e
  | ConsCtx g' _ => fun e => dropCtx (fst e)
  end.

Fixpoint mvCtx {g1 g2 g'} (f : env g1 -> env g2) : env (g1 ++ g') -> env (g2 ++ g') :=
  match g' with
  | NilCtx => f
  | ConsCtx g' _ => fun e => (mvCtx f (fst e), snd e)
  end.

Lemma mv_dropCtx {g1 g2 g'} (f : env g1 -> env g2) (e : env (g1 ++ g'))
  : f (dropCtx e) = dropCtx (mvCtx f e).
Proof.
  induction g'; cbn; auto.
Qed.

Lemma renameCtx_ext {g g'} (s : Rnm g g') e e'
  : (forall a v, lookup (s a v) e = lookup v e') ->
    renameCtx s e = e'.
Proof.
  induction g; cbn; intros H.
  - destruct e'; reflexivity.
  - destruct e'; f_equal.
    + apply IHg. intros; apply H.
    + apply H.
Qed.

Lemma renameCtx_id {g} (e : env g) : renameCtx id_Rnm e = e.
Proof.
  apply renameCtx_ext. reflexivity.
Qed.

Theorem BigStep_heap_increasing' : forall g u (t : Tm g u) (e : Env g) g' (s' : Rnm g g') (e' : Env g') (v : Vl g' u) (n : nat),
  BigStep t e s' e' v n ->
  evalEnv e = renameCtx s' (evalEnv e').
Proof.
  intros * H; induction H; cbn [eval evalEnv renameCtx] in *; intros.
  all: try solve [symmetry; apply renameCtx_id].
  - apply (f_equal fst) in IHBigStep; cbn in IHBigStep.
    apply IHBigStep.
  - rewrite IHBigStep1.
    apply (f_equal fst) in IHBigStep2. cbn in IHBigStep2. rewrite IHBigStep2.
    symmetry; apply renameCtx_cat.
  - rewrite IHBigStep1.
    apply (f_equal fst) in IHBigStep2. cbn in IHBigStep2. rewrite IHBigStep2.
    symmetry; apply renameCtx_cat.
  - auto.
  - apply (f_equal fst) in IHBigStep; cbn in IHBigStep.
    destruct H0 as [ | ? ? ? ? ? [] ]; cbn in IHBigStep.
    + assumption.
    + rewrite H2.
      rewrite renameCtx_cat. f_equal. assumption.
Qed.

Theorem BigStep_heap_increasing : forall g u (t : Tm g u) (e : Env g) g' (s' : Rnm g g') (e' : Env g') (v : Vl g' u) (n : nat),
  BigStep t e s' e' v n ->
  forall a (v : _ a), lookup (s' _ v) (evalEnv e') = lookup v (evalEnv e).
Proof.
  intros * W a v; apply BigStep_heap_increasing' in W.
  rewrite W; auto using lookup_renameCtx.
Qed.

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

Lemma eq_M_foldrA {a b} (fnil fnil' : M b) (fcons fcons' : T a -> T b -> M b)
    (xs : T (ListA a))
  : eq_M fnil fnil' ->
    (forall x y, eq_M (fcons x y) (fcons' x y)) ->
    eq_M (foldrA fnil fcons xs) (foldrA fnil' fcons' xs).
Proof.
  intros J1 J2; destruct xs; cbn; [ apply eq_M_foldrA'; auto | apply Reflexive_eq_M ].
Qed.

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

Lemma eq_M_optim {a} (u1 u2 : M a) r
  : eq_M u1 u2 -> u1 [[ r ]] -> u2 [[ r ]].
Proof.
  unfold optimistic, eq_M. firstorder eauto.
Qed.

Lemma evalVl_renameVl g a (e : Env g) (v : Vl g a) g' (s : Rnm g g') (e' : Env g')
  : (forall a v, lookup (s a v) (evalEnv e') = lookup v (evalEnv e)) ->
    evalVl (evalEnv e) v = evalVl (evalEnv e') (renameVl s v).
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

Lemma lookup_evalEnv_ g a (e : Env g) (v : V g a) g' (s : Rnm g g') (e' : Env g')
  : (forall a v, lookup (s a v) (evalEnv e') = lookup v (evalEnv e)) ->
    lookup (s _ v) (evalEnv e') = mapT (evalVl (evalEnv e')) (lookup_' v s e).
Proof.
  intros H; rewrite H.
  revert e g' s e' H; induction v; cbn; intros.
  - rewrite eta_Env in *; cbn. destruct (here e); cbn; f_equal.
    apply evalVl_renameVl.
    intros ? ?. apply H.
  - rewrite eta_Env; cbn. apply IHv.
    intros ? vv. specialize (H _ (There vv)). cbn in H. rewrite eta_Env in H; apply H.
Qed.

Lemma lookup_evalEnv g a (e : Env g) (v : V g a)
  : lookup v (evalEnv e) = mapT (evalVl (evalEnv e)) (lookup' v e).
Proof.
  apply lookup_evalEnv_ with (s := id_Rnm).
  reflexivity.
Qed.

(** If [t] evaluates to value-cost pair [(v, n)] in the [BigStep] simantics
(Hacket & Hutton's Clairvoyant CBV), then [t] evaluates to [(evalVl _ v, n)]
in the [eval] semantics.
(Recall [optim m r] means "there exists a pair in [m] satisfying the postcondition [r]") *)
Theorem soundness : forall g u (t : Tm g u) (e : Env g) g' (s' : Rnm g g') (e' : Env g') (v : Vl g' u) (n : nat),
  BigStep t e s' e' v n ->
  (eval t (evalEnv e)) [[ fun x0 n0 => evalVl (evalEnv e') v = x0 /\ n = n0 ]].
Proof.
  intros * H; induction H; cbn [eval evalEnv] in *; intros; lucky_forward.
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
    rewrite lookup_evalEnv. cbn.
    lucky_forward. firstorder.
  - rewrite lookup_evalEnv, <- H; cbn.
    mforward idtac; firstorder.
  - firstorder.
  - cbn. firstorder.
  - rewrite lookup_evalEnv, <- H.
    cbn; lucky_forward.
    rewrite 2 lookup_evalEnv, <- H0; cbn.
    cbn; lucky_forward. firstorder.
  - rewrite lookup_evalEnv, <- H.
    cbn. lucky_forward.
    rewrite 2 lookup_evalEnv, <- H0; cbn.
    cbn; lucky_forward. firstorder.
  - firstorder.
  - firstorder.
  - rewrite lookup_evalEnv, <- H; cbn. lucky_forward. firstorder.
  - rewrite lookup_evalEnv, <- H; cbn. lucky_forward.
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

(*
Fixpoint eq_by_Ty (u : Ty) : toType u -> toType u -> Prop :=
  match u return toType u -> toType u -> Prop with
  | Arr u1 u2 => fun f g => forall x, eq_M eq_by_Ty (f x) (g x)
  | Prod u1 u2 => _
  | List u0 => _
  | Base b => _
  end.
*)

Ltac decomp H :=
  lazymatch type of H with
  | (exists x_, _) => let x := fresh x_ in destruct H as [x H]; decomp H
  | (_ /\ _) =>
    let H1 := fresh H in
    destruct H as [H1 H]; decomp H
  | _ => idtac
  end.

Ltac prove_assum H :=
  lazymatch type of H with
  | (?T -> _) =>
    let w := fresh in
    assert (w : T); [ | specialize (H w); clear w ]
  end.

Definition eq_Rnm g g' (s1 s2 : Rnm g g') : Prop :=
  forall a v, s1 a v = s2 a v.

Declare Scope rnm_scope.
Delimit Scope rnm_scope with rnm.
Infix "=" := eq_Rnm : rnm_scope.

Lemma Transitive_eq_Rnm g g' (s1 s2 s3 : Rnm g g')
  : (s1 = s2)%rnm -> (s2 = s3)%rnm -> (s1 = s3)%rnm.
Proof. unfold eq_Rnm; etransitivity; eauto. Qed.

Instance Equivalence_eq_Rnm g g' : Equivalence (@eq_Rnm g g').
Proof.
  constructor; red; unfold eq_Rnm; [reflexivity | symmetry | etransitivity]; eauto.
Qed.

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

Lemma rename_cat_Rnm g1 g2 g3 (s1 : Rnm g1 g2) (s2 : Rnm g2 g3) (a : Ty) (t : Tm g1 a)
  : rename (s1 >>> s2) t = rename s2 (rename s1 t).
Proof.
  revert g2 g3 s1 s2; induction t; cbn; intros; f_equal; auto.
  all: etransitivity; [ apply Proper_rename; try apply shift_cat_Rnm | ]; auto.
  eapply Transitive_eq_Rnm; [ apply Proper_shift | ]; apply shift_cat_Rnm.
Qed.

Lemma rename_id g a (t : Tm g a) : rename id_Rnm t = t.
Proof.
  induction t; cbn; intros; f_equal; auto.
  all: etransitivity; [ apply Proper_rename; try apply shift_id | ]; eauto.
  etransitivity; [ apply Proper_shift |]; apply shift_id.
Qed.

Lemma renameCtx_restr_shift g g' (s : Rnm g g') e a (v : T (toType a))
  : renameCtx (restr (shift s)) (e, v) = renameCtx s e.
Proof.
  apply renameCtx_ext; intros; rewrite lookup_renameCtx; reflexivity.
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

(** Proof by induction on cost, which is luckily available already (otherwise we'd have
to redefine the interpreter with fuel). *)
Theorem adequacy_ : forall n g u (t : Tm g u) (f : env g),
    (eval t f) {{ fun (x0 : toType u) n0 =>
      n = n0 ->
      forall g0 (s0 : Rnm g g0) (e0 : Env g0),
        f = renameCtx s0 (evalEnv e0) ->
        exists g' (s' : Rnm g0 g') (e' : Env g') (v' : Vl g' u),
          evalVl (evalEnv e') v' = x0 /\
          BigStep (rename s0 t) e0 s' e' v' n0 }}.
Proof.
  induction n as [n IH] using lt_wf_ind; intros *; destruct t; cbn; lucky_forward.
  - intros y1 n1 Hy1 y2 n2 Hy2 -> * Hf.
    assert (IH1 := IH n1 ltac:(lia) _ _ _ _ _ _ Hy1 eq_refl _ s0 e0 Hf).
    decomp IH1.
    assert (IH2 := IH n2 ltac:(lia) _ _ _ _ _ _ Hy2 eq_refl _ (shift (cat_Rnm s0 s')) (ECons e' (Thunk v'))).
    prove_assum IH2.
    { cbn; f_equal; [ | f_equal; auto].
      rewrite Hf.
      apply renameCtx_ext; intros; rewrite lookup_renameCtx.
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
    (* For unknown reasons, [lia] gets stuck here. *)
    specialize (IH n2 ltac:(omega)  _ _ _ _ _ _ Hy2 eq_refl _ (shift s0) (e0 :*: Undefined)).
    prove_assum IH; [ cbn; f_equal; subst f; solve [auto using renameCtx_restr_shift] | ].
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
    { rewrite renameCtx_id. cbn. f_equal.
      rewrite Hf. rewrite lookup_renameCtx, <- lookup_evalEnv.
      rewrite (BigStep_heap_increasing IH1).
      reflexivity. }
    decomp IH2.
    rewrite rename_id in IH2.
    eexists _, _, _, _. split; [ eassumption | ].
    econstructor; try eassumption.
  - intros ? H -> * Hf.
    rewrite Hf in H.
    rewrite lookup_renameCtx, lookup_evalEnv in H.
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
      { rewrite Hf, lookup_renameCtx; reflexivity. } }
    constructor.
  - intros -> * Hf.
    eexists _, _, _, (VPair (s0 _ v) (s0 _ v0)).
    split.
    { cbn. rewrite Hf, 2 lookup_renameCtx; reflexivity. }
    constructor.
  - intros ? Hv. mforward idtac. intros ? Hfst.
    intros -> * Hf.
    rewrite Hf, lookup_renameCtx, lookup_evalEnv in Hv.
    destruct (lookup' _ _) eqn:Hlookup in Hv; cbn in Hv; [ | discriminate ].
    injection Hv; clear Hv; intros Hv.
    assert (Hv' := inv_Vl x1); cbn in Hv'; destruct Hv' as (X1 & X2 & ->).
    cbn in Hv; rewrite <- Hv in Hfst; cbn in Hfst.
    rewrite lookup_evalEnv in Hfst.
    destruct (lookup' _ _) eqn:Hlookup2 in Hfst; cbn in Hfst; [ | discriminate ].
    injection Hfst; clear Hfst; intros Hfst.
    eexists _, _, _, x1.
    split; [ eassumption | ].
    econstructor; try eauto.
  - intros ? Hv. mforward idtac. intros ? Hfst.
    intros -> * Hf.
    rewrite Hf, lookup_renameCtx, lookup_evalEnv in Hv.
    destruct (lookup' _ _) eqn:Hlookup in Hv; cbn in Hv; [ | discriminate ].
    injection Hv; clear Hv; intros Hv.
    assert (Hv' := inv_Vl x1); cbn in Hv'; destruct Hv' as (X1 & X2 & ->).
    cbn in Hv; rewrite <- Hv in Hfst; cbn in Hfst.
    rewrite lookup_evalEnv in Hfst.
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
    { cbn. rewrite Hf, 2 lookup_renameCtx; reflexivity. }
    constructor.
  - destruct (lookup v f) eqn:Hvf; cbn; [ | mforward idtac].
    intros y1 n1 Hy1 En * Hf.
    rewrite Hf in Hvf.
    rewrite lookup_renameCtx, lookup_evalEnv in Hvf.
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
      assert (IH1 := IH n1 ltac:(lia) _ _ (Foldr (rename s0 t1) (rename (shift (shift s0)) t2) x2) (evalEnv e0) y1 n1).
      prove_assum IH1.
      { cbn; unfold foldrA. rewrite H. cbn. revert Hy1. subst.
        apply eq_M_foldrA'.
        + apply Symmetric_eq_M. apply evalRnm. intros. rewrite lookup_renameCtx.
          reflexivity.
        + intros. apply Symmetric_eq_M, evalRnm.
          apply V_split; [ apply V_split | ]; intros; cbn; try reflexivity.
          rewrite lookup_renameCtx. reflexivity. }
      specialize (IH1 eq_refl _ id_Rnm e0).
      prove_assum IH1; [ rewrite renameCtx_id; reflexivity | ].
      decomp IH1; rewrite rename_id in IH1.
      specialize (IH n2 ltac:(lia) _ _ t2 _ _ _ Hy2 eq_refl _ (shift (shift s0) >>> shiftAlgCons x1 s')).
      specialize (IH (e' :*: Thunk v')).
      prove_assum IH.
      { symmetry; apply renameCtx_ext. apply V_split; [ apply V_split |]; cbn.
        - intros; rewrite Hf, lookup_renameCtx; auto.
          rewrite (BigStep_heap_increasing IH1). reflexivity.
        - rewrite (BigStep_heap_increasing IH1). reflexivity.
        - f_equal; auto. }
      decomp IH.
      eexists _, _, _, _.  split; [ eauto | ].
      eapply BigStep_Foldr_Node; eauto.
      { constructor. eassumption. }
      { rewrite rename_cat_Rnm in IH. eassumption. }
    + intros y1 n1 Hy1 ->.
      assert (IH1 := IH n1 ltac:(omega) _ _ _ _ _ _ Hy1 eq_refl).
      specialize (IH1 _ (shift (shift s0) >>> shiftAlgCons x1 id_Rnm) (e0 :*: Undefined)).
      prove_assum IH1.
      { symmetry; apply renameCtx_ext; apply V_split; [ apply V_split | ]; intros; cbn.
        - rewrite Hf, lookup_renameCtx. reflexivity.
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
Theorem adequacy g u (t : Tm g u) (e : Env g)
  : (eval t (evalEnv e))
      {{ fun (x' : toType u) n' => exists g' (s' : Rnm g g') (e' : Env g') (v' : Vl g' u),
             evalVl (evalEnv e') v' = x' /\
             BigStep t e s' e' v' n' }}.
Proof.
  intros y0 n0 Hy0.
  assert (AQ := adequacy_ t Hy0 eq_refl id_Rnm ltac:(rewrite renameCtx_id; reflexivity)).
  rewrite rename_id in AQ. assumption.
Qed.

Definition elem {a} (z : M a) (x : a) (n : nat) : Prop := z x n.

(** This theorem combines soundness and adequacy to make the equivalence more
explicit using [<->]. *)
Theorem soundess_and_adequacy g u (t : Tm g u) (e : Env g) (x : toType u) (n : nat)
  : elem (eval t (evalEnv e)) x n
  <-> exists g' (s' : Rnm g g') (e' : Env g') (v' : Vl g' u),
        evalVl (evalEnv e') v' = x /\
        BigStep t e s' e' v' n.
Proof.
  split; [ apply adequacy | ].
  intros H; decomp H; apply soundness in H. red in H; decomp H.
  red. subst; auto.
Qed.

End Lambda.
