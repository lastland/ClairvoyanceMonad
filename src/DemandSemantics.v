From Coq Require Import List.
Import ListNotations.

From Clairvoyance Require Import Misc Core.

Set Implicit Arguments.
Set Contextual Implicit.

Inductive listA (A : Type) : Type :=
| NilA : listA A
| ConsA : A -> Core.T (listA A) -> listA A
.

Inductive type : Type :=
| Nat
| List : type -> type
| Fun : type -> type -> type
| Prod : type -> type -> type
| T : type -> type
.

Inductive context : Type :=
| CEmpty
| Snoc : context -> type -> context
.

Infix ",," := Snoc (at level 40).

Inductive var (A : type) : context -> Type :=
| Here (G : context) : var A (G ,, A)
| There (G : context) (B : type) : var A G -> var A (G ,, B)
.

Inductive term (G : context) : type -> Type :=
| Var {A : type} : var A G -> term G A
| Lam {A B : type} : term (G ,, A) B -> term G (Fun A B)
| App {A B : type} : term G (Fun A B) -> term G A -> term G B
| Lazy {A : type} : term G A -> term G (T A)
| Force {A : type} : term G (T A) -> term G A
| Let {A B : type} : term G A -> term (G ,, A) B -> term G B
| Pair {A B : type} : term G A -> term G B -> term G (Prod A B)
| Fst {A B : type} : term G (Prod A B) -> term G A
| Snd {A B : type} : term G (Prod A B) -> term G B
| Nil {A : type} : term G (List A)
| Cons {A : type} : term G A -> term G (T (List A)) -> term G (List A)
| Foldr {A B : type} : term G B -> term (G ,, A ,, T B) B -> term G (List A) -> term G B
(* | Weaken H (A : type) : H `subset_of` G -> term H A -> term G A *)
.

Definition T_map {A B : Type} (f : A -> B) (x : Core.T A) : Core.T B :=
  match x with
  | Undefined => Undefined
  | Thunk x => Thunk (f x)
  end.

Fixpoint foldr {A B : Type} (z : B) (f : A -> Core.T B -> B) (xs : listA A) : B :=
  match xs with
  | NilA => z
  | ConsA x xs => f x (T_map (foldr z f) xs)
  end.

Section Eval.

Context (closure : Type -> Type -> Type).
Context (Apply : forall A B, closure A B -> A -> B).

Fixpoint eval_type (A : type) : Type :=
  match A with
  | Nat => nat
  | List A => listA (eval_type A)
  | Fun A B => closure (eval_type A) (eval_type B)
  | Prod A B => eval_type A * eval_type B
  | T A => Core.T (eval_type A)
  end.

Fixpoint eval_context (G : context) : Type :=
  match G with
  | CEmpty => unit
  | Snoc G A => eval_context G * eval_type A
  end.

Fixpoint Closure (sigs : list (Type * Type * Type)) (A B : Type) : Type :=
  match sigs with
  | nil => Empty_set
  | s :: sigs =>
    let C := fst (fst s) in
    let A' := snd (fst s) in
    let B' := snd s in
    C * (A' = A) * (B' = B) + Closure sigs A B
  end.

Fixpoint eval_var_fwd {G : context} {A : type} (v : var A G) : eval_context G -> eval_type A :=
  match v with
  | Here => fun g => snd g
  | There v => fun g => eval_var_fwd v (fst g)
  end.

Fixpoint list_closures {G : context} {A : type} (t : term G A) : list (Type * Type * Type) :=
  match t with
  | Var _ | Nil => []
  | @Lam _ A B t => (eval_context G, eval_type A, eval_type B) :: list_closures t
  | Lazy t | Force t | Fst t | Snd t => list_closures t
  | App t u | Let t u | Pair t u | Cons t u => list_closures t ++ list_closures u
  | Foldr t u v => list_closures t ++ list_closures u ++ list_closures v
  end.

Definition Closure_alg (C : Type -> Type -> Type) (xs : list (Type * Type * Type))  : Type :=
  forall A B, Closure xs A B -> C A B.

Definition closure_alg {G A} (t : term G A) : Type :=
  Closure_alg closure (list_closures t).

Definition absurd C : forall A B, Closure [] A B -> C A B := fun _ _ v => match v with end.
Arguments absurd : clear implicits.
Arguments absurd {C}.

Definition tl_calg {C} s s1 : Closure_alg C (s :: s1) -> Closure_alg C s1 :=
  fun f A B x => f A B (inr x).

Fixpoint fst_calg {C} s1 s2 : Closure_alg C (s1 ++ s2) -> Closure_alg C s1 :=
  match s1 return Closure_alg C (s1 ++ s2) -> _ with
  | [] => fun f => absurd
  | s :: s1 => fun f A B (x : Closure (s :: s1) A B) =>
    match x with
    | inl x => f A B (inl x)
    | inr x => fst_calg s1 s2 (tl_calg f) _ _ x
    end
  end.

Fixpoint snd_calg {C} s1 s2 : Closure_alg C (s1 ++ s2) -> Closure_alg C s2 :=
  match s1 return Closure_alg C (s1 ++ s2) -> Closure_alg C s2 with
  | [] => fun f => f
  | _ :: s1 => fun f => snd_calg s1 s2 (tl_calg f)
  end.

Fixpoint pair_calg {C} s1 s2 : Closure_alg C s1 -> Closure_alg C s2 -> Closure_alg C (s1 ++ s2) :=
  match s1 return Closure_alg C s1 -> Closure_alg C s2 -> Closure_alg C (s1 ++ s2) with
  | [] => fun f1 f2 => f2
  | s :: s1 => fun f1 f2 A B x =>
    match x with
    | inl x => f1 _ _ (inl x)
    | inr x => pair_calg (tl_calg f1) f2 _ _ x
    end
  end.

Record semantics {G A} (t : term G A) : Type :=
  { value : eval_context G -> option (eval_type A)
  ; apply : forall A B, Closure (list_closures t) A B -> A -> option B
  }.
Arguments Build_semantics {G A} t &.

Definition lift2_option {A B C} (f : A -> B -> C) : option A -> option B -> option C.
Admitted.

Definition join_T_option {A} : Core.T (option A) -> Core.T A.
Admitted.

Fixpoint eval_fwd {G : context} {A : type} (t : term G A) : closure_alg t -> semantics t :=
  match t return closure_alg t -> semantics t with
  | Var v => fun _ => {| value := fun g => Some (eval_var_fwd v g)
                       ; apply := absurd |}
  | Lam t => fun f => {| value := fun g => Some (f _ _ (inl (g, eq_refl, eq_refl)))
                       ; apply := fun A B k =>
                           let w := eval_fwd (G := G ,, _) (t := t) (tl_calg f) in
                           match k with
                           | inl (g, d, e) =>
                             match d, e with eq_refl, eq_refl => fun x => value w (g, x) end
                           | inr k => apply w k
                           end |}
  | App t u => fun f =>
      let wt := eval_fwd (t := t) (fst_calg _ _ f) in
      let wu := eval_fwd (t := u) (snd_calg _ _ f) in
      {| value := fun g => lift2_option (@Apply _ _) (value wt g) (value wu g)
       ; apply := pair_calg (apply wt) (apply wu)
      |}
  | Let t u => fun f =>
      let wt := eval_fwd (t := t) (fst_calg _ _ f) in
      let wu := eval_fwd (t := u) (snd_calg _ _ f) in
      {| value := fun g => option_bind (value wt g) (fun x =>
                           value wu (g, x))
       ; apply := pair_calg (apply wt) (apply wu) |}
  | Lazy t => fun f =>
      let w := eval_fwd (t := t) f in
      {| value := fun g => Some match value w g with
                           | Some x => Thunk x
                           | None => Undefined
                           end
       ; apply := apply w |}
  | Force t => fun f =>
      let w := eval_fwd (t := t) f in
      {| value := fun g => match value w g with
                           | Some (Core.Thunk v) => Some v
                           | None | Some Core.Undefined => None
                           end
       ; apply := apply w |}
  | Pair t u => fun f =>
      let wt := eval_fwd (t := t) (fst_calg _ _ f) in
      let wu := eval_fwd (t := u) (snd_calg _ _ f) in
      {| value := fun g => lift2_option pair (value wt g) (value wu g)
       ; apply := pair_calg (apply wt) (apply wu) |}
  | Fst t => fun f =>
      let w := eval_fwd (t := t) f in
      {| value := fun g => option_map fst (value w g)
       ; apply := apply w |}
  | Snd t => fun f =>
      let w := eval_fwd (t := t) f in
      {| value := fun g => option_map snd (value w g)
       ; apply := apply w |}
  | Nil => fun _ => {| value := fun _ => Some NilA
                    ;  apply := absurd |}
  | Cons t u => fun f =>
      let wt := eval_fwd (t := t) (fst_calg _ _ f) in
      let wu := eval_fwd (t := u) (snd_calg _ _ f) in
      {| value := fun g => lift2_option (@ConsA _) (value wt g) (value wu g)
       ; apply := pair_calg (apply wt) (apply wu) |}
  | Foldr t u v => fun f =>
      let wt := eval_fwd (t := t) (fst_calg _ _ f) in
      let wu := eval_fwd (t := u) (fst_calg _ _ (snd_calg _ _ f)) in
      let wv := eval_fwd (t := v) (snd_calg _ _ (snd_calg _ _ f) )in
      {| value := fun g => option_bind (value wv g) (fun xs =>
                           foldr (value wt g) (fun x y => value wu ((g, x), join_T_option y)) xs)
       ; apply := pair_calg (apply wt) (pair_calg (apply wu) (apply wv)) |}
  end.

End Eval.

Inductive vclosure (value_ : type -> Type) (A B : type) : list (type * type * type) -> Type :=
| CHere C sigs : vclosure value_ A B ((C, A, B) :: sigs)
| CThere s sigs : vclosure value_ A B (s :: sigs)
.

Inductive val (sigs : list (type * type * type)) : type -> Type :=
| VNat : nat -> val sigs Nat
| VPair A B : val sigs A -> val sigs B -> val sigs (Prod A B)
| VThunk A : val sigs A -> val sigs (T A)
| VUndef A : val sigs (T A)
| VNil A : val sigs (List A)
| VCons A : val sigs A -> val sigs (T (List A)) -> val sigs (List A)
| VClos A B : vclosure (val sigs) A B sigs -> val sigs (Fun A B)
.
