From Coq Require Import Arith List Lia Setoid Morphisms RelationClasses.
Import ListNotations.
From Clairvoyance Require Import Core Approx ApproxM List Misc Tick.

(** * The approximation version (with clairvoyance monad)

    I put the approximation version of [take] here just for reference. We will
    not use these definitions in this file.
*)

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

Import Tick.Notations.

(** * A demand tick monad.

    This part defines a monad [D] for demand functions. The monad I use here is
    slightly different from that of Li-yao's by adding an option
    transformer. The option transformer is used to indicate impossible cases
    (represented by [bottom] function). Li-yao's version also has a [bottom]
    function which marks cost as 0---but it can be [bind]ed with other
    operations to get a non-zero cost. Here I'm explicitly marking failures,
    which would be important for the [posthoc] logic shown later in this
    file. *)

Section DemandTick.

  Context {A B : Type}.

  (* We can theoretically just use [M]---but I use this type here to emphasize
  that there is *no* nondeterminism. *)
  Definition D (A : Type) : Type := Tick (option A).

  Definition ret (a : A) : D A :=
    Tick.ret (Some a).

  Definition bind (m : D A) (k : A -> D B) : D B :=
    match m with
    | Tick.MkTick na oa =>
        match oa with
        | Some a => Tick.bind (Tick.MkTick na a) k
        | None => Tick.ret None
        end
    end.

  Definition bottom : D A :=
    Tick.ret None.

End DemandTick.

Definition tick : D unit :=
  Tick.bind Tick.tick (fun _ => Tick.ret (Some tt)).

Declare Scope D_scope.

Notation "u >> v" := (bind u (fun _ => v)) (at level 61, left associativity) : D_scope.

Open Scope D_scope.

(** * The demand version (with the D monad)

    A relatively mechanical demand translation of [take] using the demand tick
    monad we just defined. We might be able to simplify the program using some
    combinators? *)
Fixpoint takeD {a : Type} (n : nat)(xs : list a) (outD : listA a) : D (T (listA a)) :=
  tick >>
  match n, xs with
  | O, _ =>
      match outD with
      | NilA => ret Undefined
      (* In this case, the output can only be [NilA]---see [take_], so we mark
      all other branches using [bottom]. *)
      | _ => bottom
      end
  | S _, nil =>
      match outD with
      | NilA => ret (Thunk NilA)
      (* In this case, the output can only be [NilA]---see [take_], so we mark
      all other branches using [bottom]. *)
      | _ => bottom
      end
  | S n1, x :: xs1 =>
      match outD with
      | NilA => bottom
      | ConsA x t =>
          (* Perhaps a place for combinators like [thunkD]? *)
          bind (match t with
                | Undefined => ret Undefined
                | Thunk t => takeD n1 xs1 t
                end)
            (fun i => ret (Thunk (ConsA x i)))
      end
  end.

(* If we only need the first element of the output. *)
Definition ex1 : D (T (listA nat)) :=
  takeD 1 [1; 2; 3] (ConsA (Thunk 1) Undefined).

(* If we also need to know that the first element is followed by a nil. *)
Definition ex2 : D (T (listA nat)) :=
  takeD 1 [1; 2; 3] (ConsA (Thunk 1) (Thunk NilA)).

Compute ex1. (* should be 1 *)
Compute ex2. (* should be 2 *)

(** * Definitions of our specification.

    Since the demand functions are *deterministic*, we only need a
    specification based on over-approximation.  *)

Definition posthoc {A B} (t : A -> D B) (r : B -> A -> nat -> Prop) : Prop :=
  forall (a : A), match t a with
             | Tick.MkTick n (Some b) => r b a n
             | _ => True
             end.

Notation " t {{ r }} " := (posthoc t r) (at level 42) : D_scope.


(* List approximation [a] is a prefix of list approximation [b]. This is
   different from [less_defined] because [a] can end with a [nil] early. *)
Fixpoint prefix {A} (a : listA A) (b : T (listA A)) : Prop :=
  match a with
  | NilA => True
  | ConsA x xs =>
      match b with
      | Thunk (ConsA y ys) =>
          x = y /\ (match xs with
                   | Undefined => True
                   | Thunk xs' => prefix xs' ys
                   end)
      | _ => False
      end
  end.

(** * Specification and proof.

    This contains both functional correctness and cost.

    Functional correctness: output is a prefix of the input.

    Cost: cost equals to the "size" of output---by some definition of size. *)
Theorem takeD_spec {A} `{LessDefined A} :
  forall (n : nat) (xs : list A),
    takeD n xs {{ fun inD outD cost => prefix outD inD /\
                                      cost = sizeX' 1 outD }}.
Proof.
  induction n; intros.
  - intros outD. cbn.
    destruct outD; cbn; try tauto.
  - intros outD. cbn.
    destruct outD; cbn; try tauto.
    + destruct xs; cbn; try tauto.
    + destruct xs eqn:Hxs; cbn; try tauto.
      destruct x2; cbn; try tauto.
      specialize (IHn l x). cbn in IHn.
      destruct (takeD n l x) eqn:Ht. destruct val.
      * cbn. intuition.
      * cbn. trivial.
Qed.
