From Coq Require Import Lia.
From Clairvoyance Require Import Core Tick Approx.

Lemma thunkD_cost : forall {A B : Type} `{LessDefined A} `{Bottom B}
                      (x : A) (y : T A) (f : A -> Tick B),
  y = Thunk x \/ y = Undefined ->
  Tick.cost (thunkD f y) <= Tick.cost (f x).
Proof.
  intros. destruct H1; subst; simpl; lia.
Qed.

Lemma bind_cost : forall {A B : Type} (m : Tick A) (k : A -> Tick B),
  Tick.cost (Tick.bind m (fun x => k x)) =
    Tick.cost m + Tick.cost (k (Tick.val m)).
Proof. reflexivity. Qed.
