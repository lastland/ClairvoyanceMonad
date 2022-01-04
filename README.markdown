# Reasoning about the garden of forking paths (artifact)

This artifact contains the Coq formalization of the paper [_Reasoning about the
Garden of Forking Paths_](https://doi.org/10.1145/3473585).

The paper presents a novel and simple framework for formally reasoning about
lazy computation costs based on a recent model of lazy evaluation: clairvoyant
call-by-value. The key feature of our framework is its simplicity, as expressed
by our definition of the clairvoyance monad. This monad is both simple to define
(around 20 lines of Coq) and simple to reason about. We show that this monad can
be effectively used to mechanically reason about the computational cost of lazy
functional programs written in Coq.

The artifact supports the claims in the paper in two ways:

- The artifact contains the definitions, reference implementations, the
  specifications, and proofs that programs satisfy the specifications in
  Coq. This part is contained in file `Clairvoyance.v`.
- The artifact contains the formalization of our translation (presented in
  Section 4 of the paper), and a proof of equivalence between our translation
  and the operational semantics of Hackett & Hutton (2019). This part is
  contained in file `Translation.v`.

## How to use this artifact

### Dependencies

If you are accessing the artifact via the VM image we provide, you should have
all the dependencies installed already.

The artifact requires [the Coq proof assistant](https://coq.inria.fr/). The
artifact is known to work with Coq versions 8.11.2, 8.12.2, and 8.13.2.

The artifact also requires the [Equations
library](https://github.com/mattam82/Coq-Equations). To install it via
OPAM:

``` shell
opam repo add coq-released https://coq.inria.fr/opam/released
opam install coq-equations
```
The artifact is known to work with Equations 1.2.4.

### Proof check

To check all the proofs contained in the artifact, you just need to
run `make`:

``` shell
make
```

This will invoke Coq to check the proofs in files `Clairvoyance.v` and
`Translation.v`.

The actual execution time may vary depending on the machine and the Coq version
you are using. We have seen the process takes 8-20 seconds on different
computers with different Coq versions.

### Checking axioms

The proofs in `Clairvoyance.v` does not rely on any additional axioms. The
proofs in `Translation.v` rely on axioms for functional and propositional
extensionality.

The artifact does not contain any unfinished/admitted proofs. There are two ways
to check the axioms our proofs rely on:

(1) You can search keywords such as `admit` or `Axiom`:

``` shell
grep -i admit ./*.v
grep -i axiom ./*.v
```

(The `-i` option ignores the cases. By searching `admit` with this option, both
the `admit` and `Admitted` keywords are covered.)

(2) You can use the `Print Assumptions` command [provided by
Coq](https://coq.inria.fr/refman/proof-engine/vernacular-commands.html#coq:cmd.Print-Assumptions). For
example, you can add the following line to the end of the `Translation.v` file:

``` coq
Print Assumptions Lambda.soundess_and_adequacy.
```

You should see that the `soundness_and_adequacy` theorem relies on two axioms:
they are functional and propositional extensionality.

### Checking main claims of the paper

A paper draft has also been provided in the submission. We have listed all the
main claims in the paper and where to find them in the next section of this
file. We have also added comments to the definitions/theorems for
illustration. You can cross check the claims of the paper with what's
implemented in the Coq files.

## Main claims of the paper

If you are looking for the code corresponding to a figure, you can search the
figure label in one of the two files. For example, if you are looking for the
formalization of the monadic translation presented in Fig. 8, you can find it by
searching "Figure 8" in the `Translation.v` file.

### The clairvoyance monad

In Section 3 of the paper, we introduce _the clairvoyance monad_.

The core definitions presented in Fig. 4 can be found in the `ClairvoyanceMonad`
section of the file `Clairvoyance.v`. The notations defined in the paper can
also be found right after the section.

### Translation

In Section 4 of the paper, we define a translation from pure programs to monadic
programs.

- The calculus defined in Fig. 6 can be found after the comment "the calculus
  with folds" in the `Lambda` module of the file `Translation.v`.
- The type translation presented in Fig. 7 can be found in the `toType` function
  within the same module.
- The term translation presented in Fig. 8 can be found in the `eval` function
  within the same module.
- The definition of `foldrA` presented in Fig. 9 can be found within the same
  module. The names of the definitions in the Coq file are exactly the same as
  the ones in the figure.
- The operational semantics of Hackett & Hutton (2019) is formalized as an
  inductive relation called `BigStep` within the same module.
- Theorem 4.1 presented in Section 4.2 is the final theorem
  `soundness_and_adequacy` in the `Translation.v` file. We prove the theorem by
  utilizing two lemmas: `soundness` and `adequacy`. Both lemmas can be found in
  the same Coq file.
- The Definitions presented in Fig. 10 can be found in the end of the file
  `Clairvoyance.v` (note that they are in a different file than the previous
  definitions).
- The Definitions presented in Fig. 11 can be found in the `TranslationExample`
  section of `Clairvoyance.v` (note that they are in a different file than the
  previous definitions).
- The two rewrite rules presented in Section 4.4 are proved in the
  `Translation.v` file and the corresponding theorems are called `bind_tick` and
  `thunk_tick`, respectively.

### Formal reasoning and case study

In section 5 of the paper, we discuss the formal reasoning rules based on
optimistic and pessimistic specifications. In section 6, we demonstrate the
formal reasoning methodology in some example related to tail recursions.

- All the code snippets shown in these two sections can be found in the file
  `Clairvoyance.v`. They are marked explicitly by the section numbers in the
  comments of the file.
- The inference rules presented in Fig. 13 and Fig. 14 can be found in the
  `InferenceRules` section of the file `Clairvoyance.v`.
