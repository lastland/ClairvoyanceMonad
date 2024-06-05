# ICFP 2024 Artifact

Name:    **Story of Your Lazy Function’s Life: A Bidirectional Demand Semantics for Mechanized Cost Analysis of Lazy Programs**

## Artifact Instructions

If you using the VM image. The project lives in the `demand-semantics` directory
under the home directory of the default `artifact` user. (Whenever a password is
required, enter `password`.) The image already has all dependencies installed;
to ask the Rocq Prover (AKA Coq) to proof check all the proof scripts, you just
need to run `make`.

### Dependencies

The project is known to work with Rocq Prover (AKA Coq) versions 8.16.1, 8.17.1,
8.18.0, and 8.19.1. You also need the following Rocq Prover libraries and
plugins:

- [Equations](https://github.com/mattam82/Coq-Equations)
- [CoqHammer](https://github.com/lukaszcz/coqhammer) (only the `sauto` component
  is needed; no need for installing an SMT solver)

Both of these components are part of the [Coq
platform](https://github.com/coq/platform).

### Checking axioms

To check the axioms of a named proof term, use the command `Print Assumptions
[name]`. If you check the major proof terms, you should see only the axiom
`Classical_Prop.classic`, which is the law of excluded middle.

## Correspondence between the paper and the project

### Bidirectional demand semantics

The fundamental `T` datatype and its basic theory is defined in `Core.v`.
Approximation types for other common types include `listA` (`ListA.v`),
`optionA` (`Option.v`), and `prodA` (`Prod.v`).

General notions relating to approximations are defined in `Approx.v`.

- The typeclass `LessDefined` represents the lattice of approximations itself:
  an instance `LessDefined A` defines the approximation relation, written ≤ in
  the paper and called `less_defined` in Rocq, for the type `A`. The paper
  states facts about this relation as lemmas (e.g., Lemma 3.1, transitivity);
  however, in Rocq, each instance must be proven to be a preorder.
- There is also a `Bottom` typeclass, which shows how to compute the least
  element in the less-defined relation for a type; i.e., ⊥ from the paper.
  `Bottom` is only defined for `T A` or types that wrap it; i.e., monads
  returning `T A`.
- The typeclass `Exact` shows how to embed a type into its type of
  approximations (via the `exact` method). The `ExactMaximal` typeclass is a law
  for `Exact`: it says that an embedded value should be a maximal element with
  respect to `less_defined`. We *define* the "approximates" relation `is_approx`
  (written ≺ in the paper) by saying that a value `xD` approximates `x` if `xD`
  is less defined than `exact x`; i.e., `xD` lies below `exact x` in the lattice
  of approximations.
- The typeclass `Lub` shows how to compute the least upper bound (supremum) of
  two approximations, written ⊔ in the paper and called `lub` in Rocq. The
  `LubLaw` typeclass defines laws for `Lub`, corresponding to Lemma 3.2. (Part
  (1) of Lemma 3.2 is an immediate consequence of `lub_least_upper_bound`,
  `exact_maximal` from the `ExactMaximal` typeclass, and transitivity.)
- The `BottomOf` typeclass shows how to compute the least approximation for an
  element `a`, written ⊥ₐ in the paper and called `bottom_of` in Rocq. Lemma 3.3
  is represented by the `BottomIsLeast` typeclass.
- The `Exact`, `LessDefined`, `Lub`, and `BottomOf` typeclasses, plus their
  laws, are bundled together in the `IsApproxAlgebra` typeclass.

Since we lack a mechanized translation (discussed in Section 2.3 in the paper),
each pure function in the Rocq development gets its own hand-written
demand-semantics version: a pure function, say, `f : A₁ → A₂ → ⋯ → Aₙ → B`, will
typically have a demand-semantics version `fD : A₁ → A₂ → ⋯ → Aₙ → Bᴰ → Tick (T
A₁ᴰ * T A₂ᴰ * ⋯ * T Aₙᴰ)`.

The `Tick` monad, defined in `Tick.v`, is used to count function calls, which is
our cost model: it is essentially a writer monad over the monoid (ℕ, 0, +) whose
API "conceptually" only provides the operation `tick`, which simply adds `1` to
the output. `Tick` also has instances for `LessDefined` and `Bottom`, the latter
mainly for convenience; e.g., it allows using `bottom` to abort an absurd case
of a demand function.

#### Properties of demand semantics

The shallowly-embedded Rocq demand semantics discussed thus far is much broader
than the fairly minimal calculus presented in the paper. This is close to how we
imagine the demand semantics might be used in practice, but it does not admit
the study of metatheoretical properties. To that end, `DemandSemantics.v`
contains a deep embedding of the paper's calculus. The type `Good` essentially
represents the statements of Lemmas 3.4, 3.5, and 3.6; the proof is provided by
`Good_den`.

#### Correctness: Correspondence with Clairvoyant Semantics

Monadic clairvoyance semantics are formalized in `Core.v`. The clairvoyance
monad itself is called `M`. Pessimistic specifications are given by
`pessimistic` (also notated `u {{ r }}`, and optimistic specifications are given
by `optimistic` (also notated `u [[ r ]]`).

In `DemandSemantics.v`:
- the syntax is given by the inductive types `ty` and `tm`.
- the denotation of types is in an algebraic structure called `ApproxAlgebra`,
  and the denotation function is `den_ty`.
- the denotation functions of terms are `den_lens` for the demand semantics and
  `den_cv` for the clairvoyant semantics.
- the type `Good` gives the statements of Theorems 3.4, 3.5, 3.6; the proof is
  provided by `Good_den`.
- the type `Correct` gives the statements of Theorems 3.7, 3.8, and 3.8; the
  proof is provided by `Correct_den`.

### Case studies: sorting algorithms

- `takeD` and related lemmas are defined in `List.v`.
- The insertion sort theory is developed in `InsertionSort.v`
- The selection sort theory is developed in `SelectionSort.v`

### The banker's queue and the reverse physicist's method

The correctness of the reverse physicist's method is proved in `Interfaces.v`.
In order to apply it to a data structure `T`, the following steps are necessary.

- Define a type `op` that represents the algebra of operations on `T`.
- Define an instance of `Eval`; i.e., a function `eval` that applies an `op` to
  a list of arguments.
- Define an instance of `Budget`; i.e., a function that computes the *amortized*
  cost of evaluating a given `op` on a given argument list.
- Define an instance of `Exec`; i.e., a function `exec` that applies an `op` to
  a list of arguments *in the clairvoyance monad*.
- Define an instance of `WellFormed`; i.e., a predicate `well_formed` that
  indicates whether a given element of `T` is valid. This is necessary in case
  `T` upholds some invariant that its type does not capture.
- Define an instance of `WfEval`; i.e., a lemma demonstrating that `eval`
  preserves the `well_formed` property.
- Define an instance of `IsApproxAlgebra`.
- Define an instance of `WellDefinedExec`; i.e., a lemma showing that `exec` is
  monotonic with respect to `less_defined`.
- Define an instance of `Demand`; i.e., a function `demand` that, given an `op`,
  a list of arguments, and an output demand, computes an input demand.
- Define an instance of `PureDemand`; i.e., a lemma showing that `demand` is
  functionally correct with respect to `eval`.
- Define an instance of `CvDemand`; i.e., a lemma showing that `demand` is
  cost-equivalent to `exec`.
- Define an instance of `Potential`; i.e., a function `potential` that computes
  the potential of a demand.
- Define an instance of `WellDefinedPotential`. This consists of two technical
  sub-lemmas: that `lub` is *sub-additive* with respect to `potential`—i.e., the
  potential of `lub x y` is no greater than the sum of the potentials of `x` and
  `y`—and that the potential of any bottom element ⊥ₐ is zero.
- Define an instance of `Physicist'sArgumentD`. This is theorem showing that the
  premises of the reverse physicist's method hold; i.e., that the
  demand-semantics cost of executing an operation is always less than the
  difference in potential plus the amortized cost.
- Apply `physicist's_method`, proving that the cost of executing any trace (of
  `op`s) is always less than its total budget.

The banker's queue theory is developed in `BankersQueue.v` and
`QueueInterfaces.v`; the implicit queue theory is developed in
`ImplicitQueue.v`. Both developments apply the reverse physicist's argument via
the above procedure.

## Major proof terms

- Demand semantics metatheory (`DemandSemantics.v`):
  + Properties of approximations: `Lemma_3_1`, `Lemma_3_2`, `Lemma_3_3`.
  + Totality, monotonicity, and ⊔-homomorphism: `Good_den`
  + Correctness with respect to clairvoyance semantics: `Correct_den`
- Selection sort (`SelectionSort.v`):
  + Cost: `selection_sortD_cost`
  + Cost when composed with `take`: `take_selection_sortD_cost`
- Insertion sort (`InsertionSort.v`):
  + Functional correctness: `insertion_sortD__approx`
  + Cost: `insertion_sortD_cost`
  + Cost when composed with `take`: `take_insertion_sortD_cost`
- Banker's queue:
  + Functional correctness (`BankersQueue.v`):
    * `mkQueueD_approx`
    * `pushD_approx`
    * `popD_approx`
  + Equivalence with clairvoyance semantics (`BankersQueue.v`):
    * `mkQueueD_spec`
    * `pushD_spec`
    * `popD_spec`
  + Amortized cost and persistence (`QueueInterface.v`): `amortized_cost`
- Implicit queue (`ImplicitQueue.v`):
  + Functional correctness:
    * `emptyD_approx`
    * `pushD_apporox`
    * `popD_approx`
  + Equivalence with clairvoyance semantics:
    * `emptyD_spec`
    * `pushD_spec`
    * `popD_spec`
  + Amortized cost and persistence: `amortized_cost`

## QEMU Instructions

QEMU is a hosted virtual machine monitor that can emulate a host processor
via dynamic binary translation. On common host platforms QEMU can also use
a host provided virtualization layer, which is faster than dynamic binary
translation.

QEMU homepage: https://www.qemu.org/

### Installation

#### OSX
``brew install qemu``

#### Debian and Ubuntu Linux
``apt-get install qemu-kvm``

On x86 laptops and server machines you may need to enable the
"Intel Virtualization Technology" setting in your BIOS, as some manufacturers
leave this disabled by default. See Debugging.md for details.


#### Arch Linux

``pacman -Sy qemu``

See the [Arch wiki](https://wiki.archlinux.org/title/QEMU) for more info.

See Debugging.md if you have problems logging into the artifact via SSH.


#### Windows 10

Download and install QEMU via the links at

https://www.qemu.org/download/#windows.

Ensure that `qemu-system-x86_64.exe` is in your path.

Start Bar -> Search -> "Windows Features"
          -> enable "Hyper-V" and "Windows Hypervisor Platform".

Restart your computer.

#### Windows 8

See Debugging.md for Windows 8 install instructions.

### Startup

The base artifact provides a `start.sh` script to start the VM on unix-like
systems and `start.bat` for Windows. Running this script will open a graphical
console on the host machine, and create a virtualized network interface.
On Linux you may need to run with `sudo` to start the VM. If the VM does not
start then check `Debugging.md`

Once the VM has started you can login to the guest system from the host.
Whenever you are asked for a password, the answer is `password`. The default
username is `artifact`.

```
$ ssh -p 5555 artifact@localhost
```

You can also copy files to and from the host using scp.

```
$ scp -P 5555 artifact@localhost:somefile .
```

### Shutdown

To shutdown the guest system cleanly, login to it via ssh and use

```
$ sudo shutdown now
```
