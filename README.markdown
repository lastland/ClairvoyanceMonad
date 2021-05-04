This repo contains the Coq formalization of the paper [Reasoning about the
garden of forking paths](https://arxiv.org/abs/2103.07543).

We have some comments to guide you through the code and we are working on
cleaner code and better documentation.

## Files

[Clairvoyance.v](Clairvoyance.v) contains the definitions of the clairvoyance
monad presented in Section 3 of the paper, the definitions and theorems related
to formal reasoning in Section 5, and the case studies in Section 6.

[Translation.v](Translation.v) contains the formalization of the mechanical
translation, the proof of the soundness theorem, and the proof of adequacy
theorem presented in Section 4.

## Axioms

The proofs in [Translation.v](Translation.v) rely on axioms for functional and
propositional extensionality.

## Dependencies

The code requires the [Equations
library](https://github.com/mattam82/Coq-Equations). To install via OPAM:

```
opam repo add coq-released https://coq.inria.fr/opam/released
opam install coq-equations
```

The code works with Coq versions 8.10.2, 8.11.2, 8.12.2, and 8.13.2.
