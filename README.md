# Lean formalization of the Dinitz--Garg--Goemans counterexample

[![CI](https://github.com/Arthur742Ramos/dinitz-garg-goemans-counterexample-lean/actions/workflows/ci.yml/badge.svg)](https://github.com/Arthur742Ramos/dinitz-garg-goemans-counterexample-lean/actions/workflows/ci.yml)

This repository is a standalone Lean 4 and Mathlib formalization of the finite
counterexample recorded in the Isabelle/AFP entry
[A Formal Counterexample to the Cost-Preserving Single-Source Unsplittable
Flow Conjecture](https://isa-afp.org/entries/Dinitz_Garg_Goemans_Counterexample.html).

It models the seven-vertex, nine-arc directed instance with three terminal
demands. The checked certificate has a feasible fractional flow of cost `58`
and maximum demand `15`. Every unsplittable routing whose arc loads satisfy the
weak Dinitz--Garg--Goemans additive bound therefore has cost at least `60`.
Consequently, the cost-preserving conjecture is false, and the stronger strict
congestion variant is false as well.

The arithmetic is exact over `ℚ`. This is a faithful finite certificate for the
usual real-valued statement: all data and inequalities are rational, and the
same certificate embeds into `ℝ`. The project does not claim a general
algorithmic or complexity-theoretic result.

## Repository map

- `Challenge.lean` contains the auditable statement surface with deliberate
  proof holes.
- `Solution.lean` imports the completed proof development.
- `DinitzGargGoemans/Definitions.lean` defines the finite path-flow model and
  concrete graph.
- `DinitzGargGoemans/Proof.lean` proves the graph classification, flow
  certificate, cost gap, and conjecture refutations.
- `comparator.json` specifies the declarations checked by Palomar Comparator.
- `formalization.yaml` records provenance, authorship, scope, and review status.
- `docbuild/` is the pinned doc-gen4 project.

## Verification

The repository uses Lean 4 `v4.33.0` and Mathlib `v4.33.0`:

```text
lake exe cache get
lake build
(cd docbuild && lake build DinitzGargGoemans:docs)
ruby scripts/validate-formalization.rb
./scripts/verify-comparator.sh
```

The final solution contains no `sorry` proofs and declares no axioms beyond
the permitted Lean foundations checked by Comparator and NanoDa. The
deliberate `sorry` placeholders occur only in `Challenge.lean`.

## Attribution and submission

The Lean project authors are Arthur Freitas Ramos, David Barros Hulak, and Ruy
Jose Guerra Barretto de Queiroz, matching the authors of the AFP formalization.
The mathematical source material and its provenance are listed in
`formalization.yaml`; this repository reimplements the finite certificate and
does not import Isabelle source.

The project is prepared for the
[Palomar Registry](https://palomar-registry.org/). Submission uses the
[Palomar submission form](https://submit.palomar-registry.org/) and requires a
public repository, an exact immutable commit, and explicit maintainer
authorization.
