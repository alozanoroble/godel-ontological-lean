# Gödel's ontological argument in Lean 4

A machine-checked formalization of Gödel's ontological argument and the three
emendations of it, with an explicit record of what each result depends on.

**No Mathlib, no external dependencies.** 371 lines of code, builds in about
three seconds.

- **Interactive explorer:** https://alozanoroble.github.io/godel-ontological-lean/
- **Paper:** [`paper/godel-ontological.pdf`](paper/godel-ontological.pdf)
- **Axiom certificate:** [`certificate.txt`](certificate.txt)

## What is here

Five systems. In each, the axioms are *hypotheses* of the theorems that use
them rather than global postulates, so every theorem is a conditional and
`#print axioms` reports only Lean's own three.

| System | Result | Axioms used for T3 | Frame condition | Modal collapse |
|---|---|---|---|---|
| **Gödel 1970** | axioms are **inconsistent** | — | none (`K`) | — |
| **Scott 1987** | `□∃x G(x)` | all | symmetry (`B`) | **yes** |
| **Anderson 1990** | `□∃x G(x)` | all | refl + trans + symm (`S5`) | no |
| **Fitting 2002** | `□∃x G(x)` | all | none (`K`) | no |
| **Hájek 2002 (AOE)** | `□∃x G(x)` | **2 of 4** | symmetry (`B`) | no |

Gödel's own axioms fail because his definition of essence omits the conjunct
`φ(x)`. The empty property is therefore vacuously an essence of every
individual, and Axiom 5 then demands that it be necessarily instantiated. Scott
restores the conjunct, and the argument works — at the cost of modal collapse,
which read as a condition on the frame forces the accessibility relation to be
*equality*. Anderson, Fitting and Hájek each escape the collapse by a different
route.

Every model and countermodel in the development is an explicit, constructive
proof term rather than the output of a model finder — including a one-world
structure that refutes Gödel's Axiom 5 and satisfies Scott's, which is the
sharpest available statement of what the missing conjunct costs.

## Building

The Lean development is a standalone Lake project with no dependencies:

```bash
cd lean
lake build                          # ~3 seconds
lake env lean Certificate.lean      # reproduces certificate.txt
```

Pinned to `leanprover/lean4:v4.34.0` by `lean/lean-toolchain`.

## Layout

```
index.html                   the interactive explorer
lean/Godel/Modal.lean        shallow embedding of quantified modal logic
lean/Godel/Original.lean     Gödel 1970 — the refutation
lean/Godel/Scott.lean        Scott 1987 — T2, T3, modal collapse, frame theorems
lean/Godel/Anderson.lean     Anderson 1990
lean/Godel/Fitting.lean      Fitting 2002
lean/Godel/Hajek.lean        Hájek 2002 (AOE)
lean/Godel/Sanity.lean       the models and countermodels
lean/Certificate.lean        the #print axioms dump
paper/                       the write-up, LaTeX and PDF
```

## What this is not

Not a research contribution. The mathematics is due to Gödel, Scott, Sobel,
Anderson, Fitting and Hájek, and to Christoph Benzmüller and collaborators, who
discovered the inconsistency with automated provers in 2013 and mechanised all
of this in Isabelle/HOL first. This is an independent corroboration in a
different foundation, with no automation: it checks arguments, it does not find
them. Full attribution is in the paper.

## References

- C. Benzmüller and B. Woltzenlogel Paleo, *The inconsistency in Gödel's
  ontological argument*, IJCAI-16, 936–942.
- C. Benzmüller and D. Fuenmayor, *Computer-supported analysis of positive
  properties, ultrafilters and modal collapse*, Bull. Sect. Logic 49 (2020).
- C. Benzmüller, L. Weber and B. Woltzenlogel Paleo, *Computer-assisted analysis
  of the Anderson–Hájek ontological controversy*, Logica Universalis 11 (2017).
- D. Fuenmayor and C. Benzmüller, *Types, tableaus and Gödel's God in
  Isabelle/HOL*, Archive of Formal Proofs (2017).
