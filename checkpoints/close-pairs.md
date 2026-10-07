# Close-pair algebra checkpoint

Owned module: `QuadraticMoat/ClosePairs.lean`.

The module proves the proposed algebraic statement using any field `K`
and automorphism `σ : K ≃+* K`, with `conjugateNorm σ x = x * σ x`.
Equal norm values at `x` and `x + 1` yield `x = y ∨ x = σ y` by factoring
a quadratic. Scaling handles arbitrary nonzero differences, and finite
unions yield finite norm-pairs for finite allowed norm and difference sets.

`exists_conjugation_norm` closes the arithmetic interface: every separable
quadratic field extension has two automorphisms; the Galois norm formula
therefore expresses the norm as `x * σ x`. The final native endpoints are
`finite_quadratic_fixed_norms`, `finite_quadratic_norm_pairs`,
`finite_numberField_norm_pairs`, and `finite_ringOfIntegers_norm_pairs`.

Status: KERNEL-CHECKED with Lean 4.34.1 and pinned mathlib
`d13f23b723b8a846827a245b89c10fc7d3f11612`.

Checked commands from project root:

```
./lakew env lean QuadraticMoat/ClosePairs.lean
./lakew build QuadraticMoat.ClosePairs
```

The final build after all additions exited 0 with
`Built QuadraticMoat.ClosePairs (1.8s)` and `Build completed successfully
(2088 jobs)`. Imports were narrowed to the necessary mathlib modules.

Exact final hypotheses: `[Field K] [NumberField K]`,
`Module.finrank ℚ K = 2`, a finite `S : Set ℚ` of signed field norm values,
and a finite `Δ : Set (𝓞 K)` of allowed differences. The conclusion is
finiteness of all ordered distinct pairs whose individual norms lie in S
and whose difference lies in Δ. No assumption on units, UFD, class number,
or a desired finiteness conclusion remains.

Remaining integration requirement: the moat argument must independently
produce finite norm values for its exceptional elements and finite allowed
differences from its Minkowski distance cutoff. Those inputs are not
proved by this purely algebraic module.

Axiom audit command, exit 0:

```
./lakew env lean /private/tmp/quadratic-close-pairs-audit.lean
```

The audit imported the built module and printed axioms for the algebraic
root theorem, fixed-norm finiteness, norm identification, and all native
norm endpoints. Every audited theorem depends only on
`[propext, Classical.choice, Quot.sound]`. No `sorryAx` or additional
mathematical axiom occurs.
