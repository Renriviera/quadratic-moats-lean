# Unconditional quadratic principal-split supply

`QuadraticMoat/PrincipalPrimeFamily.lean` is built and audited. The only field
hypotheses are `Field K`, `NumberField K`, and `Module.finrank ℚ K = 2`.

The module chooses a small Hilbert class field internally using native
`ClassFieldTheory.exists_smallHilbertClassField`. The checked arithmetic count
`HilbertSplit.smallHilbert_primeNormMultiplicity_real_off_discriminant` gives
its degree-one prime-norm multiplicity as `[E:ℚ]` times the principal-split
rational-prime indicator outside the finite set `discriminantDivisors K`.
No assumption about `E/ℚ` being Galois is used.

Exports:

* `principalSplitCoefficient K p : ℝ`, the indicator of
  `Nonempty (SplitPrime K p)`;
* `principalSplit_regularized_limit K hdegree`: summability for all real
  exponents greater than one and a finite regularized limit, with some
  positive pole coefficient (inverse absolute degree of the chosen Hilbert
  extension);
* `principalSplit_window_mass K hdegree`: positive logarithmic prime mass in
  exactly the original `windowIndices` exponential interval;
* `principalSplitPrimeFamily K hdegree : PrimeFamily`, whose good predicate
  is definitionally `Nonempty (SplitPrime K p)`.

Commands:

```sh
./lakew build QuadraticMoat.PrincipalPrimeFamily QuadraticMoat.PlaneBallCard
./lakew env lean logs/principal-prime-family-axioms.lean
```

Build exited 0 (9947 jobs). Headline regularization, window mass, and native
family audit use only `propext`, `Classical.choice`, `Quot.sound`.
Logs are `logs/principal-prime-family-{build,axioms}.txt`.

The generic `QuadraticMoat/SeparatedParameters.lean` also builds and audits
(`logs/separated-parameters-{build,axioms}.txt`). Its theorem
`PrimeFamily.exists_separated_parameters F` chooses `a δ t K` with all original
scalar gap/cost guards and eventual separated dense supplied batches.
It reuses original scalar `topCoefficient`, block and enumeration functions.

`QuadraticMoat/PlaneBallCard.lean` proves the native auxiliary planar lattice's
disk bound `card (planeBall R) ≤ 36*R²` for `R ≥ 1`, by its injective integer
coordinate map into the original Gaussian integer disk. The field's scale is
at least one, so the original cardinal bound is valid.

The prime-supply bridge is complete. The full quadratic moat theorem still
requires the native entropy/sieve-certificate chain and final graph
integration; no claim of final completion is made here.
