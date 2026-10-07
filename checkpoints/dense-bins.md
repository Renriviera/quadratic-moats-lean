# Generic supplied-prime dense bins

Module: `QuadraticMoat/DenseBins.lean`. Owner: supply agent.

The original Gaussian DenseBins argument is ported to any supplied rational
prime family. No congruence condition is present in the new statements.

## Stable interface

`QuadraticMoat.primeWindow good X` filters the original
`OAI.GaussianMoat.PrimeLogMass.windowIndices X` by `good`. Its real interval is
the original fixed window `[exp ((1001/1000)*X), exp ((10499/10000)*X)]`.

`QuadraticMoat.PrimeFamily` has fields:

* `good : ℕ → Prop`;
* `prime_of_good : ∀ p, good p → p.Prime`;
* `window_mass : ∃ c : ℝ, 0 < c ∧ ∀ᶠ X : ℝ in atTop,
    c*X ≤ ∑ p ∈ primeWindow good X, Real.log p/p`.

All subsequent names are in `QuadraticMoat.PrimeFamily`, with explicit family
argument `F` first. `dyadicBatch F j` filters the natural-number interval
`[2^j,2^(j+1))` by `p.Prime ∧ F.good p`. The redundant primality conjunct keeps
`mem_dyadicBatch` aligned with the original sieve tuple.

Headline theorems:

* `eventually_dense_split_bins F`: positive constants `c δ`, and eventually a
  set `J` of at least `c*X` bins; every `j ∈ J` satisfies
  `X ≤ j*log 2 ≤ (21/20)*X` and
  `δ*2^j/log(2^(j+1)) ≤ (dyadicBatch F j).card`.
* `eventually_separated_split_bins F K hK`, for `0 < K`: the same bounds plus
  `∀ i ∈ J, ∀ j ∈ J, i < j → i+K ≤ j`.

Supporting APIs: `logBin_mem`, `dyadicMass`, `dyadicMass_nonneg`,
`dyadicMass_le`, `dyadicMass_le_card`, `many_dense_bins`, `splitWindow`,
`windowBins`, `splitWindow_eq_primeWindow`, `window_mass_le_bins`,
`windowBin_bounds`, and `windowBins_card`.

The density proof uses only the prime-family mass field, original scalar
Chebyshev estimate `prime_log_mass_le_theta`, and elementary finite sums.
The spacing proof reuses original generic `OAI.GaussianMoat.thin_bins` through
the `BatchCertificate` import. Original source attribution remains in the
imported OAI modules; the mathematical argument and numerical constants here
are the original Gaussian DenseBins argument with arithmetic abstracted.

## Verification

Commands completed successfully:

```sh
./lakew build QuadraticMoat.DenseBins
./lakew env lean logs/dense-bins-axioms.lean
```

Build log: `logs/dense-bins-build.txt` (8955 jobs, exit 0).
Audit: `logs/dense-bins-axioms.txt`; `dyadicMass_le`, `many_dense_bins`, and both
headline theorems depend only on `propext`, `Classical.choice`, `Quot.sound`.
The file has no `sorry`, `admit`, or mathematical axiom declaration.

## Remaining integration

Construct the native family `good p := Nonempty (QuadraticMoat.SplitPrime K p)`
using its prime field and the unconditional small-Hilbert norm-fiber count
formula. The supply modules already turn that finite-exception count formula
into the requisite window mass. This module deliberately has a generic
`PrimeFamily` parameter; it does not claim the arithmetic instantiation or the
final quadratic moat theorem is complete.
