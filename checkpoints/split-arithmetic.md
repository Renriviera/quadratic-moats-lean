# Principal split arithmetic checkpoint

Owned module: `QuadraticMoat/SplitArithmetic.lean`.

Completed source defines the native absolute integer norm
as a monoid hom, residue quotient cardinality, primality from prime norm,
and `SplitPrime K p` with two factors of absolute norm p, element
coprimality, and product associated to rational p. Further lemmas cover
factor divisibility of rational integers, factors over different primes,
basis-coordinate primitivity, and finite product norm bounds.

Status: KERNEL-CHECKED with Lean 4.34.1 and pinned mathlib
`d13f23b723b8a846827a245b89c10fc7d3f11612`.

Checked command, exit 0:

```
./lakew build QuadraticMoat.SplitArithmetic
```

Final output: `Built QuadraticMoat.SplitArithmetic (3.7s)` and
`Build completed successfully (2122 jobs)`.

Axiom audit, exit 0:

```
./lakew env lean /private/tmp/quadratic-split-arithmetic-audit.lean
```

All ten audited endpoints (nonzero norm, divisor bound, norm-one/unit,
quotient cardinality, primality, factor primality, rational divisibility,
cross-prime coprimality, primitive-factor exclusion, finite prime product
bound) use only `[propext, Classical.choice, Quot.sound]`. No `sorryAx` or
additional mathematical axiom occurs.

Stable API and hypotheses:

- `integerAbsNorm K : (𝓞 K) →* ℕ` equals `(Algebra.norm ℤ a).natAbs`.
  Theorems establish multiplicativity, nonzero positivity, norm divisibility
  and divisor bounds, integer-cast formula, rational absolute-field-norm
  identification, norm-one iff unit, and arbitrary finite product bounds.
- `residue_card_eq_integerAbsNorm a` identifies the cardinality of the
  quotient by the principal ideal, and `prime_of_integerAbsNorm_prime`
  obtains native element primality using the requested ideal-norm API.
- `SplitPrime K p` packages only direct algebra data: `p.Prime`,
  `factor : Fin 2 → 𝓞 K`, both absolute norms p, factor coprimality, and
  product associated to rational p.
- `SplitPrime.factor_dvd_intCast_iff` proves a factor divides `(a : 𝓞 K)`
  iff `(p : ℤ) ∣ a`. It needs no extra degree hypothesis: prime divisibility
  of an integer norm power implies divisibility of the base.
- `SplitPrime.factors_coprime` proves factors over different rational primes
  coprime by mapping integer Bezout coefficients.
- `CoordinatePrimitive b v` means the two basis coordinates are coprime.
  `SplitPrime.not_both_dvd_coordinatePrimitive` excludes simultaneous
  divisibility by both factors, using that their product is associated to p.
- `splitPrime_finset_product_le_integerAbsNorm s P choice hv hd` states
  `∏ p ∈ s, p ≤ integerAbsNorm K v`, for selected packages `P` indexed by
  `p : s`, chosen factors all dividing nonzero v.

No UFD-of-elements or geometric assumptions. Supply/existence of splitting
packages is deliberately separate and still needed by global integration.
