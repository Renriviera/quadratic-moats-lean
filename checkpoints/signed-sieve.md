# Native signed sieve checkpoint — built and audited

Assigned modules: `QuadraticMoat/SignedSieve.lean` and `QuadraticMoat/SignedGeometry.lean`.

`SplitSieve K` stores a finite set of rational primes and a `SplitPrime K p` packet for each prime. Each packet supplies two coprime principal factors of absolute integer norm p. No Gaussian congruence class, unique factorization, or multiplicative coordinate equivalence is assumed.

## Checked arithmetic

- Signed factors, signed products, and the integer period, with `signedProduct_norm = period` and nonzero products.
- Products of selected factors divide a common witness; their norm products bound its absolute integer norm.
- Primitive coordinate lines consist of integer multiples of their primitive direction. A prime cannot have both factors dividing a primitive direction.
- `line_witness_norm_lower`: the primitive direction norm times the square of the ineligible-prime product bounds the witness norm. Rank two is derived from the supplied integral basis.
- `lineLog_mean`: the signed line log mean is at most half the primitive direction log norm.
- `lineLog_tail`: the line Hoeffding tail estimate, using the original generic sign probability theorem.
- `selectedFactors`, `avoiding`, and `avoiding_periodic` bridge to the native periodicity/component reduction.

## Checked geometry and concentration

- `near_witnesses_collinear`: nearby sign choices have collinear witnesses, because the common signed factor divides their integer basis determinant and its norm exceeds the determinant bound.
- Native witness-line classes and sign distance separation feed the original generic cube concentration estimate.
- `signed_region_bound` and `signed_region_exp_bound` prove the signed witness event bounds.
- Scaled-coordinate rectangles have absolute integer norm at most `2*R^2` and absolute basis determinant at most `2*R*W`.
- `signed_rectangle` has the original constants: primes in `[T,2*T]`, `T≥5`, `1≤W≤R`, `0<d<1/4`, `R*W≤period^(1-d)`, and `1000≤d^3*card` imply event measure at most `exp(-d^3*card/5120)`.
- `signed_rectangle_of_planarContext` supplies scale and norm domination from the proved planar context.

These are proved signed estimates, not assumptions. The explicit-basis version requires `scale≥1` and the elementary integer norm domination inequality; the context wrapper obtains these as context fields. The parent constructs the context unconditionally for degree-two fields. The remaining integration is the analytic sieve/entropy/no-infinite-avoiding-walk argument and enough principal split-prime packets.

## Successful checks

From the Lean project root:

```
./lakew build QuadraticMoat.SignedSieve QuadraticMoat.SignedGeometry
```

Exit 0, 8945 jobs. Both owned modules have no warnings. Replayed PlanarContext has a class-definition reducibility warning, and Lake reports the parent's dependency compatibility patches as local changes.

```
./lakew env lean --stdin <<'LEAN'
import QuadraticMoat.SignedGeometry
#print axioms QuadraticMoat.SplitSieve.line_witness_norm_lower
#print axioms QuadraticMoat.SplitSieve.lineLog_mean
#print axioms QuadraticMoat.SplitSieve.lineLog_tail
#print axioms QuadraticMoat.SplitSieve.near_witnesses_collinear
#print axioms QuadraticMoat.SplitSieve.signed_region_exp_bound
#print axioms QuadraticMoat.SplitSieve.signed_rectangle
#print axioms QuadraticMoat.SplitSieve.signed_rectangle_of_planarContext
#print axioms QuadraticMoat.SplitSieve.avoiding_periodic
#print axioms QuadraticMoat.SplitSieve.signedProduct_norm
LEAN
```

Exit 0. Every result depends only on `[propext, Classical.choice, Quot.sound]`. A source search finds no `sorry`, `admit`, or new `axiom` in either module.
