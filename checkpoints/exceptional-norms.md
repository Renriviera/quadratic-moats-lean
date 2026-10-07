# Exceptional norm values checkpoint

Owned module: `QuadraticMoat/ExceptionalNorms.lean`.

Task: derive finite signed rational norm values for all irreducibles
divisible by members of a finite set of selected nonunit elements, without
UFD or class-number-one hypotheses.

Completed source uses `Irreducible.dvd_iff` to associate each such
irreducible to its selected nonunit divisor. Applying the integer algebra
norm maps the unit factor to an integer unit, which is ±1. The existing
`Algebra.coe_norm_int` theorem transfers this to rational field norms.
The source also combines this with `finite_ringOfIntegers_norm_pairs`.

Status: KERNEL-CHECKED with Lean 4.34.1 / mathlib
`d13f23b723b8a846827a245b89c10fc7d3f11612`.

Checked build, exit 0:

```
./lakew build QuadraticMoat.ExceptionalNorms
```

Output: `Built QuadraticMoat.ExceptionalNorms (1.3s)` and
`Build completed successfully (2092 jobs)`.

Axiom audit, exit 0:

```
./lakew env lean /private/tmp/quadratic-exceptional-norms-audit.lean
```

Audit results: `associated_of_nonunit_dvd_irreducible` uses only `propext`;
`int_map_eq_or_neg_of_associated` uses `propext` and `Classical.choice`;
all native field norm and finite exceptional pair endpoints use only
`[propext, Classical.choice, Quot.sound]`. No `sorryAx` or additional
mathematical axiom occurs.

Stable API:

- `selectedNormValues (A : Set (𝓞 K)) : Set ℚ` is selected signed norms
  and their negatives.
- `finite_selectedNormValues A hA` proves finiteness for finite A.
- `irreducible_norm_mem_selectedNormValues A hp hd` needs only
  `Irreducible p` and `∃ a ∈ A, ¬ IsUnit a ∧ a ∣ p`.
- `finite_norm_image_exceptional_irreducibles A hA` proves the image of
  all such irreducibles under rational field norm is finite, for any
  number field.
- `finite_exceptional_irreducible_pairs hdegree A Δ hA hΔ` combines this
  with the close-pair result for degree-two number fields.

No remaining algebraic or norm interface hypotheses. The global moat
argument still needs its finite selected elements and finite bounded
differences from the independent sieve/lattice construction.
