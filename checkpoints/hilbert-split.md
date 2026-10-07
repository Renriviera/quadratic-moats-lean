# Hilbert/principal split bridge checkpoint

Owned module: `QuadraticMoat/HilbertSplit.lean`.

Kernel-checked source translates two distinct principal prime ideals of norm p
whose product is the rational p ideal into `Nonempty (SplitPrime K p)`
and back. It also translates CFT's principal fractional-ideal range
predicate for a finite prime into native `v.asIdeal.IsPrincipal`.

Status: ALL SOURCE KERNEL-CHECKED. Final command
`./lakew build QuadraticMoat.HilbertSplit QuadraticMoat.DyadicSieve`, exit 0,
9949 jobs; HilbertSplit compiled in 5.3s. The full CFT splitting theorem
dependency built successfully (5258 jobs) before this check.

Additional checked arithmetic bridge:

- `squarefree_natPrime_ideal_of_not_dvd_discr` proves rational p's ideal
  squarefree from p not dividing `NumberField.discr K`. It uses normalized
  factors of ideals and the native discriminant/unramified equivalence.
- `splitPrime_of_norm_prime_of_squarefree` constructs the conjugate second
  factor from one norm-p element and quadraticity; squarefree rational ideal
  forces the two prime ideals distinct and hence coprime.
- `splitPrime_iff_exists_principal_prime_norm` expresses package existence,
  away from discriminant, as existence of one principal norm-p K prime ideal.
- `prime_norm_isPrincipal_of_splitPrime` gives principality of every norm-p
  prime ideal, and `card_prime_norm_fiber_of_splitPrime` counts exactly two.
- `prime_norm_under_and_inertiaDeg` proves absolute prime norm descends to
  prime norm in K and relative inertia degree one.
- `prime_norm_splits_completely_of_unramified` upgrades the one inertia-degree
  equality to complete splitting in a finitely unramified Galois extension.

Also checked: `card_heightPrimesOver_of_splitsCompletely` and
`card_prime_norm_fiber_mul_relative_degree` count prime norm fibers by
relative field degree. These avoid needing H/ℚ Galois.

Final checked CFT endpoints:

- `smallHilbert_splitPrime_of_prime_norm`: one norm-p prime of a small
  Hilbert class field gives a native SplitPrime package in quadratic K,
  for p prime and not dividing discr K.
- `smallHilbert_prime_norm_height_fiber_card`: exactly [E:ℚ] primes of
  absolute norm p if a package exists, and zero otherwise.
- `smallHilbert_primeNormMultiplicity`: the same count in prime_supply's
  native PrimeNormIdeal presentation.
- `smallHilbert_primeNormMultiplicity_real_off_discriminant`: all natural
  n outside the explicit finite set `discriminantDivisors K` satisfy
  multiplicity = [E:ℚ] times indicator of Nonempty(SplitPrime K n).

Hypotheses: K a number field of degree two; E an actual
ClassFieldTheory.FiniteAbelianExtension K with IsSmallHilbertClassField E.
There are no class-number-one, element-UFD, geometric, or prime supply
hypotheses. Hilbert class-field existence is supplied by the dependency and
instantiated in prime_supply's PrincipalPrimeFamily module.

Audit: `./lakew env lean /private/tmp/quadratic-hilbert-complete-audit.lean`,
exit 0. All ten listed endpoints use only propext, Classical.choice,
Quot.sound, including the full CFT dependency chain. No sorry/admit/custom
axiom appears in this module. All assigned HilbertSplit work is complete.
