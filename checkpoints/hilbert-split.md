# Hilbert/principal split bridge checkpoint

Owned module: `QuadraticMoat/HilbertSplit.lean`.

Kernel-checked source translates two distinct principal prime ideals of norm p
whose product is the rational p ideal into `Nonempty (SplitPrime K p)`
and back. It also translates CFT's principal fractional-ideal range
predicate for a finite prime into native `v.asIdeal.IsPrincipal`.

Status: the native section through `finitePrime_fractionalPrincipal_iff_isPrincipal`
was kernel-checked by `./lakew build QuadraticMoat.HilbertSplit`, exit 0,
3571 jobs (5.9s). The final CFT compositions and exact multiplicity formula
are now drafted in the source but NOT YET CHECKED. The full CFT splitting
theorem dependency is still building in the parent task.

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

Still required: compile and audit the drafted final CFT compositions,
`smallHilbert_primeNormMultiplicity_real_off_discriminant`, and the explicit
finite exceptional set `discriminantDivisors K`. The native K algebra and
discriminant bridge is completed, without UFD-of-elements or unproved
arithmetic hypotheses.
