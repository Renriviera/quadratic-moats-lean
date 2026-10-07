# Native dyadic sieve checkpoint

Owned module: QuadraticMoat/DyadicSieve.lean.

Kernel-checked with `./lakew build QuadraticMoat.DyadicSieve`, exit 0,
8974 jobs, module compiled in 3.9s.

`PrimeFamily.dyadicSieve F hgood j` chooses actual SplitPrime packets for
the supplied family's dyadicBatch j. hgood states every good prime has a
native packet. The resulting arithmetic sieve contains the batch exactly.

Original-port convenience APIs: dyadic_prime_bounds, dyadic_dense_nonempty,
dyadic_mean_bounds, dyadicSieve_available_weight (all prefix F,hgood).
The finite factor set is the native s.selectedFactors.

Additional generic native residue APIs: residueWeight monotonicity and
nonnegativity, residue_vector_entropy, residue_finset_entropy, and
selectedFactors_ne_zero/selectedFactors_weight. These use native ring
quotients of O_K, with card equal to integerAbsNorm. No PlanarContext
hypothesis is needed for these entropy bounds or the dyadic APIs.

Audit command `./lakew env lean /private/tmp/quadratic-dyadic-sieve-audit.lean`
exited zero. All eight audited definitions/theorems use only propext,
Classical.choice, Quot.sound.
