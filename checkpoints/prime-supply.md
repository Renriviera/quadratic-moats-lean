# Principal-split prime supply audit (2026-10-06)

Status: analytic helper module `QuadraticMoat/PrimeSupply.lean` written; build and axiom audit pending. No principal-split instantiation is proved yet. No assertion that Dirichlet density implies the required exponential-window mass.

## Precise original analytic input

Original `OAI/NumberTheory/GaussianMoat/PrimeMass.lean` proves
`PrimeLogMass.eventually_prime_window_mass`: for a unit residue class `a mod q`,
there is `c>0` and eventually

`c X ≤ ∑ n ∈ (windowIndices X).filter Nat.Prime, residueClass a n / n`.

At primes the residue class of von Mangoldt is `log p` or zero. The window is
`exp(1001/1000 * X) ≤ n ≤ exp(10499/10000 * X)`.
The proof only needs summability at exponents `s>1`, nonnegativity, and Laplace
moments `∑ a(n)/n^(1+j/X) / X → δ/j` for every `j>0` with `δ>0`.
It uses the existing degree-4000 polynomial concentrated between `7/20` and
`11/30` in the variable `exp(-log n/X)`. The general sequence version is
`QuadraticMoat.eventually_window_mass_of_moments`.

A natural-density/PNT counting theorem is stronger than necessary here. The
TeX proof currently uses `[T,2T]` prime batch asymptotics, while the original
Lean scaffold uses exponential windows and Laplace moments. These are distinct
interfaces: adopting the weaker route requires retaining/porting the scaffold
window design rather than claiming the TeX `[T,2T]` asymptotic was formalized.

## Why exported Chebotarev is insufficient

AINTLIB pin `160e446617a2168c34c95bbe7a76c4105b392434` exports
`Chebotarev.density_split_completely` in
`CebotarevDensity/Main.lean`. `HasDirichletDensity` is a limit of ratios of
unweighted prime-ideal series, not natural density.

Its public analytic helpers in `CebotarevDensity/DirichletDensity.lean`
provide only bounded errors:

- `logDedekindZeta_sub_primeIdealZetaSum_bounded`;
- `logDedekindZeta_sub_log_inv_sub_one_bounded`;
- `primeIdealZetaSum_univ_tendsto_log`.

A ratio asymptotic `P(s)/log(1/(s-1)) → δ` does not determine fixed-ratio
Laplace differences or narrow exponential-window mass: the two divergent
terms can have errors that fail to cancel. Even an `O(1)` regularized error
is insufficient for the exact moment limit. An actual finite regularized
limit is a sufficient strengthening.

## Rigorous route requiring no full Chebotarev theorem

Choose the **small/ordinary** Hilbert class field `H/K`. For quadratic `K`,
put `d=[H:K]`, `m=[H:ℚ]=2d`, and `δ=1/m`.

1. Mathlib's Dedekind zeta simple-pole theorem gives
   `(s-1) ζ_H(s) → r_H > 0` as `s ↓ 1`.
   Therefore `log ζ_H(s) − log(1/(s-1)) → log r_H`.
   This first strengthening is included as
   `QuadraticMoat.log_dedekindZeta_regularized_limit`.

2. Upgrade the Euler-log tail from boundedness to convergence:
   `R_H(s)=∑_𝔮[-log(1-N𝔮^(-s))-N𝔮^(-s)] → R_H(1)`.
   For `s≥1`, each summand is nonnegative and bounded by `2/N𝔮²`.
   The dominating sum is summable at exponent 2. Each summand is continuous
   at 1 because `N𝔮≥2`. Use
   `tendsto_tsum_of_dominated_convergence` from
   `Mathlib.Analysis.Normed.Group.Tannery`.
   Existing AINTLIB Euler product theorem:
   `NumberField.dedekindZeta_eq_tprod_primeIdeal` (namespace must be checked
   when imported; downloaded `/tmp/quadratic-chebotarev-euler.lean`).
   Existing logarithmic Euler identity is private, so either reprove/export
   it or put the convergence lemma in the source namespace/module. This is
   not a direct available theorem today.

3. Thus full unweighted prime-ideal sum satisfies
   `Q_H(s) − log(1/(s-1)) → log r_H − R_H(1)`.

4. Separate prime ideals of absolute residue degree at least two. Their
   series converges at `s=1`: each norm is `p^f`, `f≥2`, and there are at most
   `m` primes above each rational p. Dominate by `m ∑_p p^-2` and use Tannery.
   Ramified rational primes form a finite set and also yield a convergent
   finite contribution.

5. For every rational p unramified in K, prime ideals of H of norm p exist
   precisely when p is split into principal primes of K. Their multiplicity
   is exactly `m=2d`:
   - a norm-p prime of H contracts to a norm-p prime of K;
   - relative inertia degree in H/K is one, hence (Galois and unramified)
     all primes over the contraction have e=f=1;
   - CFT splitting/principal iff makes that K prime principal;
   - quadratic conjugation makes the other K prime principal;
   - a principal split p has two K primes, with d degree-one H primes above
     each.
   This avoids a separate proof that H/ℚ is Galois. H/K Galois is already
   an instance of `FiniteAbelianExtension K`.

6. Let `P(s)=∑_{principal split p} p^-s`. Then
   `P(s) − δ log(1/(s-1)) → B` for a finite B.

7. Extract weighted moments by elementary secant inequalities, without
   termwise differentiation. For `j>0`, `0<ε<j`, put
   `M_j(X)=∑_{principal split p} log p / p^(1+j/X) / X`.
   For positive X:

   `[P(1+j/X)-P(1+(j+ε)/X)]/ε ≤ M_j(X)`
   `M_j(X) ≤ [P(1+(j-ε)/X)-P(1+j/X)]/ε`.

   These follow termwise from `1-exp(-u) ≤ u ≤ exp(u)-1` for `u≥0`
   and summable-series order. The regularized limit gives limiting secants
   `δ log((j+ε)/j)/ε` and `δ log(j/(j-ε))/ε`. Both tend to `δ/j`
   as `ε ↓ 0`. An epsilon squeeze proves `M_j(X) → δ/j`.
   This helper remains unformalized; no existing exact theorem was found.

8. For `a(n)=if principalSplit n then log n else 0`, summability at s>1
   follows by domination with all naturals. Useful exact mathlib lemma:
   `Real.log_natCast_le_rpow_div n hε` (take ε=(s-1)/2), plus real p-series
   summability. Nonnegativity is immediate because principalSplit implies
   n prime, hence n≥2. Instantiate the checked generic window lemma.

## Exact CFT APIs confirmed in source

ClassFieldTheory pin `2eb22d6485af45f29c5219de6c49f196a61c4f49` (files are under
`Lean4/ClassFieldTheory/` in its repository):

- `ClassFieldTheory.exists_smallHilbertClassField (K : Type) [Field K] [NumberField K] :
  ∃ E : FiniteAbelianExtension K, IsSmallHilbertClassField E`;
- `ClassFieldTheory.smallHilbertClassField_degree_eq_classNumber K E hE :
  Module.finrank K E = NumberField.classNumber K` (optional for δ>0);
- `ClassFieldTheory.finitePrime_splitsCompletelyInSmallHilbertClassField_iff_principal
  K E hE (v : HeightOneSpectrum (𝓞 K)) :
  FinitePrimeSplitsCompletely K E v ↔
  finitePrimeFractionalIdeal v ∈ (toPrincipalIdeal (𝓞 K) K).range`.

`FiniteAbelianExtension` packages a finite-dimensional abelian Galois
intermediate field in `SeparableClosure K`. It provides NumberField, Algebra,
FiniteDimensional and IsAbelianGalois instances.

`FinitePrimeSplitsCompletely K E v` literally says every prime above v has
`ramificationIdx (𝓞 K)=1` and `inertiaDeg (𝓞 K)=1`.
`IsSmallHilbertClassField` means **everywhere** unramified and maximal among
finite abelian everywhere-unramified extensions. This is the correct ordinary
Hilbert field; use the small field for real quadratic K (no positivity
condition on generators).

Downloaded only the tree listing (655 KB) and eight small source files
(about 54 KB total) to `/tmp`. No dependency/lakefile edits or huge repositories
were downloaded. These source reads do not establish a transitive axiom audit
or version compatibility; the parent must build pinned CFT imports and audit
endpoint theorem axioms after integration.

## Useful mathlib arithmetic APIs, names verified in current pin

- `Ideal.absNorm_pow_inertiaDeg` (preferred, see deprecated wrappers in
  `NumberTheory/RamificationInertia/Inertia.lean`);
- `Ideal.absNorm_eq_pow_inertiaDeg'` for natural rational primes;
- `Ideal.sum_ramification_inertia`;
- `Ideal.card_primesOverFinset_le_finrank`;
- `Ideal.inertiaDeg_eq_of_isGaloisGroup`;
- `Ideal.ramificationIdx_eq_of_isGaloisGroup`;
- `Ideal.ncard_primesOver_mul_ramificationIdxIn_mul_inertiaDegIn`;
- `Ideal.inertiaDegIn_mul_inertiaDegIn`.

The necessary arithmetic bridges include conversion between the CFT
fractional-principal condition and an integral principal ideal/generator,
quadratic split-prime classification and conjugation, rational-prime fiber
indexing, and correct cardinalities. These are genuine proofs, not typeclass
inference alone.

## Verification commands

`./lakew build QuadraticMoat.PrimeSupply` was started after mathlib cache
availability. The final build result and axiom output will be appended below.
