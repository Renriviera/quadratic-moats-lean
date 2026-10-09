# Quadratic moat theorems in Lean

This project proves uniform bounds on connected components in two full Minkowski graphs over every number field of degree exactly two:

- The original graph of **all irreducible elements** of the ring of integers `𝓞 K`.
- The stronger bounded-support graph of **all nonzero elements whose principal ideals have at most `b` distinct prime-ideal factors**, for every natural-number budget `b`.

Both theorems cover real and imaginary quadratic fields, including non-UFD rings of integers. Vertices are actual elements: associates remain distinct. Edges join distinct vertices at full Minkowski Euclidean distance at most `D`; both real embeddings are included in the real quadratic case. Every real `D`, including zero and negative values, is allowed.

The original theorem remains available in `QuadraticMoat/Main.lean`, in namespace `QuadraticMoat`:

```lean
theorem irreducible_components_uniformly_bounded
    (K : Type) [Field K] [NumberField K]
    (hdegree : Module.finrank ℚ K = 2) (D : ℝ) :
    ∃ B : ℕ, ∀ a : IrreducibleVertex K,
      (component K D a).Finite ∧ (component K D a).ncard ≤ B
```

The new theorem is proved in `QuadraticMoat/BoundedFactors/Main.lean`, in namespace `QuadraticMoat.BoundedFactors`:

```lean
theorem bounded_distinct_factors_components_uniformly_bounded
    (K : Type) [Field K] [NumberField K]
    (hdegree : Module.finrank ℚ K = 2) (b : ℕ) (D : ℝ) :
    ∃ M : ℕ, ∀ α : Vertex K b,
      (component K b D α).Finite ∧ (component K b D α).ncard ≤ M
```

Here `Vertex K b` consists of elements `α ≠ 0` with `omega K α ≤ b`, where `omega` counts distinct prime ideals in the factorization of the principal ideal `(α)`. **Prime-ideal multiplicities are unrestricted. All units are included, even for `b = 0`; zero is explicitly excluded.** This is a bound on distinct ideal support, not on the total number of prime factors counted with multiplicity. The conclusion is qualitative: one finite cardinality bound exists for all components, depending on `K`, `b`, and `D`; no explicit numerical bound is provided.

Importing `QuadraticMoat` exports both results. The original API remains `QuadraticMoat.irreducible_components_uniformly_bounded`, `QuadraticMoat.uniformEndpoint_proved`, and `QuadraticMoat.allQuadraticEndpoint_proved`. The additional endpoints are `QuadraticMoat.BoundedFactors.bounded_distinct_factors_components_uniformly_bounded`, `QuadraticMoat.BoundedFactors.uniformEndpoint_proved`, and `QuadraticMoat.BoundedFactors.finiteHitNoWalkEndpoint_proved`. No UFD, class-number, prime-distribution, finite-unit, or auxiliary sieve assumption remains in the public component theorems.

## Verification

Lean is pinned to 4.34.1, with dependency revisions fixed in `lake-manifest.json`. For a fresh checkout, install Python 3, Git, and elan, then run from this directory:

```sh
python3 scripts/bootstrap.py
./lakew exe cache get
./lakew build
./lakew env lean checkpoints/AuditFinal.lean
./lakew env lean checkpoints/AuditBoundedFactors.lean
python3 scripts/check_axioms.py
```

The bootstrap installs the pinned compiler in the project-local `.toolchains/elan`, checks the ClassFieldTheory and AINTLIB revisions, applies their recorded compatibility patches, and runs Lake dependency setup. The default elan and Lake launchers are under `~/.elan/bin`; alternate paths can be set with `QUADRATIC_MOAT_ELAN` and `QUADRATIC_MOAT_LAKE`. Initial setup and cache retrieval require network access. Warnings about locally modified ClassFieldTheory and AINTLIB checkouts are expected after applying the compatibility patches; retain these patches.

The GitHub Actions workflow in `.github/workflows/verify.yml` performs a fresh bootstrap, retrieves the standard mathlib cache, checks that setup preserves the dependency lockfile, builds the library, and runs both endpoint audits on Ubuntu. `scripts/check_axioms.py` reruns the two audits and fails if any of the twelve required reports is missing or uses an axiom outside `propext`, `Classical.choice`, and `Quot.sound`; this includes rejecting `sorryAx`.

For an already bootstrapped checkout, run the build and audit commands directly. The recorded local validation on 2026-10-09 completed `./lakew build` successfully (10002 jobs in the build graph) and passed `checkpoints/AuditBoundedFactors.lean`. The audited declarations depend only on `propext`, `Classical.choice`, and `Quot.sound`, with no `sorryAx` or added mathematical axioms. The audit also checks the theorem's statement and the unit/zero edge cases. See `checkpoints/bounded-factors-validation.txt` for the captured output. Earlier validation of the original theorem is preserved in `logs/final-build.log`, `logs/final-axioms.log`, and `checkpoints/AuditFinal.lean`.

## Proof organization

- `Model`, `Lattice`: the full Minkowski graph and finite lattice balls.
- `ClosePairs`, `ExceptionalNorms`, `Restoration`, `Reduction`, `Periodicity`: finite close pairs of exceptional irreducibles, restoration of all associates, and a uniform component bound from a periodic finite sieve.
- `CoordinateNorm`, `PlanarContext`, `PlanarGeometry`, `SplitArithmetic`, `SignedSieve`, `SignedGeometry`: quadratic norm domination, additive plane coordinates, principal split factors, and the signed rectangle estimate. The coordinate map is additive, not an assumed complex ring embedding.
- `HilbertSplit`, `PrimeIdealRegularization`, `HigherDegreeTail`, `PrimeNormSeries`, `FiniteFiberTransfer`, `PrimeMoments`, `PrimeSupply`, `PrincipalPrimeFamily`: unconditional quantitative principal-split prime supply via an ordinary Hilbert class field and Dedekind zeta regularization.
- `FreshEntropy` through `InformationTelescope`: native residue entropy, coverage, walk packages, and the telescope; generic probability results are reused from the original proof.
- `DenseBins`, `AccurateScales`, `WindowParameters`, `WindowBatch`, `BatchCertificate`, `SieveCertificate`, `SieveSmoothing`, `Main`: scale selection, finite certificates, and the final all-quadratic instantiation.
- `BoundedFactors/Model`, `FactorSupport`, `HitBudget`, `Periodicity`, `Endpoint`: distinct prime-ideal support, the finite hit budget, and the periodic-sieve reduction for the enlarged graph.
- `BoundedFactors/SoftLists` through `SoftInformationTelescope`, `SoftBatchParameters`, `SoftWindowBatch`, `SoftBatchCertificate`, `SoftSieveCertificate`, `Main`: the soft-information argument, finite certificates, and the unconditional bounded-support endpoint.

The source follows the [OpenAI Gaussian moat proof](https://github.com/openai/math) at commit `adc7f1241b42e322a6451854ab7e4b4c146bf78a`. Its 41 original modules are retained under `OAI/NumberTheory/GaussianMoat/`, with the original Apache 2.0 license. The original repository checkout was not modified. New native generalization modules are under `QuadraticMoat/`.

`STATUS.md` records the current result. `checkpoints/bounded-factors-validation.txt` records validation of the extension; `checkpoints/current-state.md` and earlier per-module checkpoints preserve the original theorem's development and audit history.
