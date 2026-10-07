# Quadratic moat theorem in Lean

The unconditional theorem is proved in `QuadraticMoat/Main.lean`:

```lean
theorem irreducible_components_uniformly_bounded
    (K : Type) [Field K] [NumberField K]
    (hdegree : Module.finrank ℚ K = 2) (D : ℝ) :
    ∃ B : ℕ, ∀ a : IrreducibleVertex K,
      (component K D a).Finite ∧ (component K D a).ncard ≤ B
```

Vertices are **all irreducible elements** of `𝓞 K`; associates are distinct vertices. Edges have full Minkowski Euclidean distance at most `D`. In real quadratic fields both real embeddings occur. The bound is independent of the component. Negative and zero step bounds are included.

The exported endpoints are `QuadraticMoat.irreducible_components_uniformly_bounded`, `QuadraticMoat.uniformEndpoint_proved`, and `QuadraticMoat.allQuadraticEndpoint_proved`. Their only mathematical assumptions are that `K` is a number field of degree two. No UFD, class number, prime distribution, finite-unit, or auxiliary sieve assumption remains.

## Verification

From this directory:

```sh
./lakew build QuadraticMoat
./lakew env lean checkpoints/AuditFinal.lean
```

The final build passed (9988 jobs in the build graph). The endpoint axiom audit reports only `propext`, `Classical.choice`, and `Quot.sound`; no `sorryAx` or added mathematical axioms. See `logs/final-build.log` and `logs/final-axioms.log`.

Lean is pinned to 4.34.1. Dependency revisions are fixed in `lake-manifest.json`. A local compiler/cache already exists, so resuming this checkout requires only the commands above. On a fresh checkout with elan installed, run `python3 scripts/bootstrap.py`, then `./lakew exe cache get` and the build. The bootstrap applies the recorded compatibility patches to the pinned ClassFieldTheory and AINTLIB dependencies. Their locally modified status is expected. Do not discard these patches.

## Proof organization

- `Model`, `Lattice`: the full Minkowski graph and finite lattice balls.
- `ClosePairs`, `ExceptionalNorms`, `Restoration`, `Reduction`, `Periodicity`: finite close pairs of exceptional irreducibles, restoration of all associates, and a uniform component bound from a periodic finite sieve.
- `CoordinateNorm`, `PlanarContext`, `PlanarGeometry`, `SplitArithmetic`, `SignedSieve`, `SignedGeometry`: quadratic norm domination, additive plane coordinates, principal split factors, and the signed rectangle estimate. The coordinate map is additive, not an assumed complex ring embedding.
- `HilbertSplit`, `PrimeIdealRegularization`, `HigherDegreeTail`, `PrimeNormSeries`, `FiniteFiberTransfer`, `PrimeMoments`, `PrimeSupply`, `PrincipalPrimeFamily`: unconditional quantitative principal-split prime supply via an ordinary Hilbert class field and Dedekind zeta regularization.
- `FreshEntropy` through `InformationTelescope`: native residue entropy, coverage, walk packages, and the telescope; generic probability results are reused from the original proof.
- `DenseBins`, `AccurateScales`, `WindowParameters`, `WindowBatch`, `BatchCertificate`, `SieveCertificate`, `SieveSmoothing`, `Main`: scale selection, finite certificates, and the final all-quadratic instantiation.

The source follows the [OpenAI Gaussian moat proof](https://github.com/openai/math) at commit `adc7f1241b42e322a6451854ab7e4b4c146bf78a`. Its 41 original modules are retained under `OAI/NumberTheory/GaussianMoat/`, with the original Apache 2.0 license. The original repository checkout was not modified. New native generalization modules are under `QuadraticMoat/`.

`STATUS.md` and `checkpoints/current-state.md` record the final state. Per-module checkpoints preserve the development and audit history. No cloud publication, external messaging, or subscription reset was performed.
