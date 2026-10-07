# Native entropy bands and batch parameters

Owner: supply agent. The following native modules build as part of the single
authoritative `QuadraticMoat.WindowBatch` target:

* `EntropyBand`: native displacement and relative ideal-residue laws;
  continuation entropy and backward coverage; `EntropyBand` and
  `CoverageDerivation` with checked soundness.
* `AccurateScales`: native `entropyBand_from_suffix`, `bandConstant`, margin
  construction, dense cap, accurate bands, and band cardinal bounds.
* `WindowParameters`: native top bands, residue-weight union bounds,
  `separated_factor_cost F hgood`, and `eventually_window_top F hgood`.
* `BatchParameters`: native `one_step_coverage`.
* `Smoothing`: native `coverage_from_scalar_guards`.
* `CommonBlocks`: native `floor_size_lower` and
  `eventually_window_bands F hgood`.
* `WindowBatch`: native `eventually_window_batch F hgood` giving actual
  `BatchCertificate` instances for the retained dyadic bins.

The field binder in these files is `{Fld : Type*} [Field Fld]
[NumberField Fld] [ctx : PlanarContext Fld]`. Supplied-family theorems use
`F : PrimeFamily` and `hgood : ∀ p, F.good p → Nonempty (SplitPrime Fld p)`.

`EntropyBand.alphabet` carries exactly the native geometric guard

```
log 16 + log (ctx.scale² * max (D/ctx.scale)
  ((OAI.GaussianMoat.latticeBall (4*(D/ctx.scale))).card : ℝ))
```

The `EntropyBand.sound` and `CoverageDerivation.sound` hypotheses include
`hDscale : ctx.scale ≤ D` immediately after `hD : 1 ≤ D`, matching the native
walk geometry. `WindowBatch.eventually_window_batch` also includes this
parameter immediately after `hD` for final-certificate integration; the
certificate data construction itself does not need it.

Original scalar APIs are reused: `bandScale`, `bandLength`, accurate-grid
functions, `topCoefficient`, all block lists, enumeration, integer word
lengths and package repetitions, and scalar asymptotic schedule costs.
The parent removed duplicate scalar `bandScale`/`bandLength` definitions from
native MultiscaleSchedule; its sieve-dependent `bandSize` remains native.

Pure-time types `ForwardKernel`, `TimeLaw` and generic finite-law/entropy
facts remain the original OAI types. Native methods must be called explicitly
as `QuadraticMoat.ForwardKernel.method K ...` where needed: dot notation on a
reused type otherwise selects the original Gaussian namespace.

## Verification

Completed commands:

```sh
./lakew build QuadraticMoat.WindowBatch
./lakew env lean logs/window-batch-axioms.lean
```

Build exited 0 (8998 jobs). `logs/window-batch-build.txt` is authoritative
after the parent scalar cleanup and without simultaneous dependency writes.
`logs/window-batch-axioms.txt` audits all native soundness and construction
headlines, plus `planeBall_card_le`; every result depends only on `propext`,
`Classical.choice`, `Quot.sound`. Source checks found no `sorry`, `admit`, or
mathematical axiom declaration in owned modules.

## Integration

The close-pair agent owns native DyadicSieve, BatchCertificate,
SieveCertificate, SeparatedFactors and SieveSmoothing. Parent owns the final
Main integration. Native `principalSplitPrimeFamily K hdegree` supplies `F`,
and `hgood := fun _ h => h` works by definitional equality. This checkpoint
does not itself assert the final quadratic moat endpoint has compiled.

Final follow-up: `QuadraticMoat.Main` subsequently built (9986 jobs), and
`logs/supply-final-review.txt` independently confirms
`allQuadraticEndpoint_proved : AllQuadraticEndpoint` and its standard-three-axiom
audit. No conditional supply or class-number assumption remains.
