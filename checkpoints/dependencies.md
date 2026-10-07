# Additional number theory dependencies

Pinned ClassFieldTheory 2eb22d6485af45f29c5219de6c49f196a61c4f49 and AINTLIB 160e446617a2168c34c95bbe7a76c4105b392434 are now registered in lakefile/manifest.
Applied exactly the original openai/math compatibility patches for Lean4.34.1, saved in patches/.
Both packages depend only on mathlib externally. We compile named modules only, never package default targets.

Active baseline command: `./lakew build CebotarevDensity.Density ClassFieldTheory.Theorems.FrobeniusAndHilbertClassFields.SmallHilbertClassFieldPrimeSplitting > logs/cft-analytic-baseline.log 2>&1`.
CebotarevDensity.Density has compiled successfully. ClassFieldTheory dependency closure still building at checkpoint.

AINTLIB analytical imports are kernel-checked through newly proved PrimeIdealRegularization and HigherDegreeTail; these theorems' axiom audits are recorded by agent in prime-supply checkpoint. The CFT theorem's transitive axiom audit must still be run after its build completes.
