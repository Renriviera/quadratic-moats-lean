# Native package information and telescope — built and audited

Owned modules: `PassingInformation.lean`, `WalkPackage.lean`, `InformationTelescope.lean`.

Passing information is already generic in finite laws and residue types, so the native module reuses the original proofs by import. The native package pairs a displacement in `planeBall (D*B)` with a bounded increment word. Its residues are the actual ideal quotients of `𝓞 K`.

Completed proofs include package prefix displacement, true-residue survival, the smoothed hit floor, passing-exception bounds, signed avoidance, batch package information, displacement/word information transport, selected-index sum/entropy/log averages, and existence of a batch with the required information rate.

The telescope proves word entropy rate monotonicity, the common-law information telescope, and the schedule information telescope. `schedule_batch_information` has the original numerical hypotheses and conclusion, replacing Gaussian data with native algebraic integers and adding `ctx.scale≤D` immediately after `1≤D`. The condition supplies the proved native entropy-band soundness theorem; no information estimate is an assumption.

Successful authoritative command:

```
./lakew build QuadraticMoat.InformationTelescope
```

Exit 0, 8980 jobs. Build log: `/tmp/restoration-telescope-build.log`. All owned modules build without warnings. Dependency warnings are existing class reducibility/deprecation/unused-section-variable lint warnings.

Successful direct kernel dependency audit:

```
./lakew env lean --stdin <<'LEAN'
import QuadraticMoat.InformationTelescope
#print axioms QuadraticMoat.ForwardKernel.smoothed_package_floor
#print axioms QuadraticMoat.smoothed_batch_package_information
#print axioms QuadraticMoat.ForwardKernel.package_information_transport
#print axioms QuadraticMoat.averaged_batch_package_information
#print axioms QuadraticMoat.exists_batch_information
#print axioms QuadraticMoat.word_entropy_rate_monotone
#print axioms QuadraticMoat.common_law_information_telescope
#print axioms QuadraticMoat.schedule_information_telescope
#print axioms QuadraticMoat.schedule_batch_information
LEAN
```

Exit 0. All nine results depend only on `[propext, Classical.choice, Quot.sound]`. Source search finds no `sorry`, `admit`, or new `axiom` in the owned modules. The integration beyond this checkpoint is the numerical batch/sieve certificates and unconditional prime-family supply, then the already proved native periodicity/restoration reduction.
