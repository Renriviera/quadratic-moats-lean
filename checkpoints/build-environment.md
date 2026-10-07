# Build environment

Project-local compiler installed and tested: Lean 4.34.1, commit 5045d0056413266e57c625dcd7c365b10e377c52, arm64 macOS.
Run all commands from this project via `./lakew`, which sets project-local ELAN_HOME.
Dependency: mathlib d13f23b723b8a846827a245b89c10fc7d3f11612; manifest pins transitive dependencies.
Original scaffold baseline target: `./lakew build OAI.NumberTheory.GaussianMoat.Main`.
Initial dependency bootstrap: `./lakew update` (network required; completed status to be recorded).
Use `./lakew env lean <path>` for quick isolated elaboration, and `./lakew build <module>` to save oleans.

Bootstrap COMPLETED and Gaussian baseline PASSED. Axiom audit saved in checkpoints/AuditGaussian.lean and logs/gaussian-axioms.log (only standard logical axioms).
