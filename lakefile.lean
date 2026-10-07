import Lake
open Lake DSL
package quadraticMoat where
  leanOptions := #[⟨`autoImplicit, false⟩]
require ClassFieldTheory from git
  "https://github.com/n-yamaguchi-0729/ClassFieldTheory.git" @ "2eb22d6485af45f29c5219de6c49f196a61c4f49"
require AINTLIB from git
  "https://github.com/CBirkbeck/AINTLIB.git" @ "160e446617a2168c34c95bbe7a76c4105b392434"
require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git" @ "d13f23b723b8a846827a245b89c10fc7d3f11612"
lean_lib OAI where
  globs := #[`OAI.NumberTheory.GaussianMoat.+]
@[default_target] lean_lib QuadraticMoat
