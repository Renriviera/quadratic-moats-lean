import QuadraticMoat.Lattice
import QuadraticMoat.ClosePairs
import QuadraticMoat.ExceptionalNorms
import QuadraticMoat.Restoration

/-!
Reduction of the full quadratic-field endpoint to a finite-sieve component
statement.  This proves restoration unconditionally from the stated sieve
input; it does not prove that input or the unconditional endpoint.
-/

namespace QuadraticMoat

open NumberField
open scoped Classical

variable (K : Type*) [Field K] [NumberField K]

/-- Finite signed norm values imply finite close exceptional endpoint sets. -/
theorem finite_closeExceptionalEndpoints_of_norm_values
    (hdegree : Module.finrank ℚ K = 2) (A : Set (IrreducibleVertex K))
    (S : Set ℚ) (hS : S.Finite)
    (hnorm : ∀ e : IrreducibleVertex K, e ∉ A → Algebra.norm ℚ (e.val : K) ∈ S)
    (R : ℝ) : (closeExceptionalEndpoints A R).Finite := by
  classical
  let Δ : Set (𝓞 K) := {a | minkowskiDist K a 0 ≤ R}
  have hΔ : Δ.Finite := finite_minkowski_ball K 0 R
  have hpairs := finite_ringOfIntegers_norm_pairs K hdegree S Δ hS hΔ
  have hendpoints := hpairs.image Prod.fst
  apply (hendpoints.preimage Subtype.val_injective.injOn).subset
  rintro e ⟨he, f, hf, hef, hdist⟩
  refine ⟨(e.val, f.val), ?_, rfl⟩
  refine ⟨hnorm e he, hnorm f hf, ?_, ?_⟩
  · change minkowskiDist K (e.val - f.val) 0 ≤ R
    rw [minkowskiDist_sub_zero]
    exact hdist
  · intro heq
    exact hef (Subtype.ext heq)

/-- For fixed D, bounded sieve components and finitely many exceptional norm
values imply the full irreducible graph has a uniform component bound. -/
theorem component_bound_of_sieve_components
    (hdegree : Module.finrank ℚ K = 2) (D : ℝ) (hD : 0 ≤ D)
    (A : Set (IrreducibleVertex K)) (M : ℕ)
    (hbase : ∀ a ∈ A,
      (graphComponent (baseGraph (irreducibleGraph K D) A) a).Finite ∧
      (graphComponent (baseGraph (irreducibleGraph K D) A) a).ncard ≤ M)
    (S : Set ℚ) (hS : S.Finite)
    (hnorm : ∀ e : IrreducibleVertex K, e ∉ A → Algebra.norm ℚ (e.val : K) ∈ S) :
    ∃ B : ℕ, ∀ a : IrreducibleVertex K,
      (component K D a).Finite ∧ (component K D a).ncard ≤ B := by
  let R : ℝ := ((M + 1 : ℕ) : ℝ) * D
  let F := closeExceptionalEndpoints A R
  have hF : F.Finite := finite_closeExceptionalEndpoints_of_norm_values K hdegree A S hS hnorm R
  refine ⟨max M ((F.ncard + 1) * (1 + neighborBound K D * M)), ?_⟩
  exact uniform_component_bound_of_finite_closeExceptionalEndpoints
    (irreducibleGraph K D) A M (neighborBound K D) D hD
    (fun a b hab => hab.2) hbase (irreducible_neighbor_bound K D) hF

/-- The remaining sieve input: periodic avoiding vertices have bounded
components, and omitted irreducibles have norms in a finite signed set. -/
def SieveComponentEndpoint : Prop :=
  ∀ D : ℝ, 0 ≤ D → ∃ (A : Set (IrreducibleVertex K)) (M : ℕ) (S : Set ℚ),
    (∀ a ∈ A,
      (graphComponent (baseGraph (irreducibleGraph K D) A) a).Finite ∧
      (graphComponent (baseGraph (irreducibleGraph K D) A) a).ncard ≤ M) ∧
    S.Finite ∧
    (∀ e : IrreducibleVertex K, e ∉ A → Algebra.norm ℚ (e.val : K) ∈ S)

/-- Negative step sizes have singleton components. -/
theorem component_eq_singleton_of_neg (D : ℝ) (hD : D < 0) (a : IrreducibleVertex K) :
    component K D a = {a} := by
  ext b
  constructor
  · intro h
    apply h.elim
    intro w
    cases w with
    | nil => rfl
    | cons hadj _ =>
      exact (not_le_of_gt hD ((dist_nonneg).trans hadj.2)).elim
  · intro h
    rw [Set.mem_singleton_iff] at h
    subst b
    exact SimpleGraph.Reachable.refl _

/-- All restoration and metric prerequisites are discharged for quadratic
number fields.  The finite-sieve component statement remains the sole input. -/
theorem uniformEndpoint_of_sieveComponentEndpoint
    (hdegree : Module.finrank ℚ K = 2) (hsieve : SieveComponentEndpoint K) :
    UniformEndpoint K := by
  intro D
  by_cases hD : 0 ≤ D
  · obtain ⟨A, M, S, hbase, hS, hnorm⟩ := hsieve D hD
    exact component_bound_of_sieve_components K hdegree D hD A M hbase S hS hnorm
  · refine ⟨1, fun a => ?_⟩
    rw [component_eq_singleton_of_neg K D (lt_of_not_ge hD) a]
    exact ⟨Set.finite_singleton a, by simp⟩

/-- Irreducible vertices avoiding every selected nonunit divisor. -/
def avoidingSelectedDivisors (T : Set (𝓞 K)) : Set (IrreducibleVertex K) :=
  {p | ∀ t ∈ T, ¬ IsUnit t → ¬ t ∣ p.val}

/-- The remaining arithmetic/entropy input in the usual finite-sieve form. -/
def DivisorSieveComponentEndpoint : Prop :=
  ∀ D : ℝ, 0 ≤ D → ∃ (T : Set (𝓞 K)) (M : ℕ), T.Finite ∧
    ∀ a ∈ avoidingSelectedDivisors K T,
      (graphComponent (baseGraph (irreducibleGraph K D) (avoidingSelectedDivisors K T)) a).Finite ∧
      (graphComponent (baseGraph (irreducibleGraph K D) (avoidingSelectedDivisors K T)) a).ncard ≤ M

/-- Selected nonunit divisors automatically provide the finite signed norm
set required for restoration, including every exceptional associate. -/
theorem sieveComponentEndpoint_of_divisorSieveComponentEndpoint
    (hsieve : DivisorSieveComponentEndpoint K) : SieveComponentEndpoint K := by
  intro D hD
  obtain ⟨T, M, hT, hbase⟩ := hsieve D hD
  refine ⟨avoidingSelectedDivisors K T, M, selectedNormValues T, hbase,
    finite_selectedNormValues T hT, ?_⟩
  intro e he
  have hex : ∃ t ∈ T, ¬ IsUnit t ∧ t ∣ e.val := by
    simpa only [avoidingSelectedDivisors, Set.mem_ofPred_eq, not_forall, not_imp, exists_prop,
      not_not] using he
  exact irreducible_norm_mem_selectedNormValues T e.property hex

/-- A finite-divisor sieve with bounded avoiding components suffices for the
full endpoint in every quadratic number field. -/
theorem uniformEndpoint_of_divisorSieveComponentEndpoint
    (hdegree : Module.finrank ℚ K = 2) (hsieve : DivisorSieveComponentEndpoint K) :
    UniformEndpoint K :=
  uniformEndpoint_of_sieveComponentEndpoint K hdegree
    (sieveComponentEndpoint_of_divisorSieveComponentEndpoint K hsieve)

end QuadraticMoat
