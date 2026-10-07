import QuadraticMoat.PlaneLattice
import OAI.NumberTheory.GaussianMoat.PointEnrichment

namespace QuadraticMoat
open NumberField OAI.GaussianMoat
variable {K : Type*} [Field K] [NumberField K] [ctx : PlanarContext K]

/-- Scaling the integer-coordinate lattice by a factor at least one preserves
the original elementary disk counting bound. -/
theorem planeBall_card_le {R : ℝ} (hR : 1 ≤ R) :
    ((planeBall (K := K) R).card : ℝ) ≤ 36*R^2 := by
  have hcard : (planeBall (K := K) R).card ≤ (latticeBall R).card := by
    apply Finset.card_le_card_of_injOn (coordinateGaussian ctx.basis)
    · intro a ha
      change coordinateGaussian ctx.basis a ∈ latticeBall R
      rw [mem_latticeBall]
      exact (coordinate_norm_le_plane a).trans ((mem_planeBall R a).mp ha)
    · exact (coordinateGaussian ctx.basis).injective.injOn
  have hcardR : ((planeBall (K := K) R).card : ℝ) ≤ (latticeBall R).card := by
    exact_mod_cast hcard
  exact hcardR.trans (latticeBall_card_le hR)

end QuadraticMoat
