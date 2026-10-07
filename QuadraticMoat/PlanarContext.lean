import QuadraticMoat.CoordinateNorm
import QuadraticMoat.PlanarGeometry
import QuadraticMoat.SplitArithmetic

namespace QuadraticMoat
open NumberField
open scoped Classical

variable (K : Type*) [Field K] [NumberField K]

/-- The elementary geometric data needed by the signed sieve. -/
class PlanarContext where
  basis : Module.Basis (Fin 2) ℤ (𝓞 K)
  scale : ℝ
  scale_ge_one : 1 ≤ scale
  norm_bound : ∀ a : 𝓞 K,
    (integerAbsNorm K a : ℝ) ≤ ‖scaledCoordinateComplex basis scale a‖ ^ 2

/-- Every quadratic field has the required planar data, with no prime-supply assumptions. -/
noncomputable def quadraticPlanarContext (hdegree : Module.finrank ℚ K = 2) : PlanarContext K := by
  have hcard : Fintype.card (Module.Free.ChooseBasisIndex ℤ (𝓞 K)) = 2 :=
    (Module.finrank_eq_card_basis (RingOfIntegers.basis K)).symm.trans
      ((RingOfIntegers.rank K).trans hdegree)
  let b := (RingOfIntegers.basis K).reindex (Fintype.equivFinOfCardEq hcard)
  let C : ℝ := (normFormConstant b : ℝ)
  have hC : 1 ≤ C := by
    dsimp only [C]
    have h := normFormConstant_pos b
    exact_mod_cast (show (1 : ℤ) ≤ normFormConstant b by omega)
  have hC0 : 0 ≤ C := (by norm_num : (0 : ℝ) ≤ 1).trans hC
  refine ⟨b, Real.sqrt C, ?_, ?_⟩
  · simpa using Real.sqrt_le_sqrt hC
  · intro a
    have hbound := abs_norm_le_coordinates b a
    rw [scaledCoordinateComplex_norm_sq, Real.sq_sqrt hC0]
    have hr : (|Algebra.norm ℤ a| : ℝ) ≤ C *
        ((b.repr a 0 : ℝ)^2 + (b.repr a 1 : ℝ)^2) := by
      dsimp only [C]
      exact_mod_cast hbound
    simpa only [integerAbsNorm_apply, Nat.cast_natAbs, Int.cast_abs] using hr

namespace PlanarContext

variable {K}

noncomputable def embed (P : PlanarContext K) : (𝓞 K) →+ ℂ where
  toFun := scaledCoordinateComplex P.basis P.scale
  map_zero' := by simp [scaledCoordinateComplex, coordinateComplex]
  map_add' a b := by simp [scaledCoordinateComplex, mul_add]

lemma embed_norm_bound (P : PlanarContext K) (a : 𝓞 K) :
    (integerAbsNorm K a : ℝ) ≤ ‖P.embed a‖^2 := P.norm_bound a

lemma embed_injective (P : PlanarContext K) : Function.Injective P.embed := by
  intro a b h
  have hc : coordinateComplex P.basis a = coordinateComplex P.basis b := by
    exact mul_left_cancel₀ (by exact_mod_cast (lt_of_lt_of_le zero_lt_one P.scale_ge_one).ne') h
  exact (coordinateGaussian P.basis).injective (GaussianInt.toComplex_injective hc)

end PlanarContext
end QuadraticMoat
