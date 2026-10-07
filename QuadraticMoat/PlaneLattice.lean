import QuadraticMoat.ResidueQuotient

namespace QuadraticMoat
open NumberField
open scoped Classical

variable {K : Type*} [Field K] [NumberField K] [P : PlanarContext K]

/-- The auxiliary planar embedding; only its additive structure is used. -/
noncomputable def toPlane : (𝓞 K) →+ ℂ := P.embed

noncomputable instance planeCoe : CoeOut (𝓞 K) ℂ := ⟨toPlane⟩

@[simp] lemma toPlane_sub (x y : 𝓞 K) : ((x-y : 𝓞 K) : ℂ) = (x : ℂ)-(y : ℂ) :=
  map_sub toPlane x y
@[simp] lemma toPlane_add (x y : 𝓞 K) : ((x+y : 𝓞 K) : ℂ) = (x : ℂ)+(y : ℂ) :=
  map_add toPlane x y
@[simp] lemma toPlane_zero : ((0 : 𝓞 K) : ℂ) = 0 := map_zero toPlane

lemma toPlane_injective : Function.Injective (toPlane (K := K)) := P.embed_injective

lemma coordinate_norm_le_plane (a : 𝓞 K) : ‖coordinateComplex P.basis a‖ ≤ ‖(a : ℂ)‖ := by
  change _ ≤ ‖scaledCoordinateComplex P.basis P.scale a‖
  rw [scaledCoordinateComplex, norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg ((by norm_num : (0:ℝ) ≤ 1).trans P.scale_ge_one)]
  exact le_mul_of_one_le_left (norm_nonneg _) P.scale_ge_one

lemma finite_plane_ball (D : ℝ) : {a : 𝓞 K | ‖(a : ℂ)‖ ≤ D}.Finite := by
  have hG := OAI.GaussianMoat.finite_dist_le 0 D
  apply (hG.preimage (coordinateGaussian P.basis).injective.injOn).subset
  intro a ha
  simp only [Set.mem_preimage, Set.mem_setOf_eq, GaussianInt.toComplex_zero, dist_zero_right]
  change ‖coordinateComplex P.basis a‖ ≤ D
  exact (coordinate_norm_le_plane a).trans ha

noncomputable def planeBall (D : ℝ) : Finset (𝓞 K) := (finite_plane_ball D).toFinset

@[simp] lemma mem_planeBall (D : ℝ) (a : 𝓞 K) : a ∈ planeBall D ↔ ‖(a : ℂ)‖ ≤ D :=
  Set.Finite.mem_toFinset _

lemma plane_walk_pair_displacement (z : ℕ → 𝓞 K) {D : ℝ} (hD : 0 ≤ D)
    (hs : ∀ t, dist (z t : ℂ) (z (t+1) : ℂ) ≤ D)
    (t L i j : ℕ) (hi : i ≤ L) (hj : j ≤ L) :
    ‖((z (t+i)-z (t+j) : 𝓞 K) : ℂ)‖ ≤ D*L := by
  rw [toPlane_sub, ← dist_eq_norm]
  wlog hij : i ≤ j generalizing i j
  · rw [dist_comm]
    exact this j i hj hi (by omega)
  have hsum := dist_le_Ico_sum_of_dist_le (f := fun k => (z (t+k) : ℂ)) hij
    (d := fun _ => D) (fun {k} _ _ => by simpa only [Nat.add_assoc] using hs (t+k))
  simp only [Finset.sum_const, Nat.card_Ico, nsmul_eq_mul] at hsum
  have hle : ((j-i:ℕ):ℝ) ≤ (L:ℝ) := by
    exact_mod_cast (show j-i ≤ L by omega)
  exact hsum.trans (by simpa [mul_comm] using mul_le_mul_of_nonneg_right hle hD)

end QuadraticMoat
