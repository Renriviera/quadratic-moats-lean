import QuadraticMoat.Lattice
import OAI.NumberTheory.GaussianMoat.DifferenceSampling

/-!
Planar coordinates of an integral basis.  The coordinate map is additive;
no compatibility with ring multiplication is asserted.  A finite Minkowski
increment ball supplies a uniform planar step bound.  Gaussian lattice walk
geometry is then transported and scaled by any real scale≥1.
-/

namespace QuadraticMoat

open NumberField
open scoped Classical

variable {K : Type*} [Field K] [NumberField K]

/-- Additive integer coordinates, packaged as a Gaussian lattice point. -/
noncomputable def coordinateGaussian (b : Module.Basis (Fin 2) ℤ (𝓞 K)) :
    (𝓞 K) ≃ₗ[ℤ] GaussianInt :=
  b.equivFun.trans OAI.GaussianMoat.latticeCoords.symm

/-- The auxiliary planar embedding associated to the integral basis. -/
noncomputable def coordinateComplex (b : Module.Basis (Fin 2) ℤ (𝓞 K)) (a : 𝓞 K) : ℂ :=
  (coordinateGaussian b a : ℂ)

omit [NumberField K] in
@[simp] theorem coordinateComplex_add (b : Module.Basis (Fin 2) ℤ (𝓞 K)) (a c : 𝓞 K) :
    coordinateComplex b (a + c) = coordinateComplex b a + coordinateComplex b c := by
  simp only [coordinateComplex, map_add]

omit [NumberField K] in
@[simp] theorem coordinateComplex_sub (b : Module.Basis (Fin 2) ℤ (𝓞 K)) (a c : 𝓞 K) :
    coordinateComplex b (a - c) = coordinateComplex b a - coordinateComplex b c := by
  simp only [coordinateComplex, map_sub]

/-- All full-Minkowski D-step increments. -/
noncomputable def integerIncrementBall (D : ℝ) : Finset (𝓞 K) :=
  (finite_minkowski_ball K 0 D).toFinset

@[simp] theorem mem_integerIncrementBall (D : ℝ) (a : 𝓞 K) :
    a ∈ integerIncrementBall (K := K) D ↔ minkowskiDist K a 0 ≤ D := by
  simp only [integerIncrementBall, Set.Finite.mem_toFinset, Set.mem_ofPred_eq]

/-- A fixed planar step bound obtained from finitely many Minkowski increments. -/
noncomputable def coordinateStepBound (b : Module.Basis (Fin 2) ℤ (𝓞 K)) (D : ℝ) : ℝ :=
  1 + ∑ a ∈ integerIncrementBall (K := K) D, ‖coordinateComplex b a‖

theorem coordinateStepBound_ge_one (b : Module.Basis (Fin 2) ℤ (𝓞 K)) (D : ℝ) :
    1 ≤ coordinateStepBound b D := by
  have h : 0 ≤ ∑ a ∈ integerIncrementBall (K := K) D, ‖coordinateComplex b a‖ :=
    Finset.sum_nonneg (fun _ _ => norm_nonneg _)
  unfold coordinateStepBound
  linarith

/-- Every full Minkowski D-edge is a bounded coordinate edge, independently
of its position in the ring-of-integers lattice. -/
theorem coordinate_dist_le_stepBound (b : Module.Basis (Fin 2) ℤ (𝓞 K))
    (D : ℝ) {a c : 𝓞 K} (h : minkowskiDist K a c ≤ D) :
    dist (coordinateComplex b a) (coordinateComplex b c) ≤ coordinateStepBound b D := by
  have hin : a - c ∈ integerIncrementBall (K := K) D := by
    rw [mem_integerIncrementBall, minkowskiDist_sub_zero]
    exact h
  have hsum := Finset.single_le_sum (fun x (_ : x ∈ integerIncrementBall (K := K) D) =>
    norm_nonneg (coordinateComplex b x)) hin
  rw [coordinateComplex_sub] at hsum
  rw [dist_eq_norm]
  unfold coordinateStepBound
  linarith

/-- The real-scaled planar coordinates used to dominate the signed field norm. -/
noncomputable def scaledCoordinateComplex (b : Module.Basis (Fin 2) ℤ (𝓞 K))
    (scale : ℝ) (a : 𝓞 K) : ℂ := (scale : ℂ) * coordinateComplex b a

noncomputable def integerWalkSegment (z : ℕ → 𝓞 K) (n : ℕ) : Finset (𝓞 K) :=
  (Finset.range (n + 1)).image z

noncomputable def integerDifferences (E : Finset (𝓞 K)) : Finset (𝓞 K) :=
  (E ×ˢ E).image (fun p => p.1 - p.2)

omit [NumberField K] in
@[simp] theorem mem_integerWalkSegment (z : ℕ → 𝓞 K) (n : ℕ) (w : 𝓞 K) :
    w ∈ integerWalkSegment z n ↔ ∃ i ≤ n, z i = w := by
  simp [integerWalkSegment, Finset.mem_image]

omit [NumberField K] in
@[simp] theorem mem_integerDifferences (E : Finset (𝓞 K)) (w : 𝓞 K) :
    w ∈ integerDifferences E ↔ ∃ a ∈ E, ∃ c ∈ E, a - c = w := by
  simp [integerDifferences, Finset.mem_image, Prod.exists, and_assoc]

omit [NumberField K] in
theorem coordinate_walkSegment (b : Module.Basis (Fin 2) ℤ (𝓞 K)) (z : ℕ → 𝓞 K) (n : ℕ) :
    OAI.GaussianMoat.walkSegment (fun i => coordinateGaussian b (z i)) n =
      (integerWalkSegment z n).image (coordinateGaussian b) := by
  simp only [OAI.GaussianMoat.walkSegment, integerWalkSegment, Finset.image_image]
  rfl

omit [NumberField K] in
theorem coordinate_differences (b : Module.Basis (Fin 2) ℤ (𝓞 K)) (E : Finset (𝓞 K)) :
    OAI.GaussianMoat.differences (E.image (coordinateGaussian b)) =
      (integerDifferences E).image (coordinateGaussian b) := by
  classical
  ext w
  constructor
  · intro hw
    obtain ⟨a, ha, c, hc, hac⟩ := (OAI.GaussianMoat.mem_differences _ _).mp hw
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp ha
    obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hc
    exact Finset.mem_image.mpr ⟨x - y, mem_integerDifferences E _ |>.mpr
      ⟨x, hx, y, hy, rfl⟩, by simpa only [map_sub] using hac⟩
  · intro hw
    obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hw
    obtain ⟨x, hx, y, hy, rfl⟩ := (mem_integerDifferences E _).mp hv
    exact (OAI.GaussianMoat.mem_differences _ _).mpr
      ⟨coordinateGaussian b x, Finset.mem_image.mpr ⟨x, hx, rfl⟩,
        coordinateGaussian b y, Finset.mem_image.mpr ⟨y, hy, rfl⟩, (map_sub _ _ _).symm⟩

omit [NumberField K] in
theorem coordinate_differences_card (b : Module.Basis (Fin 2) ℤ (𝓞 K))
    (z : ℕ → 𝓞 K) (n : ℕ) :
    (OAI.GaussianMoat.differences
      (OAI.GaussianMoat.walkSegment (fun i => coordinateGaussian b (z i)) n)).card =
      (integerDifferences (integerWalkSegment z n)).card := by
  rw [coordinate_walkSegment, coordinate_differences,
    Finset.card_image_of_injective _ (coordinateGaussian b).injective]

omit [NumberField K] in
/-- A scaled-coordinate rectangle retains the Gaussian walk area estimates;
the difference count is stated on native algebraic integers. -/
theorem scaled_walk_many_differences
    (b : Module.Basis (Fin 2) ℤ (𝓞 K)) (scale : ℝ) (hscale : 1 ≤ scale)
    (z : ℕ → 𝓞 K) {n : ℕ} (hn : 1 ≤ n) (hinj : Function.Injective z)
    {D : ℝ} (hD : 1 ≤ D)
    (hz : ∀ i < n, dist (coordinateComplex b (z i)) (coordinateComplex b (z (i + 1))) ≤ D) :
    ∃ (R W : ℝ) (e c : ℂ), 1 ≤ W ∧ W ≤ R ∧ ‖e‖ = 1 ∧
      (∀ p ∈ integerWalkSegment z n, 0 ≤ (e * (scaledCoordinateComplex b scale p - c)).re ∧
        (e * (scaledCoordinateComplex b scale p - c)).re ≤ R ∧
        |(e * (scaledCoordinateComplex b scale p - c)).im| ≤ W) ∧
      (n : ℝ) ≤ 18 * (R * W) ∧ R * W ≤ (scale * D) ^ 2 * (n : ℝ) ^ 2 ∧
      R * W ≤ (scale ^ 2 * max D ((OAI.GaussianMoat.latticeBall (4 * D)).card : ℝ)) *
        (integerDifferences (integerWalkSegment z n)).card := by
  obtain ⟨R, W, e, c, hW, hWR, he, hrect, hcount, hupper, hmany⟩ :=
    OAI.GaussianMoat.walk_many_differences (fun i => coordinateGaussian b (z i)) hn
      ((coordinateGaussian b).injective.comp hinj) hD hz
  have hscale0 : 0 ≤ scale := by linarith
  have hR0 : 0 ≤ R := by linarith
  have hW0 : 0 ≤ W := by linarith
  have hscale2 : 1 ≤ scale ^ 2 := by nlinarith
  refine ⟨scale * R, scale * W, e, (scale : ℂ) * c, ?_, ?_, he, ?_, ?_, ?_, ?_⟩
  · nlinarith
  · exact mul_le_mul_of_nonneg_left hWR hscale0
  · intro p hp
    obtain ⟨i, hi, rfl⟩ := (mem_integerWalkSegment z n p).mp hp
    have hpoint := hrect (coordinateGaussian b (z i))
      ((OAI.GaussianMoat.mem_walkSegment _ _ _).mpr ⟨i, hi, rfl⟩)
    have hscale : e * (scaledCoordinateComplex b scale (z i) - (scale : ℂ) * c) =
        (scale : ℂ) * (e * (coordinateComplex b (z i) - c)) := by
      unfold scaledCoordinateComplex
      ring
    rw [hscale]
    simp only [Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
      zero_mul, sub_zero, add_zero, abs_mul, abs_of_nonneg hscale0]
    exact ⟨mul_nonneg hscale0 hpoint.1, mul_le_mul_of_nonneg_left hpoint.2.1 hscale0,
      mul_le_mul_of_nonneg_left hpoint.2.2 hscale0⟩
  · have harea : R * W ≤ (scale * R) * (scale * W) := by
      have h := mul_le_mul_of_nonneg_right hscale2 (mul_nonneg hR0 hW0)
      nlinarith
    exact hcount.trans (mul_le_mul_of_nonneg_left harea (by norm_num))
  · have h := mul_le_mul_of_nonneg_left hupper (sq_nonneg scale)
    nlinarith
  · rw [coordinate_differences_card] at hmany
    have h := mul_le_mul_of_nonneg_left hmany (sq_nonneg scale)
    nlinarith

/-- Full Minkowski walks have a fixed scaled planar step bound. -/
theorem scaled_coordinate_dist_le_stepBound
    (b : Module.Basis (Fin 2) ℤ (𝓞 K)) (scale : ℝ) (hscale : 0 ≤ scale)
    (D : ℝ) {a c : 𝓞 K} (h : minkowskiDist K a c ≤ D) :
    dist (scaledCoordinateComplex b scale a) (scaledCoordinateComplex b scale c) ≤
      scale * coordinateStepBound b D := by
  have hc := coordinate_dist_le_stepBound b D h
  have hdist : dist (scaledCoordinateComplex b scale a) (scaledCoordinateComplex b scale c) =
      scale * dist (coordinateComplex b a) (coordinateComplex b c) := by
    simp only [scaledCoordinateComplex, dist_eq_norm, ← mul_sub, norm_mul,
      Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hscale]
  rw [hdist]
  exact mul_le_mul_of_nonneg_left hc hscale

/-- The native full-Minkowski walk version of the scaled rectangle/difference lemma. -/
theorem full_minkowski_walk_many_differences
    (b : Module.Basis (Fin 2) ℤ (𝓞 K)) (scale : ℝ) (hscale : 1 ≤ scale)
    (z : ℕ → 𝓞 K) {n : ℕ} (hn : 1 ≤ n) (hinj : Function.Injective z) (D : ℝ)
    (hz : ∀ i < n, minkowskiDist K (z i) (z (i + 1)) ≤ D) :
    ∃ (R W : ℝ) (e c : ℂ), 1 ≤ W ∧ W ≤ R ∧ ‖e‖ = 1 ∧
      (∀ p ∈ integerWalkSegment z n, 0 ≤ (e * (scaledCoordinateComplex b scale p - c)).re ∧
        (e * (scaledCoordinateComplex b scale p - c)).re ≤ R ∧
        |(e * (scaledCoordinateComplex b scale p - c)).im| ≤ W) ∧
      (n : ℝ) ≤ 18 * (R * W) ∧
      R * W ≤ (scale * coordinateStepBound b D) ^ 2 * (n : ℝ) ^ 2 ∧
      R * W ≤ (scale ^ 2 * max (coordinateStepBound b D)
        ((OAI.GaussianMoat.latticeBall (4 * coordinateStepBound b D)).card : ℝ)) *
        (integerDifferences (integerWalkSegment z n)).card :=
  scaled_walk_many_differences b scale hscale z hn hinj (coordinateStepBound_ge_one b D)
    (fun i hi => coordinate_dist_le_stepBound b D (hz i hi))

omit [NumberField K] in
/-- Scaling multiplies the planar determinant by scale². -/
theorem scaled_coordinate_determinant (b : Module.Basis (Fin 2) ℤ (𝓞 K))
    (scale : ℝ) (a c : 𝓞 K) :
    (scaledCoordinateComplex b scale a).re * (scaledCoordinateComplex b scale c).im -
      (scaledCoordinateComplex b scale a).im * (scaledCoordinateComplex b scale c).re =
    scale ^ 2 * (((coordinateGaussian b a).re * (coordinateGaussian b c).im -
      (coordinateGaussian b a).im * (coordinateGaussian b c).re : ℤ) : ℝ) := by
  simp only [scaledCoordinateComplex, coordinateComplex, Complex.mul_re, Complex.mul_im,
    Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero, add_zero,
    ← GaussianInt.intCast_re, ← GaussianInt.intCast_im, Int.cast_sub, Int.cast_mul]
  ring

omit [NumberField K] in
@[simp] theorem coordinateGaussian_re (b : Module.Basis (Fin 2) ℤ (𝓞 K)) (a : 𝓞 K) :
    (coordinateGaussian b a).re = b.repr a 0 := by
  change b.equivFun a 0 = b.repr a 0
  rw [Module.Basis.equivFun_apply]

omit [NumberField K] in
@[simp] theorem coordinateGaussian_im (b : Module.Basis (Fin 2) ℤ (𝓞 K)) (a : 𝓞 K) :
    (coordinateGaussian b a).im = b.repr a 1 := by
  change b.equivFun a 1 = b.repr a 1
  rw [Module.Basis.equivFun_apply]

omit [NumberField K] in
/-- Coordinate length squared is the sum of squares of the integral coefficients. -/
theorem coordinateComplex_norm_sq (b : Module.Basis (Fin 2) ℤ (𝓞 K)) (a : 𝓞 K) :
    ‖coordinateComplex b a‖ ^ 2 = (b.repr a 0 : ℝ) ^ 2 + (b.repr a 1 : ℝ) ^ 2 := by
  rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply]
  simp only [coordinateComplex, ← GaussianInt.intCast_re, ← GaussianInt.intCast_im,
    coordinateGaussian_re, coordinateGaussian_im]
  ring

omit [NumberField K] in
/-- This identity connects the scaled coordinate length to the field norm form bound. -/
theorem scaledCoordinateComplex_norm_sq (b : Module.Basis (Fin 2) ℤ (𝓞 K))
    (scale : ℝ) (a : 𝓞 K) :
    ‖scaledCoordinateComplex b scale a‖ ^ 2 =
      scale ^ 2 * ((b.repr a 0 : ℝ) ^ 2 + (b.repr a 1 : ℝ) ^ 2) := by
  simp only [scaledCoordinateComplex, norm_mul, Complex.norm_real, Real.norm_eq_abs,
    mul_pow, sq_abs, coordinateComplex_norm_sq]

end QuadraticMoat
