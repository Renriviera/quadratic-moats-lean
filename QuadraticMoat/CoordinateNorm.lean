import Mathlib

/-! Arithmetic quadratic-form estimates in an arbitrary integral basis. -/
namespace QuadraticMoat
open scoped Matrix

variable {R : Type*} [CommRing R]

noncomputable def basisDet (b : Module.Basis (Fin 2) ℤ R) (x y : R) : ℤ :=
  b.repr x 0 * b.repr y 1 - b.repr x 1 * b.repr y 0

lemma basisDet_mul_left (b : Module.Basis (Fin 2) ℤ R) (a x y : R) :
    basisDet b (a*x) (a*y) = Algebra.norm ℤ a * basisDet b x y := by
  rw [Algebra.norm_eq_matrix_det b]
  have hx := Algebra.leftMulMatrix_mulVec_repr b a x
  have hy := Algebra.leftMulMatrix_mulVec_repr b a y
  have hx0 := congrFun hx 0
  have hx1 := congrFun hx 1
  have hy0 := congrFun hy 0
  have hy1 := congrFun hy 1
  simp only [Matrix.mulVec, dotProduct, Fin.sum_univ_two] at hx0 hx1 hy0 hy1
  simp only [basisDet, Matrix.det_fin_two]
  rw [← hx0, ← hx1, ← hy0, ← hy1]
  ring

lemma abs_norm_dvd_basisDet (b : Module.Basis (Fin 2) ℤ R) {a x y : R}
    (hx : a ∣ x) (hy : a ∣ y) : |Algebra.norm ℤ a| ∣ basisDet b x y := by
  obtain ⟨u, rfl⟩ := hx
  obtain ⟨v, rfl⟩ := hy
  rw [basisDet_mul_left]
  exact (abs_dvd _ _).mpr (dvd_mul_right _ _)

lemma basisDet_eq_zero_of_common_factor (b : Module.Basis (Fin 2) ℤ R)
    {a x y : R} (hx : a ∣ x) (hy : a ∣ y)
    (hsmall : |basisDet b x y| < |Algebra.norm ℤ a|) : basisDet b x y = 0 := by
  by_contra hne
  have hpos := abs_pos.mpr hne
  have hd := (dvd_abs _ _).mpr (abs_norm_dvd_basisDet b hx hy)
  have := Int.le_of_dvd hpos hd
  omega

lemma norm_quadratic_in_basis (b : Module.Basis (Fin 2) ℤ R) (x : R) :
    Algebra.norm ℤ x =
      (b.repr x 0)^2 * Algebra.norm ℤ (b 0) +
      (b.repr x 0) * (b.repr x 1) *
        (Algebra.norm ℤ (b 0 + b 1) - Algebra.norm ℤ (b 0) - Algebra.norm ℤ (b 1)) +
      (b.repr x 1)^2 * Algebra.norm ℤ (b 1) := by
  have hx : x = (b.repr x 0) • b 0 + (b.repr x 1) • b 1 := by
    simpa only [Fin.sum_univ_two] using (b.sum_repr x).symm
  simp only [Algebra.norm_eq_matrix_det b, Matrix.det_fin_two,
    Algebra.leftMulMatrix_eq_repr_mul]
  conv_lhs => rw [hx]
  simp only [add_mul, smul_mul_assoc, map_add, map_smul,
    Finsupp.add_apply, Finsupp.smul_apply, smul_eq_mul]
  ring

/-- A positive, explicit constant controlling the norm form in any integral basis. -/
noncomputable def normFormConstant (b : Module.Basis (Fin 2) ℤ R) : ℤ :=
  |Algebra.norm ℤ (b 0)| +
    |Algebra.norm ℤ (b 0 + b 1) - Algebra.norm ℤ (b 0) - Algebra.norm ℤ (b 1)| +
    |Algebra.norm ℤ (b 1)| + 1

lemma normFormConstant_pos (b : Module.Basis (Fin 2) ℤ R) : 0 < normFormConstant b := by
  unfold normFormConstant
  positivity

private lemma abs_quadratic_le (a c n₀ m n₁ : ℝ) :
    |a^2*n₀+a*c*m+c^2*n₁| ≤ (|n₀|+|m|+|n₁|+1)*(a^2+c^2) := by
  have hac : |a*c| ≤ a^2+c^2 := by
    have h := two_mul_le_add_sq |a| |c|
    rw [sq_abs, sq_abs, mul_assoc, ← abs_mul] at h
    have hnonneg := abs_nonneg (a*c)
    linarith only [h, hnonneg]
  calc
    |a^2*n₀+a*c*m+c^2*n₁| ≤ |a^2*n₀+a*c*m|+|c^2*n₁| :=
      abs_add_le (a^2*n₀+a*c*m) (c^2*n₁)
    _ ≤ |a^2*n₀|+|a*c*m|+|c^2*n₁| := add_le_add (abs_add_le (a^2*n₀) (a*c*m)) (le_refl |c^2*n₁|)
    _ = a^2*|n₀|+|a*c| * |m|+c^2*|n₁| := by
      rw [abs_mul (a^2), abs_mul (a*c), abs_mul (c^2),
        abs_of_nonneg (sq_nonneg a), abs_of_nonneg (sq_nonneg c)]
    _ ≤ (a^2+c^2)*|n₀|+(a^2+c^2)*|m|+(a^2+c^2)*|n₁| := by
      apply add_le_add
      · apply add_le_add
        · exact mul_le_mul_of_nonneg_right (le_add_of_nonneg_right (sq_nonneg c)) (abs_nonneg n₀)
        · exact mul_le_mul_of_nonneg_right hac (abs_nonneg m)
      · exact mul_le_mul_of_nonneg_right (le_add_of_nonneg_left (sq_nonneg a)) (abs_nonneg n₁)
    _ ≤ _ := by
      have h : 0 ≤ a^2+c^2 := add_nonneg (sq_nonneg a) (sq_nonneg c)
      calc
        _ = (|n₀|+|m|+|n₁|)*(a^2+c^2) := by ring
        _ ≤ _ := mul_le_mul_of_nonneg_right (le_add_of_nonneg_right (by norm_num)) h

lemma abs_norm_le_coordinates (b : Module.Basis (Fin 2) ℤ R) (x : R) :
    |Algebra.norm ℤ x| ≤ normFormConstant b * ((b.repr x 0)^2 + (b.repr x 1)^2) := by
  rw [norm_quadratic_in_basis b x]
  unfold normFormConstant
  have h := abs_quadratic_le (b.repr x 0 : ℝ) (b.repr x 1 : ℝ)
    (Algebra.norm ℤ (b 0) : ℝ)
    ((Algebra.norm ℤ (b 0 + b 1) - Algebra.norm ℤ (b 0) - Algebra.norm ℤ (b 1) : ℤ) : ℝ)
    (Algebra.norm ℤ (b 1) : ℝ)
  exact_mod_cast h

end QuadraticMoat
