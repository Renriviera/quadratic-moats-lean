import QuadraticMoat.PrimeSupply
import Mathlib.Analysis.Normed.Group.Tannery
import Mathlib.Analysis.SpecialFunctions.Log.Deriv

namespace QuadraticMoat
open Filter Topology

/-- The logarithmic Euler-factor remainder admits a quadratic bound. -/
lemma log_euler_remainder_bound {x b : ℝ} (hx : 0 ≤ x) (hxb : x ≤ b)
    (hb : b ≤ 1/2) :
    0 ≤ -Real.log (1-x)-x ∧ -Real.log (1-x)-x ≤ 2*b^2 := by
  have hx1 : x < 1 := by linarith
  have habs : |x| < 1 := by rwa [abs_of_nonneg hx]
  have hnonneg : 0 ≤ -Real.log (1-x)-x := by
    have := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 1-x by linarith)
    linarith
  have key := Real.abs_log_sub_add_sum_range_le habs 1
  simp only [Finset.sum_range_one, pow_one, Nat.cast_zero, zero_add,
    div_one, abs_of_nonneg hx] at key
  have herr : -Real.log (1-x)-x ≤ x^2/(1-x) := by
    linarith [(abs_le.mp key).1]
  refine ⟨hnonneg, herr.trans ?_⟩
  apply (div_le_iff₀ (show 0 < 1-x by linarith)).mpr
  have hb0 : 0 ≤ b := hx.trans hxb
  nlinarith

/-- The Euler-product logarithmic remainder converges at the pole.
For prime-ideal factors take `b i = 1/N i` and `x s i = N i^(-s)`.
An actual convergent remainder supplies cancellation in scaled finite
prime-zeta differences; a bounded remainder alone does not. -/
theorem log_euler_remainder_tsum_limit {ι : Type*} (b : ι → ℝ)
    (hbhalf : ∀ i, b i ≤ 1/2)
    (hs : Summable (fun i => (b i)^2))
    (x : ℝ → ι → ℝ)
    (hlim : ∀ i, Tendsto (fun s : ℝ => x s i) (𝓝[>] 1) (𝓝 (b i)))
    (hbound : ∀ᶠ s : ℝ in 𝓝[>] 1, ∀ i, 0 ≤ x s i ∧ x s i ≤ b i) :
    Tendsto (fun s : ℝ => ∑' i, (-Real.log (1-x s i)-x s i)) (𝓝[>] 1)
      (𝓝 (∑' i, (-Real.log (1-b i)-b i))) := by
  apply tendsto_tsum_of_dominated_convergence (hs.mul_left 2)
  · intro i
    have hsub := (hlim i).const_sub 1
    have hne : 1-b i ≠ 0 := by linarith [hbhalf i]
    exact ((Real.continuousAt_log hne).tendsto.comp hsub).neg.sub (hlim i)
  · filter_upwards [hbound] with s hsb i
    obtain ⟨hnonneg, hle⟩ := log_euler_remainder_bound (hsb i).1 (hsb i).2 (hbhalf i)
    simpa only [Real.norm_eq_abs, abs_of_nonneg hnonneg] using hle


/-- Concrete norm-factor version of the convergent Euler logarithmic tail. -/
theorem norm_euler_remainder_tsum_limit {ι : Type*} (N : ι → ℝ)
    (hN : ∀ i, 2 ≤ N i) (hs : Summable (fun i => (N i)^(-2 : ℝ))) :
    Tendsto (fun s : ℝ => ∑' i, (-Real.log (1-(N i)^(-s))-(N i)^(-s)))
      (𝓝[>] 1) (𝓝 (∑' i, (-Real.log (1-(N i)⁻¹)-(N i)⁻¹))) := by
  have hNpos (i : ι) : 0 < N i := by linarith [hN i]
  apply log_euler_remainder_tsum_limit (fun i => (N i)⁻¹)
  · intro i
    have := one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 2) (hN i)
    simpa only [one_div] using this
  · apply hs.congr
    intro i
    rw [show (-2 : ℝ) = -(2 : ℝ) by norm_num, Real.rpow_neg (hNpos i).le, Real.rpow_two, inv_pow]
  · intro i
    have ht : Tendsto (fun s : ℝ => -s) (𝓝[>] 1) (𝓝 (-1 : ℝ)) :=
      tendsto_id.neg.mono_left nhdsWithin_le_nhds
    simpa only [Function.comp_def, Real.rpow_neg_one] using
      (Real.continuousAt_const_rpow (hNpos i).ne').tendsto.comp ht
  · filter_upwards [self_mem_nhdsWithin] with s hs i
    have hs' : 1 < s := hs
    refine ⟨Real.rpow_nonneg (hNpos i).le _, ?_⟩
    rw [← Real.rpow_neg_one]
    exact Real.rpow_le_rpow_of_exponent_le (by linarith [hN i]) (by linarith [hs'])

end QuadraticMoat
