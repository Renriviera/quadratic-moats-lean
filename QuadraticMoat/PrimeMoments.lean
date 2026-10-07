import QuadraticMoat.PrimeSupply
import Mathlib.Analysis.Calculus.Deriv.Slope

namespace QuadraticMoat
open Filter Topology

lemma log_forward_slope_limit {j : ℝ} (hj : 0 < j) (δ : ℝ) :
    Tendsto (fun ε : ℝ => δ * Real.log ((j+ε)/j) / ε) (𝓝[>] 0) (𝓝 (δ/j)) := by
  have h := ((Real.hasDerivAt_log hj.ne').tendsto_slope_zero_right).const_mul δ
  simp only [smul_eq_mul, inv_mul_eq_div] at h
  apply h.congr'
  filter_upwards [self_mem_nhdsWithin] with ε hε
  have hp : 0 < j+ε := add_pos hj hε
  rw [Real.log_div hp.ne' hj.ne']
  ring

lemma log_backward_slope_limit {j : ℝ} (hj : 0 < j) (δ : ℝ) :
    Tendsto (fun ε : ℝ => δ * Real.log (j/(j-ε)) / ε) (𝓝[>] 0) (𝓝 (δ/j)) := by
  have hd : HasDerivAt (fun x : ℝ => -Real.log (j-x)) j⁻¹ 0 := by
    simpa only [id_eq, sub_zero, Pi.neg_apply, neg_div, neg_neg, one_div] using!
      (((hasDerivAt_id (0 : ℝ)).const_sub j).log (by simpa using hj.ne')).neg
  have h := hd.tendsto_slope_zero_right.const_mul δ
  simp only [smul_eq_mul, zero_add, sub_zero, neg_sub_neg, inv_mul_eq_div] at h
  apply h.congr'
  filter_upwards [(eventually_lt_nhds hj).filter_mono nhdsWithin_le_nhds] with ε hε
  rw [Real.log_div hj.ne' (sub_pos.mpr hε).ne']
  ring

/-- Secant squeezing recovers a logarithmic moment from an actual finite
regularized prime-series limit. The bounds are satisfied by positive
Dirichlet series, using `1-exp(-u) ≤ u ≤ exp(u)-1` termwise. -/
theorem moment_limit_of_secants (F M : ℝ → ℝ) (δ B : ℝ)
    (hreg : Tendsto (fun s : ℝ => F s - δ * Real.log (1/(s-1)))
      (𝓝[>] 1) (𝓝 B)) {j : ℝ} (hj : 0 < j)
    (hlo : ∀ ε : ℝ, 0 < ε → ε < j → ∀ᶠ X : ℝ in atTop,
      (F (1+j/X)-F (1+(j+ε)/X))/ε ≤ M X)
    (hhi : ∀ ε : ℝ, 0 < ε → ε < j → ∀ᶠ X : ℝ in atTop,
      M X ≤ (F (1+(j-ε)/X)-F (1+j/X))/ε) :
    Tendsto M atTop (𝓝 (δ/j)) := by
  have hεevent : ∀ᶠ ε : ℝ in 𝓝[>] 0, 0 < ε := self_mem_nhdsWithin
  apply tendsto_order.mpr
  constructor
  · intro l hl
    have he := (log_forward_slope_limit hj δ).eventually (eventually_gt_nhds hl)
    obtain ⟨ε, hεlim, hεpos, hεj⟩ :=
      (he.and (hεevent.and ((eventually_lt_nhds hj).filter_mono nhdsWithin_le_nhds))).exists
    have hflim := (scaled_difference_limit_of_regularization F δ B hreg hj
      (add_pos hj hεpos)).div_const ε
    have hfgt := hflim.eventually (eventually_gt_nhds hεlim)
    filter_upwards [hfgt, hlo ε hεpos hεj] with X hgt hbound
    exact hgt.trans_le hbound
  · intro u hu
    have he := (log_backward_slope_limit hj δ).eventually (eventually_lt_nhds hu)
    obtain ⟨ε, hεlim, hεpos, hεj⟩ :=
      (he.and (hεevent.and ((eventually_lt_nhds hj).filter_mono nhdsWithin_le_nhds))).exists
    have hflim := (scaled_difference_limit_of_regularization F δ B hreg
      (sub_pos.mpr hεj) hj).div_const ε
    have hflt := hflim.eventually (eventually_lt_nhds hεlim)
    filter_upwards [hflt, hhi ε hεpos hεj] with X hlt hbound
    exact hbound.trans_lt hlt


lemma div_rpow_shift (a s h : ℝ) {x : ℝ} (hx : 0 < x) :
    a/x^(s+h) = a/x^s * Real.exp (-h * Real.log x) := by
  have he : x^h = Real.exp (h * Real.log x) := by
    rw [Real.rpow_def_of_pos hx]
    congr 1
    ring
  rw [Real.rpow_add hx, he, div_mul_eq_div_div, div_eq_mul_inv,
    ← Real.exp_neg, neg_mul]

lemma div_rpow_forward_secant (s h : ℝ) {a x : ℝ} (ha : 0 ≤ a) (hx : 0 < x) :
    a/x^s - a/x^(s+h) ≤ h * (a * Real.log x / x^s) := by
  rw [div_rpow_shift a s h hx]
  have hw : 0 ≤ a/x^s := div_nonneg ha (Real.rpow_nonneg hx.le _)
  have he := mul_le_mul_of_nonneg_left (Real.add_one_le_exp (-h * Real.log x)) hw
  have hid : h * (a * Real.log x / x^s) = (a/x^s) * (h * Real.log x) := by ring
  rw [hid]
  nlinarith

lemma div_rpow_backward_secant (s h : ℝ) {a x : ℝ} (ha : 0 ≤ a) (hx : 0 < x) :
    h * (a * Real.log x / x^s) ≤ a/x^(s-h) - a/x^s := by
  rw [show s-h = s+(-h) by ring, div_rpow_shift a s (-h) hx, neg_neg]
  have hw : 0 ≤ a/x^s := div_nonneg ha (Real.rpow_nonneg hx.le _)
  have he := mul_le_mul_of_nonneg_left (Real.add_one_le_exp (h * Real.log x)) hw
  have hid : h * (a * Real.log x / x^s) = (a/x^s) * (h * Real.log x) := by ring
  rw [hid]
  nlinarith

lemma series_forward_secant (b : ℕ → ℝ) (hb0 : b 0 = 0)
    (hb : ∀ n, 0 ≤ b n) (s h : ℝ)
    (hs : Summable (fun n : ℕ => b n/(n : ℝ)^s))
    (hsh : Summable (fun n : ℕ => b n/(n : ℝ)^(s+h)))
    (hslog : Summable (fun n : ℕ => b n * Real.log n / (n : ℝ)^s)) :
    (∑' n : ℕ, b n/(n : ℝ)^s) - (∑' n : ℕ, b n/(n : ℝ)^(s+h)) ≤
      h * (∑' n : ℕ, b n * Real.log n / (n : ℝ)^s) := by
  rw [← hs.tsum_sub hsh, ← tsum_mul_left]
  apply Summable.tsum_le_tsum _ (hs.sub hsh) (hslog.mul_left h)
  intro n
  rcases n.eq_zero_or_pos with rfl | hn
  · simp [hb0]
  · exact div_rpow_forward_secant s h (hb n) (by exact_mod_cast hn)

lemma series_backward_secant (b : ℕ → ℝ) (hb0 : b 0 = 0)
    (hb : ∀ n, 0 ≤ b n) (s h : ℝ)
    (hs : Summable (fun n : ℕ => b n/(n : ℝ)^s))
    (hsh : Summable (fun n : ℕ => b n/(n : ℝ)^(s-h)))
    (hslog : Summable (fun n : ℕ => b n * Real.log n / (n : ℝ)^s)) :
    h * (∑' n : ℕ, b n * Real.log n / (n : ℝ)^s) ≤
      (∑' n : ℕ, b n/(n : ℝ)^(s-h)) - (∑' n : ℕ, b n/(n : ℝ)^s) := by
  rw [← hsh.tsum_sub hs, ← tsum_mul_left]
  apply Summable.tsum_le_tsum _ (hslog.mul_left h) (hsh.sub hs)
  intro n
  rcases n.eq_zero_or_pos with rfl | hn
  · simp [hb0]
  · exact div_rpow_backward_secant s h (hb n) (by exact_mod_cast hn)


/-- Positive Dirichlet series convergent throughout `s>1` remain summable
when their coefficients are multiplied by `log n`. -/
lemma summable_log_weight (b : ℕ → ℝ) (hb0 : b 0 = 0)
    (hb : ∀ n, 0 ≤ b n)
    (hs : ∀ s : ℝ, 1 < s → Summable (fun n : ℕ => b n/(n : ℝ)^s))
    {s : ℝ} (hsp : 1 < s) :
    Summable (fun n : ℕ => b n * Real.log n / (n : ℝ)^s) := by
  let ε := (s-1)/2
  have hε : 0 < ε := by dsimp [ε]; linarith
  have hse : 1 < s-ε := by dsimp [ε]; linarith
  apply Summable.of_nonneg_of_le (fun n => ?_) (fun n => ?_)
    ((hs (s-ε) hse).div_const ε)
  · rcases n.eq_zero_or_pos with rfl | hn
    · simp [hb0]
    · exact div_nonneg (mul_nonneg (hb n)
        (Real.log_nonneg (by exact_mod_cast hn))) (Real.rpow_nonneg (by positivity) _)
  · rcases n.eq_zero_or_pos with rfl | hn
    · simp [hb0]
    · have hnpos : (0 : ℝ) < n := by exact_mod_cast hn
      have hw : 0 ≤ b n/(n : ℝ)^s := div_nonneg (hb n) (Real.rpow_nonneg hnpos.le _)
      calc
        b n * Real.log n / (n : ℝ)^s = (b n/(n : ℝ)^s) * Real.log n := by ring
        _ ≤ (b n/(n : ℝ)^s) * ((n : ℝ)^ε/ε) :=
          mul_le_mul_of_nonneg_left (Real.log_natCast_le_rpow_div n hε) hw
        _ = (b n/(n : ℝ)^(s-ε))/ε := by
          rw [Real.rpow_sub hnpos]
          field_simp [(Real.rpow_pos_of_pos hnpos s).ne',
            (Real.rpow_pos_of_pos hnpos ε).ne', hε.ne']

/-- An actual finite regularized limit of a positive Dirichlet series
implies the logarithmically weighted Laplace moments used by the sieve. -/
theorem log_moment_limit_of_regularization (b : ℕ → ℝ) (hb0 : b 0 = 0)
    (hb : ∀ n, 0 ≤ b n)
    (hs : ∀ s : ℝ, 1 < s → Summable (fun n : ℕ => b n/(n : ℝ)^s))
    (δ B : ℝ)
    (hreg : Tendsto (fun s : ℝ => (∑' n : ℕ, b n/(n : ℝ)^s) -
      δ * Real.log (1/(s-1))) (𝓝[>] 1) (𝓝 B))
    {j : ℝ} (hj : 0 < j) :
    Tendsto (fun X : ℝ => (∑' n : ℕ, b n * Real.log n /
      (n : ℝ)^(1+j/X)) / X) atTop (𝓝 (δ/j)) := by
  apply moment_limit_of_secants (fun s => ∑' n : ℕ, b n/(n : ℝ)^s)
    (fun X => (∑' n : ℕ, b n * Real.log n/(n : ℝ)^(1+j/X))/X) δ B hreg hj
  · intro ε hε hεj
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with X hX
    have hsj : 1 < 1+j/X := by linarith [div_pos hj hX]
    have hsk : 1 < 1+(j+ε)/X := by linarith [div_pos (add_pos hj hε) hX]
    have hid : 1+j/X+ε/X = 1+(j+ε)/X := by ring
    have hseries := series_forward_secant b hb0 hb (1+j/X) (ε/X)
      (hs _ hsj) (by rw [hid]; exact hs _ hsk)
      (summable_log_weight b hb0 hb hs hsj)
    apply (div_le_iff₀ hε).mpr
    rw [hid] at hseries
    convert hseries using 1; ring
  · intro ε hε hεj
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with X hX
    have hsj : 1 < 1+j/X := by linarith [div_pos hj hX]
    have hsk : 1 < 1+(j-ε)/X := by linarith [div_pos (sub_pos.mpr hεj) hX]
    have hid : 1+j/X-ε/X = 1+(j-ε)/X := by ring
    have hseries := series_backward_secant b hb0 hb (1+j/X) (ε/X)
      (hs _ hsj) (by rw [hid]; exact hs _ hsk)
      (summable_log_weight b hb0 hb hs hsj)
    apply (le_div_iff₀ hε).mpr
    rw [hid] at hseries
    convert hseries using 1; ring

/-- Complete analytic window bridge from strong prime-zeta regularization.
The arithmetic proof of this regularization for principal-split primes is
not supplied by this theorem. -/
theorem eventually_log_window_mass_of_regularization (b : ℕ → ℝ)
    (hb0 : b 0 = 0) (hb : ∀ n, 0 ≤ b n)
    (hs : ∀ s : ℝ, 1 < s → Summable (fun n : ℕ => b n/(n : ℝ)^s))
    (δ B : ℝ) (hδ : 0 < δ)
    (hreg : Tendsto (fun s : ℝ => (∑' n : ℕ, b n/(n : ℝ)^s) -
      δ * Real.log (1/(s-1))) (𝓝[>] 1) (𝓝 B)) :
    ∃ c : ℝ, 0 < c ∧ ∀ᶠ X : ℝ in atTop,
      c*X ≤ ∑ n ∈ OAI.GaussianMoat.PrimeLogMass.windowIndices X,
        b n * Real.log n / n := by
  apply eventually_window_mass_of_moments (fun n => b n * Real.log n) δ hδ
  · simp [hb0]
  · intro n
    rcases n.eq_zero_or_pos with rfl | hn
    · simp
    · exact mul_nonneg (hb n) (Real.log_nonneg (by exact_mod_cast hn))
  · exact fun s hsp => summable_log_weight b hb0 hb hs hsp
  · exact fun j hj => log_moment_limit_of_regularization b hb0 hb hs δ B hreg hj

end QuadraticMoat
