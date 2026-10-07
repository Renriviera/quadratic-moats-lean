import OAI.NumberTheory.GaussianMoat.PrimeMass
import Mathlib.NumberTheory.NumberField.DedekindZeta

/-!
# Analytic bridges for quadratic principal-split prime supply

The sequence theorem below is conditional on explicit Laplace moments. It does
not assert those moments for principal-split primes. The arithmetic
instantiation and extraction of moments from prime-zeta regularization remain
separate obligations; see `checkpoints/prime-supply.md`.
-/

set_option maxRecDepth 10000

namespace QuadraticMoat

open Filter Topology Finset
open OAI.GaussianMoat.PrimeLogMass

/-- The regularized logarithm of the Dedekind zeta function has an actual
finite limit, stronger than merely a bounded error. -/
theorem log_dedekindZeta_regularized_limit (K : Type*) [Field K] [NumberField K] :
    Tendsto (fun s : ℝ => Real.log (NumberField.dedekindZeta K (s : ℂ)).re -
      Real.log (1 / (s - 1))) (𝓝[>] 1)
      (𝓝 (Real.log (NumberField.dedekindZeta_residue K))) := by
  have hF : Tendsto (fun s : ℝ => (s - 1) *
      (NumberField.dedekindZeta K (s : ℂ)).re) (𝓝[>] 1)
      (𝓝 (NumberField.dedekindZeta_residue K)) := by
    refine ((Complex.continuous_re.tendsto _).comp
      (NumberField.tendsto_sub_one_mul_dedekindZeta_nhdsGT K)).congr fun s => ?_
    rw [Function.comp_apply, show ((s : ℂ) - 1) = ((s - 1 : ℝ) : ℂ) by
      push_cast; ring, Complex.re_ofReal_mul]
  have hlog := (Real.continuousAt_log
    (NumberField.dedekindZeta_residue_pos K).ne').tendsto.comp hF
  apply hlog.congr'
  have hpos := hF.eventually (eventually_gt_nhds
    (NumberField.dedekindZeta_residue_pos K))
  filter_upwards [hpos, self_mem_nhdsWithin] with s hprod hs
  have hspos : 0 < s - 1 := sub_pos.mpr hs
  have hzpos : 0 < (NumberField.dedekindZeta K (s : ℂ)).re :=
    (mul_pos_iff_of_pos_left hspos).mp hprod
  rw [Function.comp_apply, one_div, Real.log_inv, sub_neg_eq_add,
    Real.log_mul hspos.ne' hzpos.ne']
  ring

/-- Positive offsets divided by a scale approach one from above. -/
lemma one_add_div_tendsto_nhdsGT {j : ℝ} (hj : 0 < j) :
    Tendsto (fun X : ℝ => 1+j/X) atTop (𝓝[>] 1) := by
  refine tendsto_nhdsWithin_iff.mpr ⟨?_, ?_⟩
  · simpa using (tendsto_const_nhds.div_atTop tendsto_id :
      Tendsto (fun X : ℝ => j/X) atTop (𝓝 0)).const_add 1
  · filter_upwards [eventually_gt_atTop (0 : ℝ)] with X hX
    exact lt_add_of_pos_right 1 (div_pos hj hX)

/-- The finite regularized prime-zeta limit gives exact finite differences
at scaled offsets. A density ratio or bounded regularized error alone does
not supply this conclusion. -/
theorem scaled_difference_limit_of_regularization (F : ℝ → ℝ) (δ B : ℝ)
    (hreg : Tendsto (fun s : ℝ => F s - δ * Real.log (1/(s-1)))
      (𝓝[>] 1) (𝓝 B)) {j k : ℝ} (hj : 0 < j) (hk : 0 < k) :
    Tendsto (fun X : ℝ => F (1+j/X) - F (1+k/X)) atTop
      (𝓝 (δ * Real.log (k/j))) := by
  have hdiff := (hreg.comp (one_add_div_tendsto_nhdsGT hj)).sub
    (hreg.comp (one_add_div_tendsto_nhdsGT hk))
  have hlim := hdiff.add_const (δ * Real.log (k/j))
  simp only [sub_self, zero_add] at hlim
  apply hlim.congr'
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with X hX
  have hjeq : 1/(1+j/X-1) = X/j := by field_simp [hj.ne', hX.ne']; ring
  have hkeq : 1/(1+k/X-1) = X/k := by field_simp [hk.ne', hX.ne']; ring
  simp only [Function.comp_apply]
  rw [hjeq, hkeq, Real.log_div hX.ne' hj.ne', Real.log_div hX.ne' hk.ne',
    Real.log_div hk.ne' hj.ne']
  ring

section SequenceWindow

variable (a : ℕ → ℝ)

lemma sequence_laplace_term (n j : ℕ) (X : ℝ) (ha0 : a 0 = 0) :
    a n / (n : ℝ)^(1+(j+1 : ℝ)/X) =
      a n / n * (Real.exp (-Real.log n/X))^(j+1) := by
  rcases n.eq_zero_or_pos with rfl | hn
  · simp [ha0]
  · rw [Real.rpow_add (by exact_mod_cast hn), Real.rpow_one, div_mul_eq_div_div,
      div_eq_mul_inv _ ((n : ℝ)^((j+1 : ℝ)/X)),
      ← Real.rpow_neg (by positivity),
      show -((j+1 : ℝ)/X) = -(j+1 : ℝ)/X by ring,
      laplace_power n j X (by omega)]

lemma sequence_polynomial_laplace (P : Polynomial ℝ) {X : ℝ} (hX : 0 < X)
    (ha0 : a 0 = 0)
    (hs : ∀ s : ℝ, 1 < s → Summable (fun n : ℕ => a n / (n : ℝ)^s)) :
    (∑ j ∈ P.support, P.coeff j *
      (∑' n, a n / (n : ℝ)^(1+(j+1 : ℝ)/X))) =
    ∑' n, a n / n * Real.exp (-Real.log n/X) *
      Polynomial.eval (Real.exp (-Real.log n/X)) P := by
  have hsum (j : ℕ) : Summable (fun n : ℕ => a n /
      (n : ℝ)^(1+(j+1 : ℝ)/X)) := hs _ (by
    have := div_pos (show (0 : ℝ) < j+1 by positivity) hX
    linarith)
  simp_rw [← tsum_mul_left]
  rw [← Summable.tsum_finsetSum (fun j _ => (hsum j).mul_left (P.coeff j))]
  apply tsum_congr
  intro n
  simp_rw [sequence_laplace_term a n _ X ha0, Polynomial.eval_eq_sum,
    Polynomial.sum_def, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  rw [pow_succ]
  ring

lemma sequence_polynomial_summable (P : Polynomial ℝ) {X : ℝ} (hX : 0 < X)
    (ha0 : a 0 = 0)
    (hs : ∀ s : ℝ, 1 < s → Summable (fun n : ℕ => a n / (n : ℝ)^s)) :
    Summable (fun n : ℕ => a n / n * Real.exp (-Real.log n/X) *
      Polynomial.eval (Real.exp (-Real.log n/X)) P) := by
  have hsum (j : ℕ) : Summable (fun n : ℕ => P.coeff j *
      (a n / (n : ℝ)^(1+(j+1 : ℝ)/X))) := (hs _ (by
    have := div_pos (show (0 : ℝ) < j+1 by positivity) hX
    linarith)).mul_left _
  apply (summable_sum (s := P.support) (fun j _ => hsum j)).congr
  intro n
  simp_rw [sequence_laplace_term a n _ X ha0, Polynomial.eval_eq_sum,
    Polynomial.sum_def, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  rw [pow_succ]
  ring

lemma sequence_window_dominates {X : ℝ} (hX : 0 < X)
    (ha0 : a 0 = 0) (ha : ∀ n, 0 ≤ a n)
    (hs : ∀ s : ℝ, 1 < s → Summable (fun n : ℕ => a n / (n : ℝ)^s)) :
    (∑' n, a n / n * Real.exp (-Real.log n/X) *
      Polynomial.eval (Real.exp (-Real.log n/X)) windowPolynomial) ≤
      ∑ n ∈ windowIndices X, a n / n := by
  classical
  let f : ℕ → ℝ := fun n => if n ∈ windowIndices X then a n / n else 0
  have hf : Summable f := summable_of_ne_finset_zero (s := windowIndices X) (by
    intro n hn
    simp [f, hn])
  have ht : (∑' n, f n) = ∑ n ∈ windowIndices X, a n / n := by
    rw [tsum_eq_sum (s := windowIndices X) (by intro n hn; simp [f, hn])]
    apply Finset.sum_congr rfl
    intro n hn
    simp [f, hn]
  rw [← ht]
  apply Summable.tsum_le_tsum _ (sequence_polynomial_summable a windowPolynomial hX ha0 hs) hf
  intro n
  by_cases hn : n = 0
  · subst n
    simp [f, ha0]
  have hlog : 0 ≤ Real.log n :=
    Real.log_nonneg (by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hn)
  have hy : Real.exp (-Real.log n/X) ∈ Set.Icc (0 : ℝ) 1 :=
    ⟨(Real.exp_pos _).le, Real.exp_le_one_iff.mpr
      (div_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hlog) hX.le)⟩
  have hw : 0 ≤ a n / n := div_nonneg (ha n) (Nat.cast_nonneg n)
  by_cases hm : n ∈ windowIndices X
  · simp only [f, ite_eq_left hm]
    calc
      _ ≤ a n / n * Real.exp (-Real.log n/X) :=
        mul_le_of_le_one_right (mul_nonneg hw hy.1) (windowPolynomial_le_one hy)
      _ ≤ _ := mul_le_of_le_one_right hw hy.2
  · simp only [f, ite_eq_right hm]
    exact mul_nonpos_of_nonneg_of_nonpos (mul_nonneg hw hy.1)
      (laplace_window_nonpos hX n hn hm)

lemma sequence_polynomial_moment_limit (δ : ℝ)
    (hmom : ∀ j : ℝ, 0 < j →
      Tendsto (fun X : ℝ => (∑' n, a n / (n : ℝ)^(1+j/X)) / X)
        atTop (𝓝 (δ / j))) (P : Polynomial ℝ) :
    Tendsto (fun X : ℝ => ∑ j ∈ P.support, P.coeff j *
      ((∑' n, a n / (n : ℝ)^(1+(j+1 : ℝ)/X)) / X)) atTop
      (𝓝 (δ * (∫ x : ℝ in 0..1, Polynomial.eval x P))) := by
  have h (j : ℕ) := (hmom (j+1) (by positivity)).const_mul (P.coeff j)
  have ht := tendsto_finsetSum P.support (fun j _ => h j)
  convert ht using 1
  congr 1
  rw [polynomial_integral_coeff, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  ring

/-- A positive Laplace-moment density supplies positive linear mass in
`[exp(1.001 X), exp(1.0499 X)]`. For principal-split primes the intended
weight is `a n = if principalSplit n then log n else 0`. -/
theorem eventually_window_mass_of_moments (δ : ℝ) (hδ : 0 < δ)
    (ha0 : a 0 = 0) (ha : ∀ n, 0 ≤ a n)
    (hs : ∀ s : ℝ, 1 < s → Summable (fun n : ℕ => a n / (n : ℝ)^s))
    (hmom : ∀ j : ℝ, 0 < j →
      Tendsto (fun X : ℝ => (∑' n, a n / (n : ℝ)^(1+j/X)) / X)
        atTop (𝓝 (δ / j))) :
    ∃ c : ℝ, 0 < c ∧ ∀ᶠ X : ℝ in atTop,
      c*X ≤ ∑ n ∈ windowIndices X, a n / n := by
  let c := δ * (∫ x : ℝ in 0..1, Polynomial.eval x windowPolynomial)
  have hc : 0 < c := mul_pos hδ windowPolynomial_integral_pos
  have hlim := sequence_polynomial_moment_limit a δ hmom windowPolynomial
  have he := hlim.eventually (eventually_gt_nhds (show c/2 < c by linarith))
  refine ⟨c/2, half_pos hc, ?_⟩
  filter_upwards [he, eventually_gt_atTop (0 : ℝ)] with X h hX
  have hid := sequence_polynomial_laplace a windowPolynomial hX ha0 hs
  have h' : c/2 < (∑' n, a n / n * Real.exp (-Real.log n/X) *
      Polynomial.eval (Real.exp (-Real.log n/X)) windowPolynomial) / X := by
    rw [← hid, Finset.sum_div]
    simpa only [mul_div_assoc] using h
  exact ((lt_div_iff₀ hX).mp h').le.trans (sequence_window_dominates a hX ha0 ha hs)

end SequenceWindow
end QuadraticMoat
