import QuadraticMoat.PrimeNormSeries

namespace QuadraticMoat
open Filter Topology NumberField

/-- Native norm-fiber counts outside a finite exceptional set supply the
strong regularization of the arithmetic coefficient series. The only
remaining hypothesis is the arithmetic counting formula. -/
theorem regularized_limit_of_norm_fiber_formula (H : Type*) [Field H] [NumberField H]
    (m : ℝ) (hm : 0 < m) (a : ℕ → ℝ) (ha0 : a 0 = 0) (bad : Finset ℕ)
    (hcount : ∀ n : ℕ, n ∉ bad → (primeNormMultiplicity H n : ℝ) = m * a n) :
    (∀ s : ℝ, 1 < s → Summable (fun n : ℕ => a n/(n : ℝ)^s)) ∧
    ∃ B : ℝ, Tendsto (fun s : ℝ => (∑' n : ℕ, a n/(n : ℝ)^s) -
      m⁻¹ * Real.log (1/(s-1))) (𝓝[>] 1) (𝓝 B) := by
  classical
  let e : ℕ → ℝ := fun n => if n ∈ bad then (primeNormMultiplicity H n : ℝ)-m*a n else 0
  have he0 : e 0 = 0 := by
    dsimp [e]
    rw [ha0, primeNormMultiplicity_zero_of_not_prime H (by norm_num : ¬Nat.Prime 0)]
    simp
  have hid (n : ℕ) : (primeNormMultiplicity H n : ℝ) = m*a n+e n := by
    by_cases hn : n ∈ bad
    · simp [e, hn]
    · simpa [e, hn] using hcount n hn
  have hse (s : ℝ) : Summable (fun n : ℕ => e n/(n : ℝ)^s) :=
    summable_of_ne_finset_zero (s := bad) (by intro n hn; simp [e, hn])
  have hsa (s : ℝ) (hs : 1 < s) : Summable (fun n : ℕ => a n/(n : ℝ)^s) := by
    apply (summable_mul_left_iff hm.ne').mp
    apply ((summable_primeNormMultiplicity_div H hs).sub (hse s)).congr
    intro n
    rw [hid n]
    ring
  have hEterm (n : ℕ) : Tendsto (fun s : ℝ => e n/(n : ℝ)^s) (𝓝[>] 1)
      (𝓝 (e n/n)) := by
    rcases n.eq_zero_or_pos with rfl | hn
    · simpa only [he0, zero_div] using
        (tendsto_const_nhds : Tendsto (fun _ : ℝ => (0 : ℝ)) (𝓝[>] 1) (𝓝 0))
    · have hnpos : (0 : ℝ) < n := by exact_mod_cast hn
      have hden := (Real.continuousAt_const_rpow hnpos.ne').tendsto.mono_left
        (nhdsWithin_le_nhds : 𝓝[>] (1 : ℝ) ≤ 𝓝 1)
      simpa only [Pi.div_apply, Real.rpow_one] using!
        (tendsto_const_nhds.div hden (by simpa only [Real.rpow_one] using hnpos.ne'))
  have hEsum (s : ℝ) : (∑' n : ℕ, e n/(n : ℝ)^s) =
      ∑ n ∈ bad, e n/(n : ℝ)^s :=
    tsum_eq_sum (s := bad) (by intro n hn; simp [e, hn])
  have hElim : Tendsto (fun s : ℝ => ∑' n : ℕ, e n/(n : ℝ)^s) (𝓝[>] 1)
      (𝓝 (∑ n ∈ bad, e n/n)) := by
    simpa only [hEsum] using tendsto_finsetSum bad (fun n _ => hEterm n)
  have hseries (s : ℝ) (hs : 1 < s) :
      (∑' n : ℕ, (primeNormMultiplicity H n : ℝ)/(n : ℝ)^s) =
      m * (∑' n : ℕ, a n/(n : ℝ)^s) + (∑' n : ℕ, e n/(n : ℝ)^s) := by
    rw [← tsum_mul_left, ← ((hsa s hs).mul_left m).tsum_add (hse s)]
    apply tsum_congr
    intro n
    rw [hid n]
    ring
  refine ⟨hsa, ?_⟩
  obtain ⟨B, hB⟩ := primeNormMultiplicity_regularized_limit H
  refine ⟨(B-(∑ n ∈ bad, e n/n))/m, ?_⟩
  apply ((hB.sub hElim).div_const m).congr'
  filter_upwards [self_mem_nhdsWithin] with s hs
  rw [hseries s hs]
  field_simp [hm.ne']
  ring

end QuadraticMoat
