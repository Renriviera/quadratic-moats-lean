import QuadraticMoat.HilbertSplit
import QuadraticMoat.FiniteFiberTransfer
import QuadraticMoat.DenseBins
import ClassFieldTheory.Theorems.FrobeniusAndHilbertClassFields.SmallHilbertClassFieldExists

/-! Unconditional supplied principal-split prime families in quadratic fields. -/

namespace QuadraticMoat
open Filter Topology
open scoped NumberField BigOperators Classical

noncomputable def principalSplitCoefficient (K : Type) [Field K] [NumberField K]
    (p : ℕ) : ℝ := if Nonempty (SplitPrime K p) then 1 else 0

theorem principalSplitCoefficient_nonneg (K : Type) [Field K] [NumberField K]
    (p : ℕ) : 0 ≤ principalSplitCoefficient K p := by
  unfold principalSplitCoefficient
  split_ifs <;> norm_num

@[simp] theorem principalSplitCoefficient_zero (K : Type) [Field K] [NumberField K] :
    principalSplitCoefficient K 0 = 0 := by
  have h : ¬ Nonempty (SplitPrime K 0) := by
    rintro ⟨P⟩
    exact (by norm_num : ¬ Nat.Prime 0) P.prime
  simp [principalSplitCoefficient, h]

/-- Strong regularization of the principal-split rational-prime series in a
quadratic number field; its pole coefficient is the inverse absolute degree
of a small Hilbert class field. -/
theorem principalSplit_regularized_limit
    (K : Type) [Field K] [NumberField K] (hdegree : Module.finrank ℚ K = 2) :
    ∃ δ : ℝ, 0 < δ ∧
      (∀ s : ℝ, 1 < s → Summable (fun n : ℕ => principalSplitCoefficient K n/(n : ℝ)^s)) ∧
      ∃ B : ℝ, Tendsto (fun s : ℝ =>
        (∑' n : ℕ, principalSplitCoefficient K n/(n : ℝ)^s) -
          δ * Real.log (1/(s-1))) (𝓝[>] 1) (𝓝 B) := by
  obtain ⟨E,hE⟩ := ClassFieldTheory.exists_smallHilbertClassField K
  have hm : 0 < (Module.finrank ℚ E : ℝ) := by
    exact_mod_cast (Module.finrank_pos : 0 < Module.finrank ℚ E)
  obtain ⟨hs, B, hB⟩ := regularized_limit_of_norm_fiber_formula E
    (Module.finrank ℚ E : ℝ) hm (principalSplitCoefficient K)
    (principalSplitCoefficient_zero K) (discriminantDivisors K)
    (fun n hn => smallHilbert_primeNormMultiplicity_real_off_discriminant K E hE hdegree hn)
  exact ⟨(Module.finrank ℚ E : ℝ)⁻¹, inv_pos.mpr hm, hs, B, hB⟩

/-- Quantitative mass in the fixed exponential windows used by the sieve,
with no class-number or prime-supply assumption. -/
theorem principalSplit_window_mass
    (K : Type) [Field K] [NumberField K] (hdegree : Module.finrank ℚ K = 2) :
    ∃ c : ℝ, 0 < c ∧ ∀ᶠ X : ℝ in atTop,
      c*X ≤ ∑ p ∈ primeWindow (fun p => Nonempty (SplitPrime K p)) X, Real.log p/p := by
  obtain ⟨E,hE⟩ := ClassFieldTheory.exists_smallHilbertClassField K
  have hm : 0 < (Module.finrank ℚ E : ℝ) := by
    exact_mod_cast (Module.finrank_pos : 0 < Module.finrank ℚ E)
  obtain ⟨c,hc,he⟩ := eventually_window_mass_of_norm_fiber_formula E
    (Module.finrank ℚ E : ℝ) hm (principalSplitCoefficient K) (discriminantDivisors K)
    (fun n hn => smallHilbert_primeNormMultiplicity_real_off_discriminant K E hE hdegree hn)
  refine ⟨c,hc,?_⟩
  filter_upwards [he] with X hX
  simpa [primeWindow, principalSplitCoefficient, Finset.sum_filter, ite_div] using hX

/-- The native principal-split family available to every quadratic number
field. Its only extra argument records the quadratic degree. -/
noncomputable def principalSplitPrimeFamily
    (K : Type) [Field K] [NumberField K] (hdegree : Module.finrank ℚ K = 2) : PrimeFamily where
  good p := Nonempty (SplitPrime K p)
  prime_of_good p h := h.elim fun P => P.prime
  window_mass := principalSplit_window_mass K hdegree

@[simp] theorem principalSplitPrimeFamily_good
    (K : Type) [Field K] [NumberField K] (hdegree : Module.finrank ℚ K = 2) (p : ℕ) :
    (principalSplitPrimeFamily K hdegree).good p ↔ Nonempty (SplitPrime K p) := Iff.rfl

end QuadraticMoat
