import QuadraticMoat.HigherDegreeTail
import QuadraticMoat.PrimeMoments

namespace QuadraticMoat
open Filter Topology NumberField Set

abbrev PrimeNormIdeal (K : Type*) [Field K] [NumberField K] :=
  {P : Ideal (𝓞 K) // P.absNorm.Prime ∧ P.IsPrime ∧ P ≠ ⊥}

noncomputable def primeNormMultiplicity (K : Type*) [Field K] [NumberField K] (n : ℕ) : ℕ :=
  Nat.card {P : PrimeNormIdeal K // P.1.absNorm = n}

variable (K : Type*) [Field K] [NumberField K]

lemma summable_primeNorm_absNorm_rpow {s : ℝ} (hs : 1 < s) :
    Summable (fun P : PrimeNormIdeal K => (P.1.absNorm : ℝ)^(-s)) := by
  simpa only [mem_ofPred_eq] using
    (Chebotarev.summable_prime_absNorm_rpow {P : Ideal (𝓞 K) | P.absNorm.Prime} hs)

lemma primeNormMultiplicity_zero_of_not_prime {n : ℕ} (hn : ¬n.Prime) :
    primeNormMultiplicity K n = 0 := by
  have hempty : IsEmpty {P : PrimeNormIdeal K // P.1.absNorm = n} :=
    ⟨fun P => hn (P.2 ▸ P.1.2.1)⟩
  let := hempty
  exact Nat.card_of_isEmpty

lemma primeNorm_fiber_sum (s : ℝ) (n : ℕ) :
    (∑' P : {P : PrimeNormIdeal K // P.1.absNorm = n},
      (P.1.1.absNorm : ℝ)^(-s)) =
      (primeNormMultiplicity K n : ℝ) * (n : ℝ)^(-s) := by
  calc
    _ = ∑' _P : {P : PrimeNormIdeal K // P.1.absNorm = n}, (n : ℝ)^(-s) :=
      tsum_congr fun P => by rw [P.2]
    _ = _ := by rw [tsum_const, nsmul_eq_mul]; rfl

/-- Reindex prime ideals of rational-prime norm by that rational prime.
The coefficient is the exact native cardinality of the norm fiber. -/
lemma primeNorm_series_reindex {s : ℝ} (hs : 1 < s) :
    Chebotarev.primeIdealZetaSum {P : Ideal (𝓞 K) | P.absNorm.Prime} s =
      ∑' n : ℕ, (primeNormMultiplicity K n : ℝ) * (n : ℝ)^(-s) := by
  have h := (summable_primeNorm_absNorm_rpow K hs).hasSum.tsum_fiberwise
    (fun P : PrimeNormIdeal K => P.1.absNorm)
  have hf : (fun n : ℕ => ∑' P : {P : PrimeNormIdeal K // P.1.absNorm = n},
      (P.1.1.absNorm : ℝ)^(-s)) =
      (fun n : ℕ => (primeNormMultiplicity K n : ℝ) * (n : ℝ)^(-s)) := by
    funext n
    exact primeNorm_fiber_sum K s n
  change HasSum (fun n : ℕ => ∑' P : {P : PrimeNormIdeal K // P.1.absNorm = n},
    (P.1.1.absNorm : ℝ)^(-s)) _ at h
  rw [hf] at h
  simpa only [Chebotarev.primeIdealZetaSum, mem_ofPred_eq] using h.tsum_eq.symm

lemma summable_primeNormMultiplicity {s : ℝ} (hs : 1 < s) :
    Summable (fun n : ℕ => (primeNormMultiplicity K n : ℝ) * (n : ℝ)^(-s)) := by
  have h := (summable_primeNorm_absNorm_rpow K hs).hasSum.tsum_fiberwise
    (fun P : PrimeNormIdeal K => P.1.absNorm)
  change HasSum (fun n : ℕ => ∑' P : {P : PrimeNormIdeal K // P.1.absNorm = n},
    (P.1.1.absNorm : ℝ)^(-s)) _ at h
  exact h.summable.congr (fun n => primeNorm_fiber_sum K s n)


lemma primeNorm_series_div_reindex {s : ℝ} (hs : 1 < s) :
    Chebotarev.primeIdealZetaSum {P : Ideal (𝓞 K) | P.absNorm.Prime} s =
      ∑' n : ℕ, (primeNormMultiplicity K n : ℝ) / (n : ℝ)^s := by
  rw [primeNorm_series_reindex K hs]
  apply tsum_congr
  intro n
  rw [Real.rpow_neg (Nat.cast_nonneg n), div_eq_mul_inv]

lemma summable_primeNormMultiplicity_div {s : ℝ} (hs : 1 < s) :
    Summable (fun n : ℕ => (primeNormMultiplicity K n : ℝ) / (n : ℝ)^s) := by
  apply (summable_primeNormMultiplicity K hs).congr
  intro n
  rw [Real.rpow_neg (Nat.cast_nonneg n), div_eq_mul_inv]

/-- The rational norm multiplicity series retains coefficient one at the
logarithmic singularity. -/
theorem primeNormMultiplicity_regularized_limit :
    ∃ B : ℝ, Tendsto (fun s : ℝ =>
      (∑' n : ℕ, (primeNormMultiplicity K n : ℝ)/(n : ℝ)^s) -
        Real.log (1/(s-1))) (𝓝[>] 1) (𝓝 B) := by
  obtain ⟨B, hB⟩ := primeNorm_primeIdeal_regularized_limit K
  refine ⟨B, hB.congr' ?_⟩
  filter_upwards [self_mem_nhdsWithin] with s hs
  rw [primeNorm_series_div_reindex K hs]

/-- Every number field supplies positive logarithmic window mass through
its prime ideals of rational-prime norm, counted with native multiplicity. -/
theorem eventually_primeNormMultiplicity_window_mass :
    ∃ c : ℝ, 0 < c ∧ ∀ᶠ X : ℝ in atTop,
      c*X ≤ ∑ n ∈ OAI.GaussianMoat.PrimeLogMass.windowIndices X,
        (primeNormMultiplicity K n : ℝ) * Real.log n / n := by
  obtain ⟨B, hB⟩ := primeNormMultiplicity_regularized_limit K
  apply eventually_log_window_mass_of_regularization
    (fun n => (primeNormMultiplicity K n : ℝ))
    (by rw [primeNormMultiplicity_zero_of_not_prime K (by norm_num : ¬Nat.Prime 0)]; simp)
    (fun n => Nat.cast_nonneg _) (fun s hs => summable_primeNormMultiplicity_div K hs)
    1 B (by norm_num)
  simpa only [one_mul] using hB


lemma primeNorm_fiber_finite (n : ℕ) :
    Finite {P : PrimeNormIdeal K // P.1.absNorm = n} := by
  let : Finite {I : Ideal (𝓞 K) // I.absNorm = n} :=
    (Ideal.finite_setOfPred_absNorm_eq (S := 𝓞 K) n).to_subtype
  let f : {P : PrimeNormIdeal K // P.1.absNorm = n} →
      {I : Ideal (𝓞 K) // I.absNorm = n} := fun P => ⟨P.1.1, P.2⟩
  apply Finite.of_injective f
  intro P Q h
  apply Subtype.ext
  apply Subtype.ext
  exact congrArg (fun I : {I : Ideal (𝓞 K) // I.absNorm = n} => I.1) h

open OAI.GaussianMoat.PrimeLogMass in
lemma eventually_window_avoids_finset (bad : Finset ℕ) :
    ∀ᶠ X : ℝ in atTop, ∀ n ∈ windowIndices X, n ∉ bad := by
  have ht : Tendsto (fun X : ℝ => Real.exp (1001/1000*X)) atTop atTop :=
    Real.tendsto_exp_atTop.comp (Filter.Tendsto.const_mul_atTop (by norm_num) tendsto_id)
  have he : ∀ᶠ X : ℝ in atTop, ∀ n ∈ bad, (n : ℝ) < Real.exp (1001/1000*X) := by
    rw [eventually_all_finset]
    intro n _
    exact ht.eventually (eventually_gt_atTop (n : ℝ))
  filter_upwards [he] with X hX n hn hnbad
  exact (not_le_of_gt (hX n hnbad)) ((mem_windowIndices X n).mp hn).1

open OAI.GaussianMoat.PrimeLogMass in
/-- A norm-fiber multiplicity formula outside finitely many rational
primes transfers the unconditional field window mass to its split-prime
indicator. This lemma has only an arithmetic counting hypothesis. -/
theorem eventually_window_mass_of_norm_fiber_formula (m : ℝ) (hm : 0 < m)
    (a : ℕ → ℝ) (bad : Finset ℕ)
    (hcount : ∀ n : ℕ, n ∉ bad → (primeNormMultiplicity K n : ℝ) = m * a n) :
    ∃ c : ℝ, 0 < c ∧ ∀ᶠ X : ℝ in atTop,
      c*X ≤ ∑ n ∈ windowIndices X, a n * Real.log n / n := by
  obtain ⟨c, hc, he⟩ := eventually_primeNormMultiplicity_window_mass K
  refine ⟨c/m, div_pos hc hm, ?_⟩
  filter_upwards [he, eventually_window_avoids_finset bad] with X hX havoid
  have hid : (∑ n ∈ windowIndices X, (primeNormMultiplicity K n : ℝ) *
      Real.log n / n) = m * ∑ n ∈ windowIndices X, a n * Real.log n / n := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro n hn
    rw [hcount n (havoid n hn)]
    ring
  rw [hid] at hX
  rw [div_mul_eq_mul_div]
  apply (div_le_iff₀ hm).mpr
  simpa only [mul_comm] using hX

end QuadraticMoat
