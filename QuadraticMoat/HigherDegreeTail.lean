import QuadraticMoat.PrimeIdealRegularization
import CebotarevDensity.AbsoluteDegreeOneDensity

/-!
# Actual convergence of the higher-degree prime-ideal contribution

AINTLIB's absolute-degree-one density helper bounds this contribution
uniformly for s>1. Finite sums pass to the boundary to prove summability
at s=1; dominated convergence then upgrades boundedness to an actual limit.
-/

namespace QuadraticMoat
open Filter Topology NumberField Set

abbrev HigherDegreePrimeIdeal (K : Type*) [Field K] [NumberField K] :=
  {P : Ideal (𝓞 K) // ¬P.absNorm.Prime ∧ P.IsPrime ∧ P ≠ ⊥}

variable (K : Type*) [Field K] [NumberField K]

lemma summable_higherDegree_absNorm_rpow {s : ℝ} (hs : 1 < s) :
    Summable (fun P : HigherDegreePrimeIdeal K => (P.1.absNorm : ℝ)^(-s)) := by
  simpa only [mem_ofPred_eq] using
    (Chebotarev.summable_prime_absNorm_rpow {P : Ideal (𝓞 K) | ¬P.absNorm.Prime} hs)

lemma higherDegree_series_bound {s : ℝ} (hs : 1 < s) :
    (∑' P : HigherDegreePrimeIdeal K, (P.1.absNorm : ℝ)^(-s)) ≤
      (Module.finrank ℚ K : ℝ) * ∑' n : ℕ, (n : ℝ)^(-2 : ℝ) := by
  have hset : {P : Ideal (𝓞 K) | P ∈ (univ : Set (Ideal (𝓞 K))) ∧ ¬P.absNorm.Prime} =
      {P : Ideal (𝓞 K) | ¬P.absNorm.Prime} := by
    ext P
    constructor
    · exact fun h => h.2
    · exact fun h => ⟨Set.mem_univ P, h⟩
  have hbound := Chebotarev.primeIdealZetaSum_nonprimeNorm_le (univ : Set (Ideal (𝓞 K))) hs
  rw [hset] at hbound
  simpa only [Chebotarev.primeIdealZetaSum, mem_ofPred_eq] using hbound

lemma higherDegree_norm_pos (P : HigherDegreePrimeIdeal K) :
    (0 : ℝ) < P.1.absNorm := by
  have h := nonzeroPrime_two_le_absNorm K ⟨P.1, P.2.2⟩
  linarith

lemma higherDegree_term_limit (P : HigherDegreePrimeIdeal K) :
    Tendsto (fun s : ℝ => (P.1.absNorm : ℝ)^(-s)) (𝓝[>] 1)
      (𝓝 ((P.1.absNorm : ℝ)⁻¹)) := by
  have ht : Tendsto (fun s : ℝ => -s) (𝓝[>] 1) (𝓝 (-1 : ℝ)) :=
    tendsto_id.neg.mono_left nhdsWithin_le_nhds
  simpa only [Function.comp_def, Real.rpow_neg_one] using
    (Real.continuousAt_const_rpow (higherDegree_norm_pos K P).ne').tendsto.comp ht

/-- The inverse norms of prime ideals of absolute degree at least two form
a summable series. -/
theorem summable_higherDegree_inverseNorm :
    Summable (fun P : HigherDegreePrimeIdeal K => (P.1.absNorm : ℝ)⁻¹) := by
  apply summable_of_sum_le (fun P => inv_nonneg.mpr (higherDegree_norm_pos K P).le)
  intro t
  have ht := tendsto_finsetSum t (fun P _ => higherDegree_term_limit K P)
  apply le_of_tendsto ht
  filter_upwards [self_mem_nhdsWithin] with s hs
  exact ((summable_higherDegree_absNorm_rpow K hs).sum_le_tsum t
    (fun P _ => Real.rpow_nonneg (higherDegree_norm_pos K P).le _)).trans
      (higherDegree_series_bound K hs)

/-- Higher-degree prime ideals contribute a finite convergent error to the
regularized prime-ideal zeta series, stronger than a zero density ratio. -/
theorem higherDegree_primeIdeal_series_limit :
    Tendsto (fun s : ℝ => ∑' P : HigherDegreePrimeIdeal K,
      (P.1.absNorm : ℝ)^(-s)) (𝓝[>] 1)
      (𝓝 (∑' P : HigherDegreePrimeIdeal K, (P.1.absNorm : ℝ)⁻¹)) := by
  apply tendsto_tsum_of_dominated_convergence (summable_higherDegree_inverseNorm K)
    (higherDegree_term_limit K)
  filter_upwards [self_mem_nhdsWithin] with s hs P
  have hs' : 1 < s := hs
  rw [Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg (higherDegree_norm_pos K P).le _),
    ← Real.rpow_neg_one]
  exact Real.rpow_le_rpow_of_exponent_le
    (by linarith [nonzeroPrime_two_le_absNorm K ⟨P.1, P.2.2⟩]) (by linarith)


/-- The contribution from prime ideals whose absolute norm is a rational
prime retains a finite logarithmic regularization with coefficient one. -/
theorem primeNorm_primeIdeal_regularized_limit :
    ∃ B : ℝ, Tendsto (fun s : ℝ =>
      Chebotarev.primeIdealZetaSum {P : Ideal (𝓞 K) | P.absNorm.Prime} s -
        Real.log (1/(s-1))) (𝓝[>] 1) (𝓝 B) := by
  obtain ⟨B, hB⟩ := all_primeIdeal_regularized_limit K
  let T : Set (Ideal (𝓞 K)) := {P | P.absNorm.Prime}
  let U : Set (Ideal (𝓞 K)) := {P | ¬P.absNorm.Prime}
  have hU : Tendsto (fun s : ℝ => Chebotarev.primeIdealZetaSum U s)
      (𝓝[>] 1) (𝓝 (∑' P : HigherDegreePrimeIdeal K, (P.1.absNorm : ℝ)⁻¹)) := by
    simpa only [Chebotarev.primeIdealZetaSum, U, mem_ofPred_eq] using
      higherDegree_primeIdeal_series_limit K
  refine ⟨B-(∑' P : HigherDegreePrimeIdeal K, (P.1.absNorm : ℝ)⁻¹), ?_⟩
  apply (hB.sub hU).congr'
  filter_upwards [self_mem_nhdsWithin] with s hs
  have hdisj : Disjoint T U := by
    rw [Set.disjoint_left]
    exact fun P ht hu => hu ht
  have hunion : T ∪ U = univ := by
    ext P
    simp only [T, U, Set.mem_union, mem_ofPred_eq, mem_univ, iff_true]
    exact em _
  have heq : Chebotarev.primeIdealZetaSum (univ : Set (Ideal (𝓞 K))) s =
      Chebotarev.primeIdealZetaSum T s + Chebotarev.primeIdealZetaSum U s := by
    rw [← hunion, Chebotarev.primeIdealZetaSum_union_of_disjoint hdisj hs]
  rw [heq]
  dsimp [T]
  ring

end QuadraticMoat
