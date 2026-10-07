import QuadraticMoat.ZetaRegularization
import CebotarevDensity.Density

/-!
# Strong regularization of the full prime-ideal zeta series

The logarithmic Euler identity and indexing helpers below adapt the private
lemmas in AINTLIB `CebotarevDensity.Density` (CBirkbeck/AINTLIB pin
160e446617a2168c34c95bbe7a76c4105b392434). The public Euler product is the
input; the new conclusion is a finite regularized limit, not just boundedness.
-/

namespace QuadraticMoat
open Filter Topology NumberField Set

abbrev NonzeroPrimeIdeal (K : Type*) [Field K] [NumberField K] :=
  {P : Ideal (𝓞 K) // P.IsPrime ∧ P ≠ ⊥}

variable (K : Type*) [Field K] [NumberField K]

lemma summable_nonzeroPrime_absNorm_rpow {s : ℝ} (hs : 1 < s) :
    Summable (fun P : NonzeroPrimeIdeal K => (Ideal.absNorm P.1 : ℝ)^(-s)) :=
  ((Chebotarev.summable_prime_absNorm_rpow (univ : Set (Ideal (𝓞 K))) hs).comp_injective
    (Equiv.subtypeEquivRight fun _ => ⟨(⟨mem_univ _, ·⟩), And.right⟩).injective).congr
      fun _ => rfl

lemma nonzeroPrime_two_le_absNorm (P : NonzeroPrimeIdeal K) :
    (2 : ℝ) ≤ Ideal.absNorm P.1 := by
  exact_mod_cast (Nat.two_le_iff _).2
    ⟨mt Ideal.absNorm_eq_zero_iff.1 P.2.2,
      mt Ideal.absNorm_eq_one_iff.1 P.2.1.ne_top⟩

lemma primeIdealZetaSum_univ_reindex (s : ℝ) :
    Chebotarev.primeIdealZetaSum (univ : Set (Ideal (𝓞 K))) s =
      ∑' P : NonzeroPrimeIdeal K, (Ideal.absNorm P.1 : ℝ)^(-s) := by
  rw [Chebotarev.primeIdealZetaSum_def, ← (Equiv.subtypeEquivRight fun P =>
    ⟨fun h => ⟨mem_univ _, h⟩, And.right⟩).tsum_eq _]
  rfl

lemma nonzeroPrime_norm_factor_lt_one (P : NonzeroPrimeIdeal K)
    {s : ℝ} (hs : 1 < s) : (Ideal.absNorm P.1 : ℝ)^(-s) < 1 :=
  Real.rpow_lt_one_of_one_lt_of_neg
    (by linarith [nonzeroPrime_two_le_absNorm K P]) (by linarith)

lemma summable_nonzeroPrime_logFactor {s : ℝ} (hs : 1 < s) :
    Summable (fun P : NonzeroPrimeIdeal K =>
      -Real.log (1-(Ideal.absNorm P.1 : ℝ)^(-s))) :=
  ((Real.summable_log_one_add_of_summable
    (summable_nonzeroPrime_absNorm_rpow K hs).neg).neg).congr fun _ => rfl

lemma log_dedekindZeta_re_eq_prime_logs {s : ℝ} (hs : 1 < s) :
    Real.log (dedekindZeta K (s : ℂ)).re =
      ∑' P : NonzeroPrimeIdeal K, -Real.log (1-(Ideal.absNorm P.1 : ℝ)^(-s)) := by
  let g : NonzeroPrimeIdeal K → ℝ :=
    fun P => (1-(Ideal.absNorm P.1 : ℝ)^(-s))⁻¹
  have hgpos : ∀ P, 0 < g P := fun P =>
    inv_pos.mpr (sub_pos.mpr (nonzeroPrime_norm_factor_lt_one K P hs))
  have hlogsum : Summable (fun P => Real.log (g P)) :=
    (summable_nonzeroPrime_logFactor K hs).congr fun P => by
      simp only [g, Real.log_inv]
  have hCprod : HasProd (fun P : NonzeroPrimeIdeal K =>
      (1-(Ideal.absNorm P.1 : ℂ)^(-(s : ℂ)))⁻¹)
      ((Real.exp (∑' P, Real.log (g P)) : ℝ) : ℂ) := by
    refine ((Real.hasProd_of_hasSum_log hgpos hlogsum.hasSum).map Complex.ofRealHom
      Complex.continuous_ofReal).congr_fun fun P => ?_
    rw [Function.comp_apply, Complex.ofRealHom_eq_coe]
    dsimp [g]
    push_cast [Complex.ofReal_cpow (show (0 : ℝ) ≤ Ideal.absNorm P.1 by positivity)]
    ring
  have hre : (dedekindZeta K (s : ℂ)).re = Real.exp (∑' P, Real.log (g P)) := by
    rw [Chebotarev.dedekindZeta_eq_tprod_primeIdeal K (by simpa using hs),
      hCprod.tprod_eq, Complex.ofReal_re]
  rw [hre, Real.log_exp]
  exact tsum_congr fun P => by simp only [g, Real.log_inv]

/-- The full unweighted prime-ideal series has an actual finite
regularized limit at one. This is stronger than Dirichlet density. -/
theorem all_primeIdeal_regularized_limit :
    ∃ B : ℝ, Tendsto (fun s : ℝ =>
      Chebotarev.primeIdealZetaSum (univ : Set (Ideal (𝓞 K))) s -
        Real.log (1/(s-1))) (𝓝[>] 1) (𝓝 B) := by
  let R : ℝ → ℝ := fun s => ∑' P : NonzeroPrimeIdeal K,
    (-Real.log (1-(Ideal.absNorm P.1 : ℝ)^(-s))-(Ideal.absNorm P.1 : ℝ)^(-s))
  let R₁ : ℝ := ∑' P : NonzeroPrimeIdeal K,
    (-Real.log (1-(Ideal.absNorm P.1 : ℝ)⁻¹)-(Ideal.absNorm P.1 : ℝ)⁻¹)
  have hR : Tendsto R (𝓝[>] 1) (𝓝 R₁) :=
    norm_euler_remainder_tsum_limit (fun P : NonzeroPrimeIdeal K =>
      (Ideal.absNorm P.1 : ℝ)) (nonzeroPrime_two_le_absNorm K)
      (summable_nonzeroPrime_absNorm_rpow K (by norm_num : (1 : ℝ) < 2))
  refine ⟨Real.log (dedekindZeta_residue K)-R₁, ?_⟩
  apply ((log_dedekindZeta_regularized_limit K).sub hR).congr'
  filter_upwards [self_mem_nhdsWithin] with s hs
  have heq : R s = Real.log (dedekindZeta K (s : ℂ)).re -
      Chebotarev.primeIdealZetaSum (univ : Set (Ideal (𝓞 K))) s := by
    rw [log_dedekindZeta_re_eq_prime_logs K hs, primeIdealZetaSum_univ_reindex K,
      ← (summable_nonzeroPrime_logFactor K hs).tsum_sub
        (summable_nonzeroPrime_absNorm_rpow K hs)]
  rw [heq]
  ring

end QuadraticMoat
