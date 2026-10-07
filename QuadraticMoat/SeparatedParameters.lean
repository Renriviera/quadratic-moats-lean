import QuadraticMoat.DenseBins
import OAI.NumberTheory.GaussianMoat.SeparatedParameters

/-! Generic parameter selection for supplied rational-prime families.

The original scalar schedule and block APIs are reused without modification.
Only the supplied dyadic prime batches enter the theorem below.
-/

namespace QuadraticMoat.PrimeFamily
open OAI.GaussianMoat
open scoped BigOperators Classical
open Filter

theorem exists_separated_parameters (F : PrimeFamily) : ∃ a δ t : ℝ, ∃ K : ℕ,
    0<a ∧ a≤1 ∧ 2*a≤δ ∧ 0<t ∧ 0<K ∧
    a≤(2:ℝ)^K*topCoefficient a ∧
    4*Real.log 4/((2:ℝ)^K-1)≤(topCoefficient a/4)/10000 ∧
    ∀ᶠ X : ℝ in atTop, ∃ J : Finset ℕ,
      t*X≤J.card ∧ (∀ i∈J, ∀ j∈J, i<j → i+K≤j) ∧
      ∀ j∈J, X≤j*Real.log 2 ∧ j*Real.log 2≤21/20*X ∧
        δ*(2:ℝ)^j/Real.log ((2:ℝ)^(j+1))≤(dyadicBatch F j).card := by
  obtain ⟨c,δ,hc,hδ,he⟩ := eventually_dense_split_bins F
  let a := min (δ/4) 1
  have ha : 0<a := lt_min (by positivity) (by norm_num)
  have ha1 : a≤1 := min_le_right _ _
  have haδ : 2*a≤δ := by have := min_le_left (δ/4) 1; dsimp only [a]; linarith only [this,hδ]
  have hv : 0<topCoefficient a := topCoefficient_pos ha
  have powtop := tendsto_pow_atTop_atTop_of_one_lt (by norm_num : (1:ℝ)<2)
  have hn := powtop.eventually (eventually_ge_atTop (max (a/topCoefficient a) (1+160000*Real.log 4/topCoefficient a)))
  obtain ⟨K,hK,hpow⟩ := (eventually_gt_atTop 0 |>.and hn).exists
  have hlo := (le_max_left _ _).trans hpow
  have hhi := (le_max_right _ _).trans hpow
  have hgap : a≤(2:ℝ)^K*topCoefficient a := (div_le_iff₀ hv).mp hlo
  have hden : 0<(2:ℝ)^K-1 := by
    have := one_lt_pow₀ (by norm_num : (1:ℝ)<2) (by omega : K≠0)
    linarith only [this]
  have hcost : 4*Real.log 4/((2:ℝ)^K-1)≤(topCoefficient a/4)/10000 := by
    have hh : 160000*Real.log 4≤((2:ℝ)^K-1)*topCoefficient a := by
      apply (div_le_iff₀ hv).mp
      linarith only [hhi]
    apply (div_le_iff₀ hden).mpr
    nlinarith only [hh]
  refine ⟨a,δ,c/K,K,ha,ha1,haδ,div_pos hc (by exact_mod_cast hK),hK,hgap,hcost,?_⟩
  filter_upwards [he] with X hX
  obtain ⟨J,hJ,hp⟩ := hX
  obtain ⟨b,_,hcard,hsep⟩ := thin_bins J hK
  refine ⟨J.filter (fun j => j%K=b),?_,hsep,?_⟩
  · have hh := (div_le_div_of_nonneg_right hJ (Nat.cast_nonneg K)).trans hcard
    simpa only [div_mul_eq_mul_div] using hh
  · intro j hj
    exact hp j (Finset.mem_filter.mp hj).1


end QuadraticMoat.PrimeFamily
