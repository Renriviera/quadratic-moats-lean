import QuadraticMoat.EntropyBand
import OAI.NumberTheory.GaussianMoat.BatchParameters

/-! Coverage parameter selection for native quadratic-field split sieves.
The original scalar package arithmetic, integer lengths, repetitions, and
asymptotic length bounds are reused through the OAI import.
-/

namespace QuadraticMoat
open NumberField OAI.GaussianMoat
open scoped BigOperators Classical
variable {Fld : Type*} [Field Fld] [NumberField Fld] [ctx : PlanarContext Fld]

theorem one_step_coverage (s : SplitSieve Fld) (D : ℝ) (N : ℕ)
    (mid bot : List ℕ) (b q n : ℕ) (e ebase : ℝ)
    (u : s.SignedIndex → ℝ)
    (hm : EntropyBand s D mid 0 b e)
    (hb : EntropyBand s D bot N q ebase)
    (hb0 : 0<b) (hbk : b≤ s.primes.card) (hq0 : 0<q) (hqk : q≤ s.primes.card)
    (hN : 1≤bot.sum+N) (hn : 0<n)
    (hprime : ∀ i, Real.exp 100≤(s.signedPrime i:ℝ))
    (hu : ∀ i, 0<u i)
    (hbase : ebase*s.meanLog≤Real.exp (-100)/(512*640000))
    (hgap : e*s.meanLog+n*(Real.log 36+2*Real.log (D*(bot.sum+N)))/b<1/256)
    (herr : ∀ i, (s.signedPrime i:ℝ)*Real.exp
      (-(n:ℝ)*(1/64)^2*u i/(2*(s.signedPrime i:ℝ)))≤1/640000) :
    CoverageDerivation s D N (mid++bot) (1/4) u (1/100) := by
  let c : ℝ := Real.exp (-100)/512
  let u' : s.SignedIndex → ℝ := fun i => Real.exp (-100)/64*(s.signedPrime i:ℝ)
  let C : s.SignedIndex → ℝ := fun i => Real.exp (-100)*(s.signedPrime i:ℝ)
  have hc : 0<c := by dsimp [c]; positivity
  have htail : CoverageDerivation s D N bot (1/4+4*(1/64)) u' (1/640000) := by
    apply CoverageDerivation.base bot q (1/4+4*(1/64)) c ebase (1/640000) u' hb hq0 hqk
    · norm_num
    · exact hc
    · intro i; dsimp [c,u']; ring_nf; exact le_rfl
    · apply (div_le_iff₀ hc).mpr
      dsimp [c]
      linarith only [hbase]
  apply CoverageDerivation.step mid bot b n (1/4) (1/64) (1/640000) (1/100)
    (1/640000) e 100 u u' C hm htail hN hn hb0 hbk
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · exact hu
  · norm_num
  · norm_num only [mul_one,one_mul,div_div]
    have hl2 : Real.log 2≤1 := by simpa only [show (2:ℝ)-1=1 by norm_num] using Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ)<2)
    have hl : Real.log (12800:ℝ)≤14 := by
      have hh := Real.log_le_log (by norm_num : (0:ℝ)<12800) (by norm_num : (12800:ℝ)≤2^14)
      rw [Real.log_pow] at hh
      norm_num at hh
      linarith only [hh,hl2]
    rw [show (1:ℝ)/12800=(12800:ℝ)⁻¹ by rw [one_div],Real.log_inv]
    linarith only [hl]
  · norm_num only [Nat.cast_ofNat] at hgap ⊢
    convert hgap using 1
  · intro i
    have hh := mul_le_mul_of_nonneg_left (hprime i) (Real.exp_nonneg (-100))
    dsimp [C]
    rw [←Real.exp_add] at hh
    norm_num at hh
    exact hh
  · intro i
    dsimp [C]
    rw [Real.log_mul (Real.exp_ne_zero _) (ne_of_gt ((Real.exp_pos 100).trans_le (hprime i))),Real.log_exp]
    linarith
  · intro i; dsimp [u',C]; ring_nf; exact le_rfl
  · exact herr


end QuadraticMoat
