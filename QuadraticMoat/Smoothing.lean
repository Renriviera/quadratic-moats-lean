import QuadraticMoat.BatchParameters
import QuadraticMoat.AccurateScales
import OAI.NumberTheory.GaussianMoat.Smoothing

namespace QuadraticMoat
open NumberField OAI.GaussianMoat
open scoped BigOperators Classical
variable {Fld : Type*} [Field Fld] [NumberField Fld] [ctx : PlanarContext Fld]

theorem coverage_from_scalar_guards (s : SplitSieve Fld) (D X : ℝ) (N : ℕ)
    (mid bot : List ℕ) (b q : ℕ) (e : ℝ)
    (hm : EntropyBand s D mid 0 b e) (hb : EntropyBand s D bot N q e)
    (hmean : 0< s.meanLog) (hN : 1≤bot.sum+N)
    (hX : 100≤X)
    (hp : ∀ i, Real.exp X≤(s.signedPrime i:ℝ) ∧
      (s.signedPrime i:ℝ)≤2*Real.exp (21/20*X))
    (hbase : e*s.meanLog≤Real.exp (-100)/(512*640000))
    (hmid : e*s.meanLog≤1/1024)
    (hcost : (coverageRepetitions X:ℝ)*(Real.log 36+2*Real.log (D*(bot.sum+N)))/b≤1/1024)
    (hhazard : ∀ i, (s.signedPrime i:ℝ)*Real.exp
      (-(coverageRepetitions X:ℝ)*(1/64)^2*
        ((s.signedPrime i:ℝ)*Real.exp (-X/200))/(2*(s.signedPrime i:ℝ)))≤1/640000) :
    CoverageDerivation s D N (mid++bot) (1/4)
      (fun i => (s.signedPrime i:ℝ)*Real.exp (-X/200)) (1/100) := by
  exact one_step_coverage s D N mid bot b q (coverageRepetitions X) e e _ hm hb
    (hm.size_pos hmean) (hm.size_cap hmean) (hb.size_pos hmean) (hb.size_cap hmean)
    hN (coverageRepetitions_pos X)
    (fun i => (Real.exp_le_exp.mpr hX).trans (hp i).1)
    (fun i => mul_pos ((Real.exp_pos X).trans_le (hp i).1) (Real.exp_pos _)) hbase
    (by linarith only [hmid,hcost]) hhazard


end QuadraticMoat
