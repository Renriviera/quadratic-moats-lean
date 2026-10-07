import QuadraticMoat.BatchCertificate
import QuadraticMoat.WindowParameters
import OAI.NumberTheory.GaussianMoat.SeparatedParameters

namespace QuadraticMoat
open NumberField OAI.GaussianMoat
open scoped BigOperators Classical
variable {Fld : Type*} [Field Fld] [NumberField Fld] [ctx : PlanarContext Fld]

lemma precedingFactors_enum_subset (F : PrimeFamily) (hgood : ∀ p, F.good p → Nonempty (SplitPrime Fld p)) (J : Finset ℕ) {n : ℕ} (hn : n<J.card) :
    precedingFactors (fun k => F.dyadicSieve hgood (binEnum J k)) n⊆
      (J.filter (·<binEnum J n)).biUnion (fun j => (F.dyadicSieve hgood j).selectedFactors) := by
  intro f hf
  obtain ⟨k,hk,hf⟩ := Finset.mem_biUnion.mp hf
  have hk' := Finset.mem_range.mp hk
  apply Finset.mem_biUnion.mpr
  exact ⟨binEnum J k,Finset.mem_filter.mpr ⟨binEnum_mem J (hk'.trans hn),binEnum_strictMono J hk' hn⟩,hf⟩

lemma precedingFactors_enum_cost (F : PrimeFamily) (hgood : ∀ p, F.good p → Nonempty (SplitPrime Fld p)) (J : Finset ℕ) {K n : ℕ} (hK : 0<K) (hn : n<J.card)
    (hsep : ∀ a∈J, ∀ b∈J, a<b → a+K≤b) :
    residueWeight (precedingFactors (fun k => F.dyadicSieve hgood (binEnum J k)) n)≤
      (4*Real.log 4/((2:ℝ)^K-1))*(2:ℝ)^(binEnum J n) := by
  apply (residueWeight_mono (precedingFactors_enum_subset F hgood J hn)).trans
  apply separated_factor_cost F hgood _ hK
  · intro a ha b hb hab
    exact hsep a (Finset.mem_filter.mp ha).1 b (Finset.mem_filter.mp hb).1 hab
  · intro a ha
    exact hsep a (Finset.mem_filter.mp ha).1 (binEnum J n) (binEnum_mem J hn) (Finset.mem_filter.mp ha).2

lemma precedingFactors_enum_all (F : PrimeFamily) (hgood : ∀ p, F.good p → Nonempty (SplitPrime Fld p)) (J : Finset ℕ) :
    precedingFactors (fun k => F.dyadicSieve hgood (binEnum J k)) J.card=
      J.biUnion (fun j => (F.dyadicSieve hgood j).selectedFactors) := by
  ext f
  constructor
  · intro hf
    obtain ⟨k,hk,hf⟩ := Finset.mem_biUnion.mp hf
    exact Finset.mem_biUnion.mpr ⟨binEnum J k,binEnum_mem J (Finset.mem_range.mp hk),hf⟩
  · intro hf
    obtain ⟨j,hj,hf⟩ := Finset.mem_biUnion.mp hf
    obtain ⟨n,hn,he⟩ := binEnum_surj J hj
    exact Finset.mem_biUnion.mpr ⟨n,Finset.mem_range.mpr hn,by simpa only [he] using hf⟩


end QuadraticMoat
