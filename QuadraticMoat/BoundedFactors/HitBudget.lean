import QuadraticMoat.BatchCertificate

namespace QuadraticMoat.BoundedFactors
open NumberField OAI.GaussianMoat
open scoped BigOperators Classical
variable {K : Type*} [Field K] [NumberField K]

/-- Charge all available factors against one common sampling law. -/
noncomputable def lawHitMass {Ω : Type*} [Fintype Ω] (p : FinLaw Ω)
    (Z : Ω → 𝓞 K) (A : Finset (𝓞 K)) : ℝ :=
  ∑ f ∈ A, p.prob (fun ω => f ∣ Z ω)

noncomputable def hitMass (P : TimeLaw) (z : ℕ → 𝓞 K) (A : Finset (𝓞 K)) : ℝ :=
  lawHitMass P.law (fun t => z t.val) A

lemma advance_hitMass (P : TimeLaw) (R : ForwardKernel) (z : ℕ → 𝓞 K)
    (A : Finset (𝓞 K)) :
    hitMass (P.advance R) z A = lawHitMass (P.law.joint (fun t => R.law t.val))
      (fun v => z (v.1.val+v.2.val)) A := by
  unfold hitMass lawHitMass TimeLaw.advance
  simp only [FinLaw.prob_map]
  rfl

lemma lawHitMass_nonneg {Ω : Type*} [Fintype Ω] (p : FinLaw Ω)
    (Z : Ω → 𝓞 K) (A : Finset (𝓞 K)) : 0 ≤ lawHitMass p Z A :=
  Finset.sum_nonneg (fun _ _ => p.prob_nonneg _)

lemma lawHitMass_eq_expected_count {Ω : Type*} [Fintype Ω] (p : FinLaw Ω)
    (Z : Ω → 𝓞 K) (A : Finset (𝓞 K)) :
    lawHitMass p Z A = ∑ ω, p ω * ((A.filter (fun f => f ∣ Z ω)).card : ℝ) := by
  unfold lawHitMass FinLaw.prob
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro ω _
  rw [← Finset.sum_boole]
  simp only [Finset.mul_sum, mul_ite, mul_one, mul_zero]

lemma lawHitMass_le {Ω : Type*} [Fintype Ω] (p : FinLaw Ω)
    (Z : Ω → 𝓞 K) (A : Finset (𝓞 K)) (b : ℕ)
    (hb : ∀ ω, (A.filter (fun f => f ∣ Z ω)).card ≤ b) :
    lawHitMass p Z A ≤ b := by
  rw [lawHitMass_eq_expected_count]
  have hh := Finset.sum_le_sum (s := Finset.univ) (fun ω _ =>
    mul_le_mul_of_nonneg_left (show ((A.filter (fun f => f ∣ Z ω)).card : ℝ) ≤ b by
      exact_mod_cast hb ω) (p.nonneg ω))
  simpa only [← Finset.sum_mul, p.sum_one, one_mul] using hh

lemma hitMass_sum_eq {ι : Type*} [DecidableEq ι] (P : TimeLaw) (z : ℕ → 𝓞 K)
    (J : Finset ι) (A : ι → Finset (𝓞 K))
    (hA : (J : Set ι).Pairwise (fun i j => Disjoint (A i) (A j))) :
    (∑ j ∈ J, hitMass P z (A j)) = hitMass P z (J.biUnion A) := by
  unfold hitMass lawHitMass
  exact (Finset.sum_biUnion hA).symm

lemma hitMass_sum_le {ι : Type*} [DecidableEq ι] (P : TimeLaw) (z : ℕ → 𝓞 K)
    (J : Finset ι) (A : ι → Finset (𝓞 K)) (b : ℕ)
    (hA : (J : Set ι).Pairwise (fun i j => Disjoint (A i) (A j)))
    (hb : ∀ t, ((J.biUnion A).filter (fun f => f ∣ z t)).card ≤ b) :
    (∑ j ∈ J, hitMass P z (A j)) ≤ b := by
  rw [hitMass_sum_eq P z J A hA]
  exact lawHitMass_le P.law (fun t => z t.val) _ b (fun t => hb t.val)

lemma selected_sum_le_lawHitMass {Ω ι : Type*} [Fintype Ω] [Fintype ι]
    (p : FinLaw Ω) (Z : Ω → 𝓞 K) (A : Finset (𝓞 K))
    (f : ι → 𝓞 K) (hf : Function.Injective f) (hmem : ∀ i, f i ∈ A) :
    (∑ i, p.prob (fun ω => f i ∣ Z ω)) ≤ lawHitMass p Z A := by
  change (∑ i ∈ Finset.univ, (fun f : 𝓞 K => p.prob (fun ω => f ∣ Z ω)) (f i)) ≤ _
  rw [← Finset.sum_image (s := Finset.univ) (g := f)
    (f := fun g : 𝓞 K => p.prob (fun ω => g ∣ Z ω)) (fun i _ j _ h => hf h)]
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · intro x hx
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hx
    exact hmem i
  · intro x _ _
    exact p.prob_nonneg _

end QuadraticMoat.BoundedFactors
