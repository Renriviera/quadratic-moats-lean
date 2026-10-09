import QuadraticMoat.BoundedFactors.SoftBatchCertificate
import QuadraticMoat.BoundedFactors.Endpoint

namespace QuadraticMoat.BoundedFactors
open NumberField OAI.GaussianMoat
open scoped BigOperators Classical
variable {K : Type*} [Field K] [NumberField K] [ctx : PlanarContext K]

structure SieveCertificate (F : PrimeFamily)
    (hgood : ∀ p, F.good p → Nonempty (SplitPrime K p)) (D : ℝ) (B : ℕ) where
  schedule : List ℕ
  smoothing : ℕ
  batches : ℕ → ℕ
  last : ℕ
  batches_inj : Set.InjOn batches (Finset.range (last+1) : Set ℕ)
  lengths : ℕ → ℕ
  rates : ℕ → ℝ
  error : ℝ
  batch : ∀ j ≤ last, BatchCertificate D schedule smoothing
    (F.dyadicSieve hgood (batches j)) (lengths j)
    (residueWeight (precedingFactors (fun i => F.dyadicSieve hgood (batches i)) j)) (rates j)
  divides : ∀ j < last, lengths j ∣ lengths (j+1)
  nonneg : 0 ≤ error
  smooth : ∀ j < last, ∀ a < lengths (j+1), 2*Real.binEntropy ((a : ℝ)/(smoothing+1)) +
    ((a : ℝ)/(smoothing+1))*((lengths j : ℝ)*Real.log (planeBall (K := K) D).card +
      2*residueWeight (precedingFactors (fun i => F.dyadicSieve hgood (batches i)) (last+1))) ≤ error
  excess : Real.log (planeBall (K := K) D).card + last*error+B <
    ∑ j ∈ Finset.range (last+1), rates j

namespace SieveCertificate
variable {F : PrimeFamily} {hgood : ∀ p, F.good p → Nonempty (SplitPrime K p)}
    {D : ℝ} {B : ℕ}

noncomputable def factors (q : SieveCertificate F hgood D B) : Finset (𝓞 K) :=
  precedingFactors (fun j => F.dyadicSieve hgood (q.batches j)) (q.last+1)

noncomputable def period (q : SieveCertificate F hgood D B) : ℕ :=
  ∏ j ∈ Finset.range (q.last+1), (F.dyadicSieve hgood (q.batches j)).period

lemma period_pos (q : SieveCertificate F hgood D B) : 0 < q.period :=
  Finset.prod_pos (fun j _ => SplitSieve.period_pos _)

lemma primes_disjoint (q : SieveCertificate F hgood D B) :
    (Finset.range (q.last+1) : Set ℕ).Pairwise
      (fun i j => Disjoint (F.dyadicSieve hgood (q.batches i)).primes
        (F.dyadicSieve hgood (q.batches j)).primes) := by
  intro i hi j hj hij
  apply F.dyadicBatch_disjoint
  intro heq
  exact hij (q.batches_inj hi hj heq)

lemma factors_disjoint (q : SieveCertificate F hgood D B) :
    (Finset.range (q.last+1) : Set ℕ).Pairwise
      (fun i j => Disjoint (F.dyadicSieve hgood (q.batches i)).selectedFactors
        (F.dyadicSieve hgood (q.batches j)).selectedFactors) := by
  intro i hi j hj hij
  exact SplitSieve.selectedFactors_disjoint_of_primes_disjoint _ _ (q.primes_disjoint hi hj hij)

lemma factors_prime (q : SieveCertificate F hgood D B) :
    ∀ f ∈ q.factors, Prime f :=
  SplitSieve.biUnion_selectedFactors_prime _ _

lemma factors_coprime (q : SieveCertificate F hgood D B) :
    (q.factors : Set (𝓞 K)).Pairwise IsCoprime :=
  SplitSieve.biUnion_selectedFactors_pairwise_coprime _ _ q.primes_disjoint

lemma factors_hitCount_le_omega (q : SieveCertificate F hgood D B)
    {α : 𝓞 K} (hα : α ≠ 0) : finiteFactorHitCount q.factors α ≤ omega K α :=
  finiteFactorHitCount_le_omega q.factors_prime q.factors_coprime hα

lemma factor_dvd_period (q : SieveCertificate F hgood D B) :
    ∀ f ∈ q.factors, f ∣ (q.period : 𝓞 K) := by
  intro f hf
  obtain ⟨j, hj, hf⟩ := Finset.mem_biUnion.mp hf
  exact ((F.dyadicSieve hgood (q.batches j)).selectedFactor_dvd_period hf).trans
    (map_dvd (Nat.castRingHom (𝓞 K)) (Finset.dvd_prod_of_mem
      (fun j => (F.dyadicSieve hgood (q.batches j)).period) hj))

theorem sound (q : SieveCertificate F hgood D B) (hD : 1 ≤ D) (hDscale : ctx.scale ≤ D) :
    ∀ z : ℕ → 𝓞 K, (∀ t, z t ∈ finiteHitSieve q.factors B) → Function.Injective z →
      (∀ t, dist (z (t+1) : ℂ) (z t : ℂ) ≤ D) → False := by
  intro z ha hz hs
  exact certificate_no_walk hD hDscale q.schedule q.smoothing q.last
    (fun j => F.dyadicSieve hgood (q.batches j)) q.lengths q.rates B q.batch q.divides
    q.nonneg q.smooth q.factors_disjoint q.excess z hz ha
    (fun t => by simpa only [dist_comm] using hs t)

end SieveCertificate

/-- Planar hit-budget certificates imply the finite full-Minkowski sieve input. -/
theorem finiteHitNoWalkEndpoint_of_certificates
    (F : PrimeFamily) (hgood : ∀ p, F.good p → Nonempty (SplitPrime K p))
    (h : ∀ B : ℕ, ∀ D : ℝ, 1 ≤ D → ctx.scale ≤ D →
      Nonempty (SieveCertificate F hgood D B)) : FiniteHitNoWalkEndpoint K := by
  intro B D hD
  let E : ℝ := ctx.scale * coordinateStepBound ctx.basis D
  have hscale0 : 0 ≤ ctx.scale := (by norm_num : (0 : ℝ) ≤ 1).trans ctx.scale_ge_one
  have hSE : ctx.scale ≤ E := by
    dsimp only [E]
    simpa only [mul_one] using mul_le_mul_of_nonneg_left
      (coordinateStepBound_ge_one ctx.basis D) hscale0
  have hE : 1 ≤ E := ctx.scale_ge_one.trans hSE
  obtain ⟨q⟩ := h B E hE hSE
  refine ⟨q.factors, q.period, q.period_pos.ne', q.factors_prime,
    q.factors_coprime, q.factor_dvd_period, ?_⟩
  intro z hz hinj hstep
  apply q.sound hE hSE z hz hinj
  intro n
  change dist (scaledCoordinateComplex ctx.basis ctx.scale (z (n+1)))
    (scaledCoordinateComplex ctx.basis ctx.scale (z n)) ≤ E
  exact scaled_coordinate_dist_le_stepBound ctx.basis ctx.scale hscale0 D (hstep n)

end QuadraticMoat.BoundedFactors
