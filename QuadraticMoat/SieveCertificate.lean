import QuadraticMoat.BatchCertificate

namespace QuadraticMoat
open NumberField OAI.GaussianMoat
open scoped BigOperators Classical
variable {K : Type*} [Field K] [NumberField K] [ctx : PlanarContext K]

structure SieveCertificate (F : PrimeFamily)
    (hgood : ∀ p, F.good p → Nonempty (SplitPrime K p)) (D : ℝ) where
  schedule : List ℕ
  smoothing : ℕ
  batches : ℕ → ℕ
  last : ℕ
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
  excess : Real.log (planeBall (K := K) D).card + last*error <
    ∑ j ∈ Finset.range (last+1), rates j

namespace SieveCertificate
variable {F : PrimeFamily} {hgood : ∀ p, F.good p → Nonempty (SplitPrime K p)} {D : ℝ}

noncomputable def primes (q : SieveCertificate F hgood D) : Finset ℕ :=
  (Finset.range (q.last+1)).biUnion (fun j => F.dyadicBatch (q.batches j))

lemma primes_spec (q : SieveCertificate F hgood D) :
    ∀ p ∈ q.primes, p.Prime ∧ F.good p := by
  intro p hp
  obtain ⟨j, _, hj⟩ := Finset.mem_biUnion.mp hp
  exact (F.mem_dyadicBatch _ _ |>.mp hj).2.2

noncomputable def sieve (q : SieveCertificate F hgood D) : SplitSieve K :=
  splitSieveOf q.primes (fun p hp => hgood p (q.primes_spec p hp).2)

/-- Packet choice is global: the union sieve and each dyadic batch select
the same factors at every shared rational prime. -/
lemma factor_eq_batch (q : SieveCertificate F hgood D) {j p : ℕ}
    (hj : j ≤ q.last) (hp : p ∈ (F.dyadicSieve hgood (q.batches j)).primes) :
    q.sieve.factor p = (F.dyadicSieve hgood (q.batches j)).factor p := by
  have hp' : p ∈ q.primes := Finset.mem_biUnion.mpr
    ⟨j, Finset.mem_range.mpr (by omega), hp⟩
  rw [SplitSieve.factor_eq _ p hp', SplitSieve.factor_eq _ p hp]
  rfl

lemma avoiding_batch (q : SieveCertificate F hgood D)
    {z : 𝓞 K} (hz : z ∈ q.sieve.avoiding) {j : ℕ} (hj : j ≤ q.last) :
    z ∈ (F.dyadicSieve hgood (q.batches j)).avoiding := by
  rw [SplitSieve.mem_avoiding] at hz ⊢
  intro p hp i
  have hp' : p ∈ q.sieve.primes := Finset.mem_biUnion.mpr
    ⟨j, Finset.mem_range.mpr (by omega), hp⟩
  rw [← q.factor_eq_batch hj hp]
  exact hz p hp' i

theorem sound (q : SieveCertificate F hgood D) (hD : 1 ≤ D) (hDscale : ctx.scale ≤ D) :
    ∀ z : ℕ → 𝓞 K, (∀ t, z t ∈ q.sieve.avoiding) → Function.Injective z →
      (∀ t, dist (z (t+1) : ℂ) (z t : ℂ) ≤ D) → False := by
  intro z ha hz hs
  exact certificate_no_walk hD hDscale q.schedule q.smoothing q.last
    (fun j => F.dyadicSieve hgood (q.batches j)) q.lengths q.rates q.batch q.divides
    q.nonneg q.smooth q.excess z hz (fun _ hj t => q.avoiding_batch (ha t) hj)
    (fun t => by simpa only [dist_comm] using hs t)

end SieveCertificate

/-- A certificate at every sufficiently enlarged planar step bound supplies
the finite divisor no-walk conclusion for full Minkowski steps. -/
theorem finiteDivisorNoWalkEndpoint_of_certificates
    (F : PrimeFamily) (hgood : ∀ p, F.good p → Nonempty (SplitPrime K p))
    (h : ∀ D : ℝ, 1 ≤ D → ctx.scale ≤ D → Nonempty (SieveCertificate F hgood D)) :
    FiniteDivisorNoWalkEndpoint K := by
  intro D hD
  let B : ℝ := ctx.scale * coordinateStepBound ctx.basis D
  have hscale0 : 0 ≤ ctx.scale := (by norm_num : (0 : ℝ) ≤ 1).trans ctx.scale_ge_one
  have hSB : ctx.scale ≤ B := by
    dsimp only [B]
    simpa only [mul_one] using mul_le_mul_of_nonneg_left
      (coordinateStepBound_ge_one ctx.basis D) hscale0
  have hB : 1 ≤ B := ctx.scale_ge_one.trans hSB
  obtain ⟨q⟩ := h B hB hSB
  refine ⟨(q.sieve.selectedFactors : Set (𝓞 K)), q.sieve.period,
    q.sieve.selectedFactors.finite_toSet, q.sieve.period_pos.ne', ?_, ?_⟩
  · intro t ht _
    exact q.sieve.selectedFactor_dvd_period ht
  · intro z hz hinj hstep
    apply q.sound hB hSB z hz hinj
    intro n
    change dist (scaledCoordinateComplex ctx.basis ctx.scale (z (n+1)))
      (scaledCoordinateComplex ctx.basis ctx.scale (z n)) ≤ B
    exact scaled_coordinate_dist_le_stepBound ctx.basis ctx.scale hscale0 D (hstep n)

lemma bandLength_le_exp_start {g U : ℝ} (hg : 0≤g) (hg1 : g≤1) (hU : 0≤U) (j : ℕ) :
    (bandLength g U j:ℝ)≤Real.exp (g*U) := by
  apply (Nat.floor_le (Real.exp_nonneg _)).trans
  apply Real.exp_le_exp.mpr
  have hh := bandScale_antitone hg hg1 hU (Nat.zero_le j)
  simpa only [bandScale,pow_zero,one_mul] using mul_le_mul_of_nonneg_left hh hg

lemma bandLength_le_exp_at {g U : ℝ} (hg : 0≤g) (hg1 : g≤1) (hU : 0≤U)
    {i j : ℕ} (hij : i≤j) :
    (bandLength g U j:ℝ)≤Real.exp (g*bandScale g U i) := by
  exact (Nat.floor_le (Real.exp_nonneg _)).trans
    (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left (bandScale_antitone hg hg1 hU hij) hg))


end QuadraticMoat
