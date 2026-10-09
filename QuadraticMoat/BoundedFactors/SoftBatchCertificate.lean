import QuadraticMoat.DyadicSieve
import QuadraticMoat.EntropyBand
import QuadraticMoat.BoundedFactors.SoftInformationTelescope

namespace QuadraticMoat.BoundedFactors
open NumberField OAI.GaussianMoat
open scoped Classical BigOperators
variable {K : Type*} [Field K] [NumberField K] [ctx : PlanarContext K]

structure BatchCertificate (D : ℝ) (ns : List ℕ) (N : ℕ) (s : SplitSieve K)
    (L : ℕ) (E r : ℝ) where
  pre : List ℕ
  rest : List ℕ
  schedule : ns=pre++rest
  T : ℝ
  nonempty : s.primes.Nonempty
  prime_scale : ∀ p∈s.primes, T≤(p:ℝ) ∧ (p:ℝ)≤2*T
  large : 5≤T
  mean : 1≤ s.meanLog
  b : ℕ
  n : ℕ
  τ : ℝ
  h : ℝ
  A : ℝ
  η : ℝ
  δ : ℝ
  u : s.SignedIndex → ℝ
  band : EntropyBand s D pre 0 b δ
  coverage : CoverageDerivation s D N rest τ u η
  cap : b≤ s.primes.card
  repetitions : 0<n
  length : 0<L
  floor : 0<τ
  threshold : 0<h
  log_cap : ∀ i, Real.log (s.signedPrime i)≤h
  cutoff : ∀ i, h≤(n:ℝ)*((L:ℝ)*(τ/(s.signedPrime i:ℝ))/2)/8
  gain : 0≤A
  exceptions : ∀ i, 0≤u i
  short : ∀ i, (D*L)^2<(s.signedPrime i:ℝ)
  smooth_length : L≤N
  smooth_error : ∀ i, (L:ℝ)/(N+1)≤(τ/(s.signedPrime i:ℝ))/2
  list : ∀ i, Real.log (1+4*u i+(s.signedPrime i:ℝ)*Real.exp
      (-(n:ℝ)*(((L:ℝ)*(τ/(s.signedPrime i:ℝ))/2)/32)))≤Real.log (s.signedPrime i)-A
  rate : (n:ℝ)*((L:ℝ)*(r+(b:ℝ)*L/(N+1))+2*(Real.log 36+2*Real.log (D*(rest.sum+N))))≤
      (b:ℝ)*(A*(1-2*η)-δ*s.meanLog-Real.log 2)-E

theorem BatchCertificate.sound {D E r : ℝ} {ns : List ℕ} {N L : ℕ} {s : SplitSieve K}
    (q : BatchCertificate D ns N s L E r) (hD : 1≤D) (hDscale : ctx.scale ≤ D)
    (z : ℕ → (𝓞 K)) (hz : Function.Injective z)
    (hs : ∀ t, dist (z t:ℂ) (z (t+1):ℂ)≤D)
    (F : Finset (𝓞 K)) (hf : ∀ f∈F, f≠0) (hF : residueWeight F≤E) :
    ∃ G : Finset (𝓞 K), F⊆G ∧ G⊆F∪s.selectedFactors ∧
      r≤TimeLaw.info ((TimeLaw.at 0).advance (commonSchedule z ns N))
        (fun a (f : G) => residueCode f.val (z a)) (incrementWord z L)
        (fun a (f : F) => residueCode f.val (z a)) / L +
        hitMass ((TimeLaw.at 0).advance (commonSchedule z ns N)) z s.selectedFactors := by
  let Q := (TimeLaw.at 0).advance (commonSchedule z q.pre 0)
  have hOld : Q.law.Hf (fun t (f : F) => residueCode f.val (z t.val))≤E :=
    (residue_finset_entropy Q.law (fun t => z t.val) F hf).trans hF
  obtain ⟨σ,π,hh⟩ := soft_schedule_batch_information (r := r) (h := q.h) (U := q.h) (C := 1) s q.nonempty z hz q.pre q.rest hD hDscale q.large
    q.mean hs q.prime_scale q.band q.u q.coverage (fun f : F => f.val) hOld
    q.cap q.repetitions q.length q.floor q.gain q.threshold q.threshold.le
    (by norm_num : (0:ℝ)≤1) (by simp only [div_self q.threshold.ne', le_refl])
    q.log_cap q.cutoff q.exceptions q.short q.smooth_length
    q.smooth_error q.list (by convert q.rate using 1 <;> ring)
  let f := fun j => s.signedFactorAt (s.selectedIndex q.cap σ π j)
  let G := F∪Finset.univ.image f
  refine ⟨G,Finset.subset_union_left,?_,?_⟩
  · apply Finset.union_subset Finset.subset_union_left
    intro g hg
    obtain ⟨j,_,rfl⟩ := Finset.mem_image.mp hg
    exact Finset.mem_union_right F (s.signed_mem_selectedFactors _)
  · rw [q.schedule]
    simp only [one_mul] at hh
    unfold TimeLaw.info
    rw [residue_cIf_finset_union]
    exact hh

theorem certificate_no_walk {D ε : ℝ} (hD : 1≤D) (hDscale : ctx.scale ≤ D) (ns : List ℕ) (N n : ℕ)
    (s : ℕ → SplitSieve K) (L : ℕ → ℕ) (r : ℕ → ℝ) (B : ℕ)
    (cert : ∀ j≤n, BatchCertificate D ns N (s j) (L j)
      (residueWeight (precedingFactors s j)) (r j))
    (hdiv : ∀ j<n, L j∣L (j+1)) (hε : 0≤ε)
    (herr : ∀ j<n, ∀ a<L (j+1), 2*Real.binEntropy ((a:ℝ)/(N+1))+
      ((a:ℝ)/(N+1))*((L j:ℝ)*Real.log (planeBall (K := K) D).card+
        2*residueWeight (precedingFactors s (n+1)))≤ε)
    (hdisj : (Finset.range (n+1) : Set ℕ).Pairwise
      (fun i j => Disjoint (s i).selectedFactors (s j).selectedFactors))
    (hexcess : Real.log (planeBall (K := K) D).card+n*ε+B<∑ j∈Finset.range (n+1), r j)
    (z : ℕ → (𝓞 K)) (hz : Function.Injective z)
    (hbudget : ∀ t, ((precedingFactors s (n+1)).filter (fun f => f ∣ z t)).card≤B)
    (hs : ∀ t, dist (z t:ℂ) (z (t+1):ℂ)≤D) : False := by
  let P := (TimeLaw.at 0).advance (commonSchedule z ns N)
  let rate (j : ℕ) (F G : Finset (𝓞 K)) := TimeLaw.info P
    (fun a (f : G) => residueCode f.val (z a)) (incrementWord z (L j))
    (fun a (f : F) => residueCode f.val (z a)) / L j
  obtain ⟨F,hFA,hFF,hR⟩ := greedy_finite_selection (precedingFactors s)
    (fun j => precedingFactors_mono s (Nat.le_succ j)) n
    (fun j F G => r j≤rate j F G+hitMass P z (s j).selectedFactors) (by
      intro j hj F hF
      obtain ⟨G,hFG,hG,hI⟩ := (cert j hj).sound hD hDscale z hz hs F
        (fun f hf => precedingFactors_ne_zero s (hF hf)) (residueWeight_mono hF)
      refine ⟨G,hFG,?_,hI⟩
      rw [precedingFactors_succ]
      exact hG.trans (Finset.union_subset_union_left hF))
  have ht := schedule_information_telescope z hs ns N n F hFF
    (fun j f hf => precedingFactors_ne_zero s (hFA j hf)) L
    (fun j hj => (cert j hj).length) hdiv (fun j hj => (cert j hj).smooth_length) hε (by
      intro j hj a ha
      have hw := residueWeight_mono ((hFA (j+1)).trans (precedingFactors_mono s (j := n+1) (by omega)))
      have hh := herr j hj a ha
      have hx : 0≤(a:ℝ)/(N+1) := by positivity
      change _+_ * (_+2*residueWeight (F (j+1)))≤ε
      nlinarith only [hw,hh,hx])
  have hh := Finset.sum_le_sum (s := Finset.range (n+1)) (fun j hj => hR j (by simpa only [Finset.mem_range,Nat.lt_succ_iff] using hj))
  have hb := hitMass_sum_le P z (Finset.range (n+1))
    (fun j => (s j).selectedFactors) B hdisj hbudget
  rw [Finset.sum_add_distrib] at hh
  have htotal : (∑ j∈Finset.range (n+1), r j)≤
      Real.log (planeBall (K := K) D).card+n*ε+B := by
    exact hh.trans (add_le_add ht hb)
  exact (not_lt_of_ge htotal) hexcess


end QuadraticMoat.BoundedFactors
