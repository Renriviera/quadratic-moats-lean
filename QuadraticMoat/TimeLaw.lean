import QuadraticMoat.PointEnrichment
import QuadraticMoat.PlaneLattice
import OAI.NumberTheory.GaussianMoat.TimeLaw

universe uOmega uCapitalKappa uAlpha uBeta uGamma uIota

namespace QuadraticMoat
open NumberField OAI.GaussianMoat
open scoped BigOperators Classical
variable {Fld : Type*} [Field Fld] [NumberField Fld] [ctx : PlanarContext Fld]
noncomputable def TimeLaw.step (P : TimeLaw) (z : ℕ → (𝓞 Fld)) (n : ℕ) : TimeLaw where
  last := P.last+n
  law := ((FinLaw.uniform Bool).joint (fun _ => P.law.joint (fun a =>
    differenceLaw (fun t => z (a.val+t)) n))).map (endpointTime P.last n)

lemma SplitSieve.pointEntropy_map {Ω : Type uOmega} {Κ : Type uCapitalKappa} [Fintype Ω] [Fintype Κ]
    (s : SplitSieve Fld) (p : FinLaw Ω) (f : Ω → Κ) (Z : Κ → (𝓞 Fld)) (b : ℕ) :
    s.pointEntropy (p.map f) Z b = s.pointEntropy p (Z ∘ f) b := by
  unfold pointEntropy FinLaw.signedEntropy FinLaw.orderedEntropy
  simp only [FinLaw.Hf_map]
  rfl

lemma SplitSieve.pointEntropy_joint_fst {Ω : Type uOmega} {Κ : Type uCapitalKappa} [Fintype Ω] [Fintype Κ]
    (s : SplitSieve Fld) (p : FinLaw Ω) (q : Ω → FinLaw Κ) (Z : Ω → (𝓞 Fld)) (b : ℕ) :
    s.pointEntropy (p.joint q) (fun v => Z v.1) b = s.pointEntropy p Z b := by
  have h := s.pointEntropy_map (p.joint q) Prod.fst Z b
  rw [FinLaw.joint_map_fst] at h
  exact h.symm

lemma shifted_walk_injective (z : ℕ → (𝓞 Fld)) (hz : Function.Injective z) (a : ℕ) :
    Function.Injective (fun t => z (a+t)) := by intro i j h; have := hz h; omega

theorem TimeLaw.step_enrichment (P : TimeLaw) (s : SplitSieve Fld)
    (z : ℕ → (𝓞 Fld)) {D F : ℝ} (hD : 1 ≤ D)
    (hstep : ∀ t, dist (z t:ℂ) (z (t+1):ℂ) ≤ D) {n b q : ℕ}
    (hn : 1 ≤ n) (hb : 0 < b) (hbq : b < q) (hq : q ≤ s.primes.card)
    (hF : ∀ a : Fin (P.last+1), F ≤ s.freshCoordinate
      (differenceLaw (fun t => z (a.val+t)) n)
      (fun ij => z (a.val+ij.1.val)) (fun ij => z (a.val+ij.2.val)) b (by omega)) :
    (b:ℝ)*((q-b:ℕ)*F+s.pointEntropy P.law (fun a => z a.val) q-
      2*(Real.log 36+2*Real.log (D*n))) ≤
      2*(q:ℝ)*s.pointEntropy (TimeLaw.step P z n).law (fun a => z a.val) b := by
  let K := P.law.joint (fun a => differenceLaw (fun t => z (a.val+t)) n)
  let X := fun v : Fin (P.last+1) × (Fin (n+1) × Fin (n+1)) => z (v.1.val+v.2.1.val)
  let Y := fun v : Fin (P.last+1) × (Fin (n+1) × Fin (n+1)) => z (v.1.val+v.2.2.val)
  let Z := fun v : Fin (P.last+1) × (Fin (n+1) × Fin (n+1)) => z v.1.val
  have hF' : F ≤ s.freshCoordinate K X Y b (by omega) := by
    have hh := s.freshCoordinate_joint_ge P.law
      (fun a => differenceLaw (fun t => z (a.val+t)) n)
      (fun a ij => z (a.val+ij.1.val)) (fun a ij => z (a.val+ij.2.val)) (by omega : b < s.primes.card)
    apply le_trans _ hh
    have hsum := Finset.sum_le_sum (s := Finset.univ) (fun a _ =>
      mul_le_mul_of_nonneg_left (hF a) (P.law.nonneg a))
    simpa only [← Finset.sum_mul,P.law.sum_one,one_mul] using hsum
  have hDn : 1 ≤ D*n := one_le_mul_of_one_le_of_one_le hD (by exact_mod_cast hn)
  have h := s.actual_enrichment K X Y Z hb hbq hq hF' hDn
    (fun v => plane_walk_pair_displacement z (by linarith) hstep _ _ _ _ (by omega) (by omega))
    (fun v => by
      change ‖((z (v.1.val+v.2.1.val)-z v.1.val:(𝓞 Fld)):ℂ)‖ ≤ D*n
      simpa only [Nat.add_zero] using
        plane_walk_pair_displacement z (by linarith) hstep v.1.val n v.2.1.val 0 (by omega) (by omega))
  have hZ := s.pointEntropy_joint_fst P.law
    (fun a => differenceLaw (fun t => z (a.val+t)) n) (fun a => z a.val) q
  rw [hZ] at h
  have hout : s.pointEntropy (TimeLaw.step P z n).law (fun a => z a.val) b =
      s.pointEntropy ((FinLaw.uniform Bool).joint (fun _ => K))
        (fun v => if v.1 then X v.2 else Y v.2) b := by
    change s.pointEntropy (((FinLaw.uniform Bool).joint (fun _ => K)).map
      (endpointTime P.last n)) (fun a => z a.val) b = _
    rw [s.pointEntropy_map]
    apply congrArg (fun F => s.pointEntropy ((FinLaw.uniform Bool).joint (fun _ => K)) F b)
    funext v
    simp only [Function.comp_def,endpointTime,X,Y]
    split_ifs <;> rfl
  rw [hout]
  exact h

end QuadraticMoat
