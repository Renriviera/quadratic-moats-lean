import QuadraticMoat.MultiscaleSchedule
import OAI.NumberTheory.GaussianMoat.KernelComposition

universe uOmega uAlpha uBeta

namespace QuadraticMoat
open NumberField OAI.GaussianMoat
open scoped BigOperators Classical
variable {Fld : Type*} [Field Fld] [NumberField Fld] [ctx : PlanarContext Fld]
lemma SplitSieve.pointEntropy_exact_start (s : SplitSieve Fld) (K : ForwardKernel)
    (z : ℕ → (𝓞 Fld)) (a b : ℕ) :
    s.pointEntropy ((TimeLaw.at a).advance K).law (fun t => z t.val) b=
      s.pointEntropy (K.law a) (fun t => z (a+t.val)) b := by
  rw [TimeLaw.at_advance]
  change s.pointEntropy ((K.law a).map
    (fun t => (⟨a+t.val,by omega⟩ : Fin (a+K.bound+1)))) (fun t => z t.val) b = _
  rw [s.pointEntropy_map]
  rfl

theorem TimeLaw.advance_entropy_succ (P : TimeLaw) (K : ForwardKernel) (s : SplitSieve Fld)
    (z : ℕ → (𝓞 Fld)) {D : ℝ} (hD : 1≤D)
    (hs : ∀ t, dist (z t:ℂ) (z (t+1):ℂ)≤D) (b : ℕ) :
    s.pointEntropy P.law (fun a => z a.val) b-
      (Real.log 36+2*Real.log (D*(K.bound+1))) ≤
    s.pointEntropy (P.advance K).law (fun a => z a.val) b := by
  let Q := P.law.joint (fun a => K.law a.val)
  have hh := s.pointEntropy_shift Q (fun v => z v.1.val)
    (fun v => z (v.1.val+v.2.val)) b
  have hf := s.pointEntropy_joint_fst P.law (fun a => K.law a.val) (fun a => z a.val) b
  change s.pointEntropy Q (fun v => z v.1.val) b=_ at hf
  rw [hf] at hh
  have he : s.pointEntropy (P.advance K).law (fun a => z a.val) b=
      s.pointEntropy Q (fun v => z (v.1.val+v.2.val)) b := by
    unfold TimeLaw.advance
    rw [s.pointEntropy_map]
    rfl
  have hc : Q.Hf (fun v => z (v.1.val+v.2.val)-z v.1.val) ≤
      Real.log 36+2*Real.log (D*(K.bound+1)) := by
    apply displacement_entropy_le
    · exact one_le_mul_of_one_le_of_one_le hD (by exact_mod_cast Nat.le_add_left 1 K.bound)
    · intro v
      have hd := plane_walk_pair_displacement z (by linarith only [hD]) hs
        v.1.val (K.bound+1) v.2.val 0 (by omega) (by omega)
      simpa only [Nat.add_zero,Nat.cast_add,Nat.cast_one] using hd
  rw [he]
  linarith only [hh,hc]

theorem commonSchedule_subband_entropy (s : SplitSieve Fld) (hne : s.primes.Nonempty)
    (z : ℕ → (𝓞 Fld)) (hinj : Function.Injective z)
    (pre post : List ℕ) (a N : ℕ) {D T U g e : ℝ} {l : ℕ}
    (hD : 1≤D) (hDscale : ctx.scale≤D) (hT : 5≤T) (hs : ∀ t, dist (z t:ℂ) (z (t+1):ℂ)≤D)
    (hpT : ∀ p∈s.primes, T≤(p:ℝ) ∧ (p:ℝ)≤2*T)
    (hg : 0<g) (hg1 : g≤1/200) (hL : 1≤ s.meanLog) (hU : 0<U)
    (hlog : 2*(1+Real.log 18)≤g*bandScale g U l)
    (hlarge : 640*s.meanLog≤g^5*bandScale g U l)
    (hsize : Real.log 16+Real.log (ctx.scale^2 * max (D/ctx.scale) ((latticeBall (4*(D/ctx.scale))).card:ℝ))≤g^2*bandScale g U l)
    (hdisp : 4*Real.log D+2*Real.log 36≤4*g*bandScale g U l)
    (hgeom : 2*Real.log 16+4*Real.log D≤bandScale g U l/4)
    (hcap : ⌊U/s.meanLog⌋₊≤ s.primes.card)
    (hcost : Real.log 36+2*Real.log (D*((post.sum+N:ℕ)+1)) ≤
      e*(bandSize s g U l:ℝ)*s.meanLog) :
    (1-(1/2:ℝ)^l-80*g-e)*(bandSize s g U l:ℝ)*s.meanLog ≤
      s.pointEntropy ((commonSchedule z
        (pre++List.ofFn (fun i : Fin l => bandLength g U i.val)++post) N).law a)
          (fun t => z (a+t.val)) (bandSize s g U l) := by
  rw [← s.pointEntropy_exact_start]
  rw [List.append_assoc,TimeLaw.advance_common_append,TimeLaw.advance_common_append,
    TimeLaw.foldl_ofFn]
  let P := pre.foldl (fun Q k => TimeLaw.step Q z k) (TimeLaw.at a)
  have h1 := TimeLaw.geometric_band_entropy P s hne z hinj hD hDscale hT hs hpT hg hg1 hL hU
    hlog hlarge hsize hdisp hgeom hcap
  have h2 := TimeLaw.advance_entropy_succ (TimeLaw.run P z (bandLength g U) l)
    (commonSchedule z post N) s z hD hs (bandSize s g U l)
  rw [commonSchedule_bound] at h2
  change _ ≤ s.pointEntropy ((TimeLaw.run P z (bandLength g U) l).advance (commonSchedule z post N)).law
    (fun a => z a.val) (bandSize s g U l)
  simp only [Nat.cast_add] at hcost h2
  nlinarith only [h1,h2,hcost]

lemma commonSchedule_append (z : ℕ → (𝓞 Fld)) (ns ms : List ℕ) (N : ℕ) :
    commonSchedule z (ns++ms) N=(commonSchedule z ns 0).then (commonSchedule z ms N) := by
  induction ns with
  | nil => exact (ForwardKernel.zero_then _).symm
  | cons n ns ih =>
    rw [List.cons_append,commonSchedule_cons,commonSchedule_cons,ih,ForwardKernel.then_assoc]

end QuadraticMoat
