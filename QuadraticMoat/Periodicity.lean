import QuadraticMoat.Lattice
import QuadraticMoat.Restoration
import QuadraticMoat.Reduction

/-! Finiteness and the Q² periodic component bound on the full Minkowski lattice. -/

namespace QuadraticMoat

open NumberField
open scoped Classical

variable {K : Type*} [Field K] [NumberField K]

@[simp] theorem minkowskiDist_add_right (a b v : 𝓞 K) :
    minkowskiDist K (a + v) (b + v) = minkowskiDist K a b := by
  simp only [minkowskiDist, map_add, dist_add_right]

noncomputable def integerLatticeGraph (A : Set (𝓞 K)) (D : ℝ) : SimpleGraph (𝓞 K) where
  Adj z w := z ≠ w ∧ z ∈ A ∧ w ∈ A ∧ minkowskiDist K (z) (w) ≤ D
  symm := by
    constructor
    intro z w h
    exact ⟨h.1.symm, h.2.2.1, h.2.1, by simpa only [minkowskiDist, dist_comm] using h.2.2.2⟩
  loopless := by
    constructor
    intro z h
    exact h.1 rfl

theorem lattice_walk_mem {A : Set (𝓞 K)} {D : ℝ} {z w : 𝓞 K}
    (p : (integerLatticeGraph A D).Walk z w) (hz : z ∈ A) (i : ℕ) : p.getVert i ∈ A := by
  induction p generalizing i with
  | nil => simpa using hz
  | @cons u v w huv p ih =>
    cases i with
    | zero => simpa using hz
    | succ i => exact ih huv.2.2.1 i

theorem lattice_walk_dist {A : Set (𝓞 K)} {D : ℝ} {z w : 𝓞 K}
    (p : (integerLatticeGraph A D).Walk z w) :
    minkowskiDist K (z) (w) ≤ (p.length : ℝ) * max D 0 := by
  induction p with
  | nil => simp [minkowskiDist]
  | @cons u v w huv p ih =>
    calc
      minkowskiDist K (u) (w) ≤ minkowskiDist K (u) (v) + minkowskiDist K (v) (w) :=
        dist_triangle _ _ _
      _ ≤ D + (p.length : ℝ) * max D 0 := add_le_add huv.2.2.2 ih
      _ ≤ ((p.cons huv).length : ℝ) * max D 0 := by
        simp only [SimpleGraph.Walk.length_cons, Nat.cast_add, Nat.cast_one]
        nlinarith [le_max_left D 0]

@[ext]
structure LatticePrefix (A : Set (𝓞 K)) (D : ℝ) (root : 𝓞 K) (n : ℕ) where
  point : Fin (n + 1) → 𝓞 K
  mem : ∀ i, point i ∈ A
  start : point 0 = root
  injective : Function.Injective point
  step : ∀ i j, j.val = i.val + 1 → minkowskiDist K (point j) (point i) ≤ D

theorem LatticePrefix.dist_le {A : Set (𝓞 K)} {D : ℝ} {root : 𝓞 K}
    {n : ℕ} (p : LatticePrefix A D root n) (i : Fin (n + 1)) :
    minkowskiDist K (p.point i) (root) ≤ (i.val : ℝ) * max D 0 := by
  induction i using Fin.induction with
  | zero => simp [p.start, minkowskiDist]
  | succ i ih =>
    calc
      minkowskiDist K (p.point i.succ) (root) ≤
          minkowskiDist K (p.point i.succ) (p.point i.castSucc) +
            minkowskiDist K (p.point i.castSucc) (root) := dist_triangle _ _ _
      _ ≤ D + (i.val : ℝ) * max D 0 := add_le_add (p.step _ _ rfl) ih
      _ ≤ (i.succ.val : ℝ) * max D 0 := by
        simp only [Fin.val_succ, Nat.cast_add, Nat.cast_one]
        nlinarith [le_max_left D 0]

instance LatticePrefix.finite (A : Set (𝓞 K)) (D : ℝ) (root : 𝓞 K) (n : ℕ) :
    Finite (LatticePrefix A D root n) := by
  let S : Set (Fin (n + 1) → 𝓞 K) :=
    {f | ∀ i, minkowskiDist K (f i) (root) ≤ (n : ℝ) * max D 0}
  have hS : S.Finite := Set.Finite.pi' (fun _ => finite_minkowski_ball K root ((n : ℝ) * max D 0))
  let := hS.to_subtype
  let f : LatticePrefix A D root n → S := fun p => ⟨p.point, fun i =>
    (p.dist_le i).trans (mul_le_mul_of_nonneg_right
      (by exact_mod_cast Nat.le_of_lt_succ i.isLt) (le_max_right D 0))⟩
  exact Finite.of_injective f (fun p q h => LatticePrefix.ext (congrArg Subtype.val h))

def LatticePrefix.restrict {A : Set (𝓞 K)} {D : ℝ} {root : 𝓞 K}
    {n m : ℕ} (h : n ≤ m) (p : LatticePrefix A D root m) : LatticePrefix A D root n where
  point i := p.point (Fin.castLE (by omega) i)
  mem i := p.mem _
  start := by simpa using p.start
  injective := p.injective.comp (Fin.castLE_injective (by omega))
  step i j hij := p.step _ _ hij

theorem infinite_component_has_walk {A : Set (𝓞 K)} {D : ℝ} {root : 𝓞 K}
    (hroot : root ∈ A) (hinfinite : {w | (integerLatticeGraph A D).Reachable root w}.Infinite) :
    ∃ z : ℕ → 𝓞 K, (∀ n, z n ∈ A) ∧ Function.Injective z ∧
      ∀ n, minkowskiDist K (z (n + 1)) (z n) ≤ D := by
  classical
  have hne (n : ℕ) : Nonempty (LatticePrefix A D root n) := by
    have hnot : ¬ {w | (integerLatticeGraph A D).Reachable root w} ⊆
        {w | minkowskiDist K (w) (root) ≤ (n : ℝ) * max D 0} := by
      intro h
      exact hinfinite ((finite_minkowski_ball K root ((n : ℝ) * max D 0)).subset h)
    obtain ⟨w, hw, hfar⟩ := Set.not_subset.mp hnot
    apply hw.elim_path
    intro path
    let p := path.val
    have hn : n ≤ p.length := by
      by_contra hn
      have hlen : (p.length : ℝ) ≤ (n : ℝ) := by exact_mod_cast (by omega : p.length ≤ n)
      have hdist := (lattice_walk_dist p).trans
        (mul_le_mul_of_nonneg_right hlen (le_max_right D 0))
      apply hfar
      change minkowskiDist K (w) (root) ≤ (n : ℝ) * max D 0
      simpa only [minkowskiDist, dist_comm] using hdist
    exact ⟨{
      point := fun i => p.getVert i.val
      mem := fun i => lattice_walk_mem p hroot _
      start := p.getVert_zero
      injective := fun i j h => Fin.ext (path.isPath.getVert_injOn
        (show i.val ≤ p.length from (Nat.le_of_lt_succ i.isLt).trans hn)
        (show j.val ≤ p.length from (Nat.le_of_lt_succ j.isLt).trans hn) h)
      step := fun i j h => by
        have hadj := p.adj_getVert_succ (i := i.val) (by omega)
        simpa only [h, minkowskiDist, dist_comm] using hadj.2.2.2
    }⟩
  let (n : ℕ) : Nonempty (LatticePrefix A D root n) := hne n
  obtain ⟨p, hp⟩ := exists_seq_forall_proj_of_forall_finite
    (α := fun n => LatticePrefix A D root n)
    (fun h => LatticePrefix.restrict h)
    (by intro n a; apply LatticePrefix.ext; funext i; rfl)
    (by intro i j k hij hjk a; apply LatticePrefix.ext; funext l; rfl)
    (fun _ _ => Set.toFinite _)
  let z : ℕ → 𝓞 K := fun n => (p n).point (Fin.last n)
  have hagree (n k : ℕ) (hnk : n ≤ k) :
      (p k).point ⟨n, by omega⟩ = z n := by
    simpa only [LatticePrefix.restrict, z, Fin.last, Fin.castLE] using
      congrArg (fun a : LatticePrefix A D root n => a.point (Fin.last n)) (hp hnk)
  refine ⟨z, fun n => (p n).mem _, ?_, ?_⟩
  · intro n m heq
    have h := (hagree n (max n m) (le_max_left _ _)).trans
      (heq.trans (hagree m (max n m) (le_max_right _ _)).symm)
    exact congrArg Fin.val ((p (max n m)).injective h)
  · intro n
    have h := (p (n + 1)).step ⟨n, by omega⟩ (Fin.last (n + 1)) rfl
    simpa only [hagree n (n + 1) (by omega)] using h

theorem lattice_component_finite {A : Set (𝓞 K)} {D : ℝ}
    (hno : ∀ z : ℕ → 𝓞 K, (∀ n, z n ∈ A) → Function.Injective z →
      (∀ n, minkowskiDist K (z (n + 1)) (z n) ≤ D) → False)
    {root : 𝓞 K} (hroot : root ∈ A) :
    {w | (integerLatticeGraph A D).Reachable root w}.Finite := by
  by_contra h
  obtain ⟨z, hz, hinj, hstep⟩ := infinite_component_has_walk hroot h
  exact hno z hz hinj hstep

def latticeTranslation {A : Set (𝓞 K)} {D : ℝ} (v : 𝓞 K)
    (hv : ∀ z ∈ A, z + v ∈ A) :
    integerLatticeGraph A D →g integerLatticeGraph A D where
  toFun z := z + v
  map_rel' := by
    intro z w h
    refine ⟨fun he => h.1 (add_right_cancel he), hv z h.2.1, hv w h.2.2.1, ?_⟩
    simpa only [minkowskiDist_add_right] using h.2.2.2

theorem eq_of_finite_component_period {A : Set (𝓞 K)} {D : ℝ}
    {root x y v : 𝓞 K}
    (hfinite : {w | (integerLatticeGraph A D).Reachable root w}.Finite)
    (hx : (integerLatticeGraph A D).Reachable root x)
    (hy : (integerLatticeGraph A D).Reachable root y)
    (hv : ∀ z ∈ A, z + v ∈ A) (hxy : y = x + v) : x = y := by
  classical
  by_contra hne
  have hv0 : v ≠ 0 := by intro h; apply hne; simpa [h] using hxy.symm
  have hreach : (integerLatticeGraph A D).Reachable x (x + v) := by
    rw [← hxy]
    exact hx.symm.trans hy
  have hall (n : ℕ) : (integerLatticeGraph A D).Reachable x (x + n • v) := by
    induction n with
    | zero => simp
    | succ n ih =>
      have ht := ih.map (latticeTranslation v hv)
      have hh := hreach.trans ht
      change (integerLatticeGraph A D).Reachable x ((x + n • v) + v) at hh
      simpa only [succ_nsmul, add_assoc] using hh
  have hinj : Function.Injective (fun n : ℕ => x + n • v) := by
    intro n m h
    have hh := add_left_cancel h
    simp only [nsmul_eq_mul] at hh
    exact Nat.cast_injective (mul_right_cancel₀ hv0 hh)
  apply (Set.infinite_range_of_injective hinj)
  exact hfinite.subset (by rintro _ ⟨n, rfl⟩; exact hx.trans (hall n))


/-- An integral basis gives two integer coordinates in every degree-two field. -/
noncomputable def quadraticCoordinates (hdegree : Module.finrank ℚ K = 2) :
    (𝓞 K) ≃+ (ℤ × ℤ) := by
  have hcard : Fintype.card (Module.Free.ChooseBasisIndex ℤ (𝓞 K)) = 2 :=
    (Module.finrank_eq_card_basis (RingOfIntegers.basis K)).symm.trans
      ((RingOfIntegers.rank K).trans hdegree)
  let e := Fintype.equivFinOfCardEq hcard
  exact (((RingOfIntegers.basis K).reindex e).equivFun.trans
    (LinearEquiv.finTwoArrow ℤ ℤ)).toAddEquiv

/-- Two integer coordinates reduced modulo Q.  The additive equivalence may
be supplied by any integral basis in degree two. -/
def coordinateResidue (b : (𝓞 K) ≃+ (ℤ × ℤ)) (Q : ℕ) (z : 𝓞 K) :
    ZMod Q × ZMod Q := ((b z).1, (b z).2)

omit [NumberField K] in
theorem eq_add_period_of_coordinateResidue_eq
    (b : (𝓞 K) ≃+ (ℤ × ℤ)) {Q : ℕ} {x y : 𝓞 K}
    (h : coordinateResidue b Q x = coordinateResidue b Q y) :
    ∃ v : 𝓞 K, y = x + (Q : 𝓞 K) * v := by
  have hx := (ZMod.intCast_eq_intCast_iff_dvd_sub (b x).1 (b y).1 Q).mp (congrArg Prod.fst h)
  have hy := (ZMod.intCast_eq_intCast_iff_dvd_sub (b x).2 (b y).2 Q).mp (congrArg Prod.snd h)
  obtain ⟨a, ha⟩ := hx
  obtain ⟨c, hc⟩ := hy
  refine ⟨b.symm (a, c), ?_⟩
  apply b.injective
  rw [map_add, ← nsmul_eq_mul, map_nsmul, b.apply_symm_apply]
  apply Prod.ext <;> simp <;> omega

/-- Translation-periodic finite components inject into their Q² residue classes. -/
theorem periodic_component_bound (b : (𝓞 K) ≃+ (ℤ × ℤ))
    {A : Set (𝓞 K)} {D : ℝ} {Q : ℕ} (hQ : Q ≠ 0)
    (hperiod : ∀ z ∈ A, ∀ v : 𝓞 K, z + (Q : 𝓞 K) * v ∈ A)
    {root : 𝓞 K}
    (hfinite : (graphComponent (integerLatticeGraph A D) root).Finite) :
    (graphComponent (integerLatticeGraph A D) root).ncard ≤ Q ^ 2 := by
  classical
  let : NeZero Q := ⟨hQ⟩
  let C := graphComponent (integerLatticeGraph A D) root
  have hinj : Set.InjOn (coordinateResidue b Q) C := by
    intro x hx y hy heq
    obtain ⟨v, hv⟩ := eq_add_period_of_coordinateResidue_eq b heq
    exact eq_of_finite_component_period hfinite hx hy
      (fun z hz => hperiod z hz v) hv
  have hcard := Set.ncard_le_card ((coordinateResidue b Q) '' C)
  rw [Set.InjOn.ncard_image hinj, Nat.card_prod, Nat.card_zmod, pow_two] at *
  exact hcard

/-- The finite-sieve no-walk conclusion, expressed on the full integer lattice. -/
def NoInfiniteAvoidingWalk (A : Set (𝓞 K)) (D : ℝ) : Prop :=
  ∀ z : ℕ → 𝓞 K, (∀ n, z n ∈ A) → Function.Injective z →
    (∀ n, minkowskiDist K (z (n + 1)) (z n) ≤ D) → False

/-- The periodicity bridge from the analytical no-walk endpoint to a uniform
bound on lattice components, without exceptions or irreducibility restrictions. -/
theorem lattice_component_bound_of_periodic_no_walk
    (b : (𝓞 K) ≃+ (ℤ × ℤ)) {A : Set (𝓞 K)} {D : ℝ} {Q : ℕ}
    (hQ : Q ≠ 0)
    (hperiod : ∀ z ∈ A, ∀ v : 𝓞 K, z + (Q : 𝓞 K) * v ∈ A)
    (hno : NoInfiniteAvoidingWalk A D) {root : 𝓞 K} (hroot : root ∈ A) :
    (graphComponent (integerLatticeGraph A D) root).Finite ∧
    (graphComponent (integerLatticeGraph A D) root).ncard ≤ Q ^ 2 := by
  have hfin := lattice_component_finite hno hroot
  exact ⟨hfin, periodic_component_bound b hQ hperiod hfin⟩

/-- The induced irreducible graph maps injectively into the full lattice graph. -/
def irreducibleBaseToInteger (A : Set (𝓞 K)) (D : ℝ) :
    baseGraph (irreducibleGraph K D) (Subtype.val ⁻¹' A) →g integerLatticeGraph A D where
  toFun := Subtype.val
  map_rel' := by
    intro a b hab
    exact ⟨fun h => hab.1.1 (Subtype.ext h), hab.2.1, hab.2.2, hab.1.2⟩

/-- Restricting to irreducibles cannot increase a lattice component's size. -/
theorem irreducible_base_bound_of_integer_bound {A : Set (𝓞 K)} {D : ℝ} {M : ℕ}
    (hbound : ∀ r ∈ A, (graphComponent (integerLatticeGraph A D) r).Finite ∧
      (graphComponent (integerLatticeGraph A D) r).ncard ≤ M)
    (a : IrreducibleVertex K) (ha : a.val ∈ A) :
    (graphComponent (baseGraph (irreducibleGraph K D) (Subtype.val ⁻¹' A)) a).Finite ∧
    (graphComponent (baseGraph (irreducibleGraph K D) (Subtype.val ⁻¹' A)) a).ncard ≤ M := by
  classical
  let C := graphComponent (baseGraph (irreducibleGraph K D) (Subtype.val ⁻¹' A)) a
  have hsub : Subtype.val '' C ⊆ graphComponent (integerLatticeGraph A D) a.val := by
    rintro _ ⟨b, hb, rfl⟩
    exact hb.map (irreducibleBaseToInteger A D)
  have himage : (Subtype.val '' C).Finite := (hbound a.val ha).1.subset hsub
  have hfin : C.Finite := (himage.preimage Subtype.val_injective.injOn).subset
    (fun b hb => ⟨b, hb, rfl⟩)
  refine ⟨hfin, ?_⟩
  have hcard := (Set.ncard_le_ncard hsub (hbound a.val ha).1).trans (hbound a.val ha).2
  rw [Set.InjOn.ncard_image Subtype.val_injective.injOn] at hcard
  exact hcard

/-- The precise periodicity output consumed by the irreducible restoration theorem. -/
theorem irreducible_base_bound_of_periodic_no_walk
    (b : (𝓞 K) ≃+ (ℤ × ℤ)) {A : Set (𝓞 K)} {D : ℝ} {Q : ℕ}
    (hQ : Q ≠ 0)
    (hperiod : ∀ z ∈ A, ∀ v : 𝓞 K, z + (Q : 𝓞 K) * v ∈ A)
    (hno : NoInfiniteAvoidingWalk A D)
    (a : IrreducibleVertex K) (ha : a.val ∈ A) :
    (graphComponent (baseGraph (irreducibleGraph K D) (Subtype.val ⁻¹' A)) a).Finite ∧
    (graphComponent (baseGraph (irreducibleGraph K D) (Subtype.val ⁻¹' A)) a).ncard ≤ Q ^ 2 :=
  irreducible_base_bound_of_integer_bound
    (fun _ hr => lattice_component_bound_of_periodic_no_walk b hQ hperiod hno hr) a ha

/-- Avoiding selected nonunit divisors on the entire ring of integers. -/
def integerAvoidingSelectedDivisors (T : Set (𝓞 K)) : Set (𝓞 K) :=
  {z | ∀ t ∈ T, ¬ IsUnit t → ¬ t ∣ z}

omit [NumberField K] in
/-- Every common multiple of the selected factors is a translation period. -/
theorem integerAvoidingSelectedDivisors_periodic (T : Set (𝓞 K)) (Q : ℕ)
    (hfactor : ∀ t ∈ T, ¬ IsUnit t → t ∣ (Q : 𝓞 K)) :
    ∀ z ∈ integerAvoidingSelectedDivisors T, ∀ v : 𝓞 K,
      z + (Q : 𝓞 K) * v ∈ integerAvoidingSelectedDivisors T := by
  intro z hz v t ht hnu hd
  apply hz t ht hnu
  have hh := dvd_sub hd (dvd_mul_of_dvd_left (hfactor t ht hnu) v)
  simpa only [add_sub_cancel_right] using hh

/-- Periodicity turns a full-lattice no-walk sieve output into the component
input needed by the exception-restoration reduction. -/
theorem divisor_base_bound_of_no_walk (hdegree : Module.finrank ℚ K = 2)
    (T : Set (𝓞 K)) {D : ℝ} {Q : ℕ} (hQ : Q ≠ 0)
    (hfactor : ∀ t ∈ T, ¬ IsUnit t → t ∣ (Q : 𝓞 K))
    (hno : NoInfiniteAvoidingWalk (integerAvoidingSelectedDivisors T) D) :
    ∀ a ∈ avoidingSelectedDivisors K T,
      (graphComponent (baseGraph (irreducibleGraph K D) (avoidingSelectedDivisors K T)) a).Finite ∧
      (graphComponent (baseGraph (irreducibleGraph K D) (avoidingSelectedDivisors K T)) a).ncard ≤ Q ^ 2 := by
  intro a ha
  exact irreducible_base_bound_of_periodic_no_walk (quadraticCoordinates hdegree) hQ
    (integerAvoidingSelectedDivisors_periodic T Q hfactor) hno a ha

/-- An analytical sieve output with a finite factor set, common-multiple
period, and no infinite avoiding walk.  It is an explicit remaining input. -/
def FiniteDivisorNoWalkEndpoint (K : Type*) [Field K] [NumberField K] : Prop :=
  ∀ D : ℝ, 0 ≤ D → ∃ (T : Set (𝓞 K)) (Q : ℕ), T.Finite ∧ Q ≠ 0 ∧
    (∀ t ∈ T, ¬ IsUnit t → t ∣ (Q : 𝓞 K)) ∧
    NoInfiniteAvoidingWalk (integerAvoidingSelectedDivisors T) D

/-- All combinatorial and restoration steps of the all-quadratic proof are
now discharged; the concrete no-walk finite sieve remains to be proved. -/
theorem uniformEndpoint_of_finiteDivisorNoWalkEndpoint
    (hdegree : Module.finrank ℚ K = 2) (hsieve : FiniteDivisorNoWalkEndpoint K) :
    UniformEndpoint K := by
  apply uniformEndpoint_of_divisorSieveComponentEndpoint K hdegree
  intro D hD
  obtain ⟨T, Q, hT, hQ, hfactor, hno⟩ := hsieve D hD
  exact ⟨T, Q ^ 2, hT, divisor_base_bound_of_no_walk hdegree T hQ hfactor hno⟩

end QuadraticMoat
