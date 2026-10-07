import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
import Mathlib.Data.Set.Card.Arithmetic
import Mathlib.Topology.MetricSpace.Basic
import Mathlib.Tactic

/-!
Restoring a possibly infinite set of exceptional vertices.  The only finite
exceptional set required is the set of endpoints of connections through one
base component.  This is the combinatorial part of the close-pair argument.
-/

namespace QuadraticMoat

variable {X : Type*}

def baseGraph (G : SimpleGraph X) (A : Set X) : SimpleGraph X where
  Adj x y := G.Adj x y ∧ x ∈ A ∧ y ∈ A
  symm := ⟨by rintro x y ⟨h, hx, hy⟩; exact ⟨h.symm, hy, hx⟩⟩
  loopless := ⟨by intro x h; exact G.irrefl h.1⟩

def graphComponent (G : SimpleGraph X) (x : X) : Set X := {y | G.Reachable x y}

/-- A connection between exceptions with all intervening vertices in one
base component.  The direct-edge alternative allows zero interior vertices. -/
def exceptionalBridge (G : SimpleGraph X) (A : Set X) (e f : X) : Prop :=
  G.Adj e f ∨ ∃ a b, a ∈ A ∧ b ∈ A ∧ G.Adj e a ∧
    (baseGraph G A).Reachable a b ∧ G.Adj b f

/-- The exceptional endpoint set that the arithmetic close-pair lemma bounds. -/
def bridgeEndpoints (G : SimpleGraph X) (A : Set X) : Set X :=
  {e | e ∉ A ∧ ∃ f, f ∉ A ∧ e ≠ f ∧ exceptionalBridge G A e f}

theorem exceptionalBridge_symm {G : SimpleGraph X} {A : Set X} {e f : X}
    (h : exceptionalBridge G A e f) : exceptionalBridge G A f e := by
  rcases h with h | ⟨a, b, ha, hb, hea, hab, hbf⟩
  · exact Or.inl h.symm
  · exact Or.inr ⟨b, a, hb, ha, hbf.symm, hab.symm, hea.symm⟩

theorem reachable_mem_of_closed {G : SimpleGraph X} {T : Set X}
    (hclosed : ∀ a b, a ∈ T → G.Adj a b → b ∈ T)
    {a b : X} (ha : a ∈ T) (h : G.Reachable a b) : b ∈ T := by
  apply h.elim
  intro w
  clear h
  induction w with
  | nil => exact ha
  | @cons a b c hab w ih => exact ih (hclosed a b ha hab)

theorem base_reachable_mem {G : SimpleGraph X} {A : Set X} {a b : X}
    (ha : a ∈ A) (h : (baseGraph G A).Reachable a b) : b ∈ A :=
  reachable_mem_of_closed (G := baseGraph G A) (fun _ _ _ hadj => hadj.2.2) ha h

theorem base_reachable_imp_reachable {G : SimpleGraph X} {A : Set X} {a b : X}
    (h : (baseGraph G A).Reachable a b) : G.Reachable a b := by
  apply h.elim
  intro w
  clear h
  induction w with
  | nil => exact SimpleGraph.Reachable.refl _
  | cons hadj w ih => exact hadj.1.reachable.trans ih

def attached (G : SimpleGraph X) (A : Set X) (e : X) : Set X :=
  ⋃ a ∈ {a | G.Adj e a ∧ a ∈ A}, graphComponent (baseGraph G A) a

def restored (G : SimpleGraph X) (A S : Set X) : Set X :=
  S ∪ ⋃ e ∈ S, attached G A e

theorem restored_closed {G : SimpleGraph X} {A F : Set X}
    (hF : bridgeEndpoints G A ⊆ F) (hFA : ∀ f ∈ F, f ∉ A) {e : X} (he : e ∉ A)
    {x y : X} (hx : x ∈ restored G A (F ∪ {e})) (hxy : G.Adj x y) :
    y ∈ restored G A (F ∪ {e}) := by
  classical
  by_cases hy : y ∈ A
  · rcases hx with hx | hx
    · exact Or.inr (Set.mem_iUnion.mpr ⟨x, Set.mem_iUnion.mpr ⟨hx,
        Set.mem_iUnion.mpr ⟨y, Set.mem_iUnion.mpr
          ⟨⟨hxy, hy⟩, SimpleGraph.Reachable.refl _⟩⟩⟩⟩)
    · obtain ⟨f, hf⟩ := Set.mem_iUnion.mp hx
      obtain ⟨hfs, hf⟩ := Set.mem_iUnion.mp hf
      obtain ⟨a, ha⟩ := Set.mem_iUnion.mp hf
      obtain ⟨hea, hax⟩ := Set.mem_iUnion.mp ha
      have hxA := base_reachable_mem hea.2 hax
      exact Or.inr (Set.mem_iUnion.mpr ⟨f, Set.mem_iUnion.mpr ⟨hfs,
        Set.mem_iUnion.mpr ⟨a, Set.mem_iUnion.mpr
          ⟨hea, hax.trans (show (baseGraph G A).Adj x y from ⟨hxy, hxA, hy⟩).reachable⟩⟩⟩⟩)
  · rcases hx with hx | hx
    · have hxA : x ∉ A := by
        rcases hx with hx | hx
        · exact hFA x hx
        · have hxe : x = e := hx
          exact hxe ▸ he
      by_cases hxeq : x = y
      · exact Or.inl (hxeq ▸ hx)
      · exact Or.inl (Or.inl (hF ⟨hy, x, hxA, Ne.symm hxeq,
          exceptionalBridge_symm (Or.inl hxy)⟩))
    · obtain ⟨f, hf⟩ := Set.mem_iUnion.mp hx
      obtain ⟨hfs, hf⟩ := Set.mem_iUnion.mp hf
      obtain ⟨a, ha⟩ := Set.mem_iUnion.mp hf
      obtain ⟨hea, hax⟩ := Set.mem_iUnion.mp ha
      by_cases hfy : f = y
      · exact Or.inl (hfy ▸ hfs)
      · have hfA : f ∉ A := by
          rcases hfs with hfF | hfe
          · exact hFA f hfF
          · have hfe' : f = e := hfe
            exact hfe' ▸ he
        have hbridge : exceptionalBridge G A f y :=
          Or.inr ⟨a, x, hea.2, base_reachable_mem hea.2 hax, hea.1, hax, hxy⟩
        exact Or.inl (Or.inl (hF ⟨hy, f, hfA, Ne.symm hfy,
          exceptionalBridge_symm hbridge⟩))

/-- A finite family of finite sets, each of cardinality at most B. -/
theorem finite_biUnion_bound {S : Set X} (hS : S.Finite) (T : X → Set X) (B : ℕ)
    (hT : ∀ x ∈ S, (T x).Finite) (hB : ∀ x ∈ S, (T x).ncard ≤ B) :
    (⋃ x ∈ S, T x).Finite ∧ (⋃ x ∈ S, T x).ncard ≤ S.ncard * B := by
  classical
  refine ⟨hS.biUnion hT, ?_⟩
  calc
    (⋃ x ∈ S, T x).ncard ≤ ∑ x ∈ hS.toFinset, (T x).ncard := by
      simpa only [Set.Finite.mem_toFinset] using hS.toFinset.set_ncard_biUnion_le T
    _ ≤ ∑ _x ∈ hS.toFinset, B :=
      Finset.sum_le_sum (fun x hx => hB x (hS.mem_toFinset.mp hx))
    _ = S.ncard * B := by simp [Set.ncard_eq_toFinset_card S hS]

theorem attached_bound {G : SimpleGraph X} {A : Set X} {M k : ℕ}
    (hbase : ∀ a ∈ A, (graphComponent (baseGraph G A) a).Finite ∧
      (graphComponent (baseGraph G A) a).ncard ≤ M)
    (hdegree : ∀ e, (G.neighborSet e).Finite ∧ (G.neighborSet e).ncard ≤ k) (e : X) :
    (attached G A e).Finite ∧ (attached G A e).ncard ≤ k * M := by
  let N : Set X := {a | G.Adj e a ∧ a ∈ A}
  have hNsub : N ⊆ G.neighborSet e := fun _ h => h.1
  have hN : N.Finite := (hdegree e).1.subset hNsub
  have hNM : N.ncard ≤ k := (Set.ncard_le_ncard hNsub (hdegree e).1).trans (hdegree e).2
  have h := finite_biUnion_bound hN (graphComponent (baseGraph G A)) M
    (fun a ha => (hbase a ha.2).1) (fun a ha => (hbase a ha.2).2)
  exact ⟨h.1, h.2.trans (Nat.mul_le_mul_right M hNM)⟩

theorem restored_bound {G : SimpleGraph X} {A S : Set X} {M k : ℕ}
    (hS : S.Finite)
    (hbase : ∀ a ∈ A, (graphComponent (baseGraph G A) a).Finite ∧
      (graphComponent (baseGraph G A) a).ncard ≤ M)
    (hdegree : ∀ e, (G.neighborSet e).Finite ∧ (G.neighborSet e).ncard ≤ k) :
    (restored G A S).Finite ∧ (restored G A S).ncard ≤ S.ncard * (1 + k * M) := by
  have h := finite_biUnion_bound hS (attached G A) (k * M)
    (fun e _ => (attached_bound hbase hdegree e).1)
    (fun e _ => (attached_bound hbase hdegree e).2)
  refine ⟨hS.union h.1, ?_⟩
  calc
    (restored G A S).ncard ≤ S.ncard + (⋃ e ∈ S, attached G A e).ncard :=
      Set.ncard_union_le _ _
    _ ≤ S.ncard + S.ncard * (k * M) := Nat.add_le_add_left h.2 _
    _ = S.ncard * (1 + k * M) := by ring

/-- Generic restoration theorem.  Exceptions can be infinite; only exceptional
endpoints linked through a single base component must form a finite set. -/
theorem uniform_component_bound_of_finite_bridgeEndpoints
    (G : SimpleGraph X) (A : Set X) (M k : ℕ)
    (hbase : ∀ a ∈ A, (graphComponent (baseGraph G A) a).Finite ∧
      (graphComponent (baseGraph G A) a).ncard ≤ M)
    (hdegree : ∀ e, (G.neighborSet e).Finite ∧ (G.neighborSet e).ncard ≤ k)
    (hF : (bridgeEndpoints G A).Finite) :
    ∀ x, (graphComponent G x).Finite ∧
      (graphComponent G x).ncard ≤
        max M (((bridgeEndpoints G A).ncard + 1) * (1 + k * M)) := by
  classical
  intro x
  by_cases hex : ∃ e, e ∉ A ∧ G.Reachable x e
  · obtain ⟨e, he, hxe⟩ := hex
    let S := bridgeEndpoints G A ∪ {e}
    have hS : S.Finite := hF.union (Set.finite_singleton e)
    have hrest := restored_bound hS hbase hdegree
    have hsub : graphComponent G x ⊆ restored G A S := by
      intro y hy
      exact reachable_mem_of_closed
        (fun _ _ hx hxy => restored_closed (fun _ h => h) (fun _ h => h.1) he hx hxy)
        (Or.inl (Or.inr (Set.mem_singleton e))) (hxe.symm.trans hy)
    refine ⟨hrest.1.subset hsub, ?_⟩
    have hScard : S.ncard ≤ (bridgeEndpoints G A).ncard + 1 := by
      simpa only [Set.ncard_singleton] using Set.ncard_union_le (bridgeEndpoints G A) {e}
    exact ((Set.ncard_le_ncard hsub hrest.1).trans hrest.2).trans
      ((Nat.mul_le_mul_right _ hScard).trans (le_max_right _ _))
  · have hA : ∀ y, G.Reachable x y → y ∈ A := by
      intro y hy
      by_contra hyA
      exact hex ⟨y, hyA, hy⟩
    have hxA := hA x (SimpleGraph.Reachable.refl _)
    have hsub : graphComponent G x ⊆ graphComponent (baseGraph G A) x := by
      intro y hy
      apply reachable_mem_of_closed (G := G)
        (T := graphComponent (baseGraph G A) x) ?_
        (SimpleGraph.Reachable.refl _) hy
      intro a b ha hab
      have hxa : G.Reachable x a := base_reachable_imp_reachable ha
      exact ha.trans (show (baseGraph G A).Adj a b from
        ⟨hab, hA a hxa, hA b (hxa.trans hab.reachable)⟩).reachable
    exact ⟨(hbase x hxA).1.subset hsub,
      ((Set.ncard_le_ncard hsub (hbase x hxA).1).trans (hbase x hxA).2).trans
        (le_max_left _ _)⟩

/-- Distances along a walk are bounded by its number of edges times D. -/
theorem walk_dist_le [PseudoMetricSpace X] {G : SimpleGraph X} {D : ℝ}
    (hedge : ∀ a b, G.Adj a b → dist a b ≤ D) {a b : X} (p : G.Walk a b) :
    dist a b ≤ (p.length : ℝ) * D := by
  induction p with
  | nil => simp
  | @cons a b c hab p ih =>
    calc
      dist a c ≤ dist a b + dist b c := dist_triangle _ _ _
      _ ≤ D + (p.length : ℝ) * D := add_le_add (hedge a b hab) ih
      _ = ((SimpleGraph.Walk.cons hab p).length : ℝ) * D := by
        simp only [SimpleGraph.Walk.length_cons, Nat.cast_add, Nat.cast_one]
        ring

/-- A simple path contains at most as many vertices as its finite component. -/
theorem path_length_add_one_le_component_ncard {G : SimpleGraph X} {a b : X}
    (hfin : (graphComponent G a).Finite) (p : G.Walk a b) (hp : p.IsPath) :
    p.length + 1 ≤ (graphComponent G a).ncard := by
  classical
  have hsub : (p.support.toFinset : Set X) ⊆ graphComponent G a := by
    intro z hz
    exact (p.takeUntil z (List.mem_toFinset.mp hz)).reachable
  have hcard := Set.ncard_le_ncard hsub hfin
  simpa only [Set.ncard_coe_finset, List.toFinset_card_of_nodup hp.support_nodup,
    SimpleGraph.Walk.length_support] using hcard

/-- A bridge between two exceptions has metric length at most (M+1)D
when its base component contains at most M vertices. -/
theorem exceptionalBridge_dist_le [PseudoMetricSpace X]
    {G : SimpleGraph X} {A : Set X} {M : ℕ} {D : ℝ} (hD : 0 ≤ D)
    (hedge : ∀ a b, G.Adj a b → dist a b ≤ D)
    (hbase : ∀ a ∈ A, (graphComponent (baseGraph G A) a).Finite ∧
      (graphComponent (baseGraph G A) a).ncard ≤ M)
    {e f : X} (h : exceptionalBridge G A e f) :
    dist e f ≤ ((M + 1 : ℕ) : ℝ) * D := by
  rcases h with hef | ⟨a, b, ha, _hb, hea, hab, hbf⟩
  · calc
      dist e f ≤ D := hedge e f hef
      _ ≤ ((M + 1 : ℕ) : ℝ) * D := by
        have hM : (1 : ℝ) ≤ ((M + 1 : ℕ) : ℝ) := by
          exact_mod_cast (show (1 : ℕ) ≤ M + 1 by omega)
        simpa using mul_le_mul_of_nonneg_right hM hD
  · obtain ⟨p, hp⟩ := hab.exists_isPath
    have hlength : p.length + 1 ≤ M :=
      (path_length_add_one_le_component_ncard (hbase a ha).1 p hp).trans (hbase a ha).2
    have hpdist : dist a b ≤ (p.length : ℝ) * D :=
      walk_dist_le (G := baseGraph G A) (fun u v huv => hedge u v huv.1) p
    have hcast : ((p.length + 2 : ℕ) : ℝ) ≤ ((M + 1 : ℕ) : ℝ) := by
      exact_mod_cast (show p.length + 2 ≤ M + 1 by omega)
    calc
      dist e f ≤ dist e a + (dist a b + dist b f) :=
        by nlinarith [dist_triangle e a f, dist_triangle a b f]
      _ ≤ D + ((p.length : ℝ) * D + D) :=
        add_le_add (hedge e a hea) (add_le_add hpdist (hedge b f hbf))
      _ = ((p.length + 2 : ℕ) : ℝ) * D := by push_cast; ring
      _ ≤ ((M + 1 : ℕ) : ℝ) * D := mul_le_mul_of_nonneg_right hcast hD

/-- Endpoint set supplied by an arithmetic close-pair finiteness theorem. -/
def closeExceptionalEndpoints [PseudoMetricSpace X] (A : Set X) (R : ℝ) : Set X :=
  {e | e ∉ A ∧ ∃ f, f ∉ A ∧ e ≠ f ∧ dist e f ≤ R}

/-- Metric restoration, with a bound uniform in the starting vertex. -/
theorem uniform_component_bound_of_finite_closeExceptionalEndpoints [PseudoMetricSpace X]
    (G : SimpleGraph X) (A : Set X) (M k : ℕ) (D : ℝ) (hD : 0 ≤ D)
    (hedge : ∀ a b, G.Adj a b → dist a b ≤ D)
    (hbase : ∀ a ∈ A, (graphComponent (baseGraph G A) a).Finite ∧
      (graphComponent (baseGraph G A) a).ncard ≤ M)
    (hdegree : ∀ e, (G.neighborSet e).Finite ∧ (G.neighborSet e).ncard ≤ k)
    (hclose : (closeExceptionalEndpoints A (((M + 1 : ℕ) : ℝ) * D)).Finite) :
    ∀ x, (graphComponent G x).Finite ∧
      (graphComponent G x).ncard ≤
        max M (((closeExceptionalEndpoints A (((M + 1 : ℕ) : ℝ) * D)).ncard + 1) *
          (1 + k * M)) := by
  have hsub : bridgeEndpoints G A ⊆
      closeExceptionalEndpoints A (((M + 1 : ℕ) : ℝ) * D) := by
    rintro e ⟨he, f, hf, hef, hbridge⟩
    exact ⟨he, f, hf, hef, exceptionalBridge_dist_le hD hedge hbase hbridge⟩
  have hF : (bridgeEndpoints G A).Finite := hclose.subset hsub
  intro x
  obtain ⟨hfin, hbound⟩ :=
    uniform_component_bound_of_finite_bridgeEndpoints G A M k hbase hdegree hF x
  refine ⟨hfin, hbound.trans ?_⟩
  exact max_le_max (le_refl M) (Nat.mul_le_mul_right _
    (Nat.add_le_add_right (Set.ncard_le_ncard hsub hclose) 1))

end QuadraticMoat
