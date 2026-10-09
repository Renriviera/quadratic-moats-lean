import QuadraticMoat.Model
import Mathlib.RingTheory.DedekindDomain.Ideal.Lemmas

/-! The graph of nonzero elements with bounded distinct prime-ideal support.
Prime-ideal valuations are unrestricted, and units belong to every budget. -/

namespace QuadraticMoat.BoundedFactors

open NumberField UniqueFactorizationMonoid
open scoped Classical

variable (K : Type*) [Field K] [NumberField K]

noncomputable def omega (α : 𝓞 K) : ℕ :=
  (normalizedFactors (Ideal.span ({α} : Set (𝓞 K)))).toFinset.card

/-- Zero is explicitly excluded: its normalized factor list is empty. -/
abbrev Vertex (b : ℕ) := {α : 𝓞 K // α ≠ 0 ∧ omega K α ≤ b}

noncomputable def graph (b : ℕ) (D : ℝ) : SimpleGraph (Vertex K b) where
  Adj α β := α ≠ β ∧ minkowskiDist K α.val β.val ≤ D
  symm := by
    constructor
    intro α β h
    exact ⟨h.1.symm, by simpa only [minkowskiDist, dist_comm] using h.2⟩
  loopless := by
    constructor
    intro α h
    exact h.1 rfl

def component (b : ℕ) (D : ℝ) (α : Vertex K b) : Set (Vertex K b) :=
  {β | (graph K b D).Reachable α β}

def UniformEndpoint : Prop :=
  ∀ b : ℕ, ∀ D : ℝ, ∃ B : ℕ, ∀ α : Vertex K b,
    (component K b D α).Finite ∧ (component K b D α).ncard ≤ B

@[simp] theorem omega_zero : omega K 0 = 0 := by
  unfold omega
  rw [Ideal.span_singleton_eq_bot.mpr rfl]
  change (normalizedFactors (0 : Ideal (𝓞 K))).toFinset.card = 0
  rw [normalizedFactors_zero]
  rfl

@[simp] theorem omega_of_isUnit {α : 𝓞 K} (hα : IsUnit α) : omega K α = 0 := by
  unfold omega
  rw [Ideal.span_singleton_eq_top.mpr hα]
  rw [← Ideal.one_eq_top]
  rw [normalizedFactors_one]
  rfl

theorem unit_mem_vertex (b : ℕ) {α : 𝓞 K} (hα : IsUnit α) :
    α ≠ 0 ∧ omega K α ≤ b := by
  exact ⟨hα.ne_zero, by simp [omega_of_isUnit K hα]⟩

end QuadraticMoat.BoundedFactors
