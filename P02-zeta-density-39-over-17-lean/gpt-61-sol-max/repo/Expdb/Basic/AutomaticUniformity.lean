module

public import Expdb.Basic.Asymptotics

/-!
# Automatic uniformity

This module formalizes the automatic uniformity results of the blueprint's Basic notation chapter
(`notation-chapter`):
choicewise boundedness or infinitesimality along every variable sequence can be made uniform
after passing to a subsequence.
-/

@[expose] public section

open Filter Topology

namespace Expdb

variable {α : Type*} [SeminormedAddCommGroup α]

/-! ### Auxiliary lemmas for subsequence extraction -/

/-! ### Automatic uniformity (`auto`) -/

/-! ### Full-tail uniformity -/

/-- Infinitesimality along every variable choice is equivalent to convergence that is eventually
uniform over the original variable sets. This strengthens
`automatic_uniformity_of_choicewise_infinitesimal`. -/
theorem VariableFunction.isChoicewiseInfinitesimal_iff_forall_pos_uniform
    (E : VariableObject (Set ℝ)) (hE : ∀ i, (E i).Nonempty)
    (f : VariableFunction (fun i ↦ E i) α) :
    f.IsChoicewiseInfinitesimal ↔
      ∀ ε : ℝ, 0 < ε →
        ∀ᶠ i in atTop, ∀ x : E i, ‖f i x‖ < ε := by
  constructor
  · intro hf ε hε
    classical
    let x₀ : ∀ i, E i := fun i ↦ ⟨(hE i).choose, (hE i).choose_spec⟩
    let x : ∀ i, E i := fun i ↦
      if h : ∃ y : E i, ε ≤ ‖f i y‖ then h.choose else x₀ i
    have hx (i : ℕ) (h : ∃ y : E i, ε ≤ ‖f i y‖) :
        ε ≤ ‖f i (x i)‖ := by
      simp only [x, dite_eq_left h]
      exact h.choose_spec
    have hsmall :=
      (VariableObject.isInfinitesimal_iff_forall_pos
        (fun i ↦ f i (x i))).1 (hf x) ε hε
    by_contra h
    have hfrequent :
        ∃ᶠ i in atTop, ε ≤ ‖f i (x i)‖ := (not_eventually.mp h).mono fun i hi ↦ by
      apply hx i
      simpa only [not_forall, not_lt] using hi
    obtain ⟨i, hilarge, hismall⟩ := (hfrequent.and_eventually hsmall).exists
    exact (not_lt_of_ge hilarge) hismall
  · intro h x
    apply (VariableObject.isInfinitesimal_iff_forall_pos
      (fun i ↦ f i (x i))).2
    intro ε hε
    filter_upwards [h ε hε] with i hi
    exact hi (x i)


