module

public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Algebra.GroupWithZero.Indicator
public import Mathlib.Data.Fintype.BigOperators
public import Mathlib.Basic.Real.Basic

@[expose] public section

namespace PottsDiscontinuity

private theorem sum_bool_pairs {X Ω : Type*} [Fintype X] [Fintype Ω]
    (e : Ω ≃ X × Bool) (f : Ω → ℝ) :
    ∑ A, f A = ∑ x, (f (e.symm (x, false)) + f (e.symm (x, true))) := by
  rw [← e.symm.sum_comp f, Fintype.sum_prod_type]
  simp [add_comm]

/-- Pointwise bounds on the fraction of mass in one state of a pair sum to
bounds on the mass of that state in any event stable on the pairs. -/
theorem pairedMass_bounds {X Ω : Type*} [Fintype X] [Fintype Ω]
    (e : Ω ≃ X × Bool) (w : Ω → ℝ) (S T : Set Ω) (i : Bool) {a b : ℝ}
    (hs : ∀ x, e.symm (x, true) ∈ S ↔ e.symm (x, false) ∈ S)
    (ht : ∀ x j, e.symm (x, j) ∈ T ↔ j = i)
    (h : ∀ x, a * (w (e.symm (x, false)) + w (e.symm (x, true))) ≤ w (e.symm (x, i)) ∧
      w (e.symm (x, i)) ≤ b * (w (e.symm (x, false)) + w (e.symm (x, true)))) :
    a * (∑ A, S.indicator w A) ≤ ∑ A, (S ∩ T).indicator w A ∧
      ∑ A, (S ∩ T).indicator w A ≤ b * ∑ A, S.indicator w A := by
  classical
  simp only [sum_bool_pairs e, Set.indicator, Set.mem_inter_iff, hs, ht, Finset.mul_sum]
  refine ⟨Finset.sum_le_sum fun x _ => ?_, Finset.sum_le_sum fun x _ => ?_⟩ <;>
    (have hx := h x; by_cases H : e.symm (x, false) ∈ S <;> cases i <;> simp_all)

end PottsDiscontinuity
