module

public import NearlyMinimax.HighWindowFactorialEnergy

@[expose] public section

/-! Finite count partition used by the original sample-design Fisher sum.
It retains the radial count two, the actual refined counts through D, and
the exterior-degree tail without imposing a relation between n and D. -/
noncomputable section
open scoped BigOperators
namespace NearlyMinimax

theorem finite_refined_sum_le_start_two D (f : ℕ → ℝ) (hf : ∀ r, 0 ≤ f r) :
    (∑ j ∈ Finset.range (D-2), f (3+j)) ≤
      ∑ j ∈ Finset.range (D-1), f (2+j) := by
  apply Finset.sum_le_sum_of_injOn (fun j => j+1)
  · intro i _ j _ hij
    change i+1=j+1 at hij
    omega
  · grind
  · intro j _
    exact le_of_eq (by congr 1; omega)
  · intro j _ _
    exact hf _

theorem finite_refined_gated_sum_le_tail D M (f : ℕ → ℝ)
    (hf : ∀ r, 0 ≤ f r) :
    (∑ j ∈ Finset.range (D-2), if M<3+j then f (3+j) else 0) ≤
      ∑ j ∈ Finset.range (D-M), f (M+1+j) := by
  classical
  rw [← Finset.sum_filter]
  apply Finset.sum_le_sum_of_injOn (fun j => 3+j-(M+1))
  · intro i hi j hj hij
    grind
  · grind
  · simp_all
  · intro j _ _
    exact hf _

theorem finite_refined_sum_eq_start_four D (hD : 3 ≤ D)
    (f : ℕ → ℝ) (hf3 : f 3 = 0) :
    (∑ j ∈ Finset.range (D-2), f (3+j)) =
      ∑ j ∈ Finset.range (D-3), f (4+j) := by
  rw [show D-2=(D-3)+1 by omega, Finset.sum_range_succ']
  grind

theorem finite_count_energy_from_blocks {x } (hx : 0 ≤ x) n D (hD : 2 ≤ D)
    (e : ℕ → ℝ) (he : ∀ r, 0 ≤ e r) (he0 : e 0 = 0) (he1 : e 1 = 0)
    E2 Eref Etail
    (h2 : poissonCountWeight x 2 * e 2 ≤ E2)
    (href : (∑ r ∈ Finset.range (D-2), poissonCountWeight x (3+r) * e (3+r)) ≤ Eref)
    (htail : (∑ r ∈ Finset.range (n+1), poissonCountWeight x (D+1+r) * e (D+1+r)) ≤ Etail) :
    (∑ r ∈ Finset.range (n+1), poissonCountWeight x r * e r) ≤ E2+Eref+Etail := by
  have hf (r : ℕ) : 0 ≤ poissonCountWeight x r * e r :=
    mul_nonneg (poissonCountWeight_nonneg hx r) (he r)
  have hprefix : (∑ r ∈ Finset.range (D+1), poissonCountWeight x r * e r) ≤ E2+Eref := by
    have hlen : D+1 = 3+(D-2) := by omega
    rw [hlen, Finset.sum_range_add]
    have hthree : (∑ r ∈ Finset.range 3, poissonCountWeight x r * e r) =
        poissonCountWeight x 2 * e 2 := by
      simp [Finset.sum_range_succ, he0, he1]
    rw [hthree]
    exact add_le_add h2 href
  calc
    _ ≤ ∑ r ∈ Finset.range ((D+1)+(n+1)), poissonCountWeight x r * e r := by
      simp_all [Finset.sum_le_sum_of_subset_of_nonneg]
    _ = (∑ r ∈ Finset.range (D+1), poissonCountWeight x r * e r) +
        (∑ r ∈ Finset.range (n+1), poissonCountWeight x (D+1+r) * e (D+1+r)) := by
      rw [Finset.sum_range_add]
    _ ≤ _ := add_le_add hprefix htail

end NearlyMinimax
