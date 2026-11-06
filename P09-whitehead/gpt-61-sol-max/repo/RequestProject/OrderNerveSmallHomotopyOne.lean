import Mathlib.Tactic

import RequestProject.OrderNerveSmallSingularApproximation

namespace FiniteChains.Comb
open TopologicalSingular SingularSubdivision

variable {P : Type}
/-- Fill the comparison discrepancy on a one-simplex after correcting its endpoints. -/
theorem orderSmallHomotopyOneFill_exists  [PartialOrder P]
    (σ : OrderSmallSimplex P 1) :
    ∃ b : Chain (orderNerveRealization P) 2, b ∈ orderSingularCarrierChains σ.val 2 ∧
      boundary 1 b = Finsupp.single σ.val 1 -
        orderSmallSingularApproximation1 (orderSmallSingle σ 1) -
        orderSmallHomotopy0 (smallBoundary (orderNerveRealizationOpenStar P) 0 (orderSmallSingle σ 1)) := by
  apply orderSingularCarrierChains_cycle_bounds σ.val σ.property 0
  · simp_all [Submodule.sub_mem, FiniteChains.Comb.orderSingularCarrierChains_single, FiniteChains.Comb.orderSmallSingularApproximation1_carrier, FiniteChains.Comb.orderSmallBoundary_map_carrier, FiniteChains.Comb.orderSmallHomotopy0_carrier]
  · rw [map_sub, map_sub, orderSmallSingularApproximation1_boundary, orderSmallHomotopy0_boundary]
    exact sub_self _

noncomputable def orderSmallHomotopy1  [PartialOrder P]  :=
  (Finsupp.linearCombination ℤ (fun σ => (orderSmallHomotopyOneFill_exists σ).choose)).comp
    (orderSmallChainEquiv P 1).toLinearMap

theorem orderSmallHomotopy1_single  [PartialOrder P]
    (σ : OrderSmallSimplex P 1) :
    orderSmallHomotopy1 (orderSmallSingle σ 1) = (orderSmallHomotopyOneFill_exists σ).choose := by
  have he := (orderSmallChainEquiv P 1).apply_symm_apply (Finsupp.single σ 1)
  rw [orderSmallChainEquiv_symm_single] at he
  change (Finsupp.linearCombination ℤ (fun τ : OrderSmallSimplex P 1 =>
    (orderSmallHomotopyOneFill_exists τ).choose))
      ((orderSmallChainEquiv P 1) (orderSmallSingle σ 1)) = _
  rw [he, Finsupp.linearCombination_single, one_smul]

theorem orderSmallHomotopy1_carrier  [PartialOrder P]
    (σ : OrderSmallSimplex P 1) :
    orderSmallHomotopy1 (orderSmallSingle σ 1) ∈ orderSingularCarrierChains σ.val 2 := by
  rw [orderSmallHomotopy1_single]
  exact (orderSmallHomotopyOneFill_exists σ).choose_spec.1

theorem orderSmallHomotopy1_boundary  [PartialOrder P]
    (c : smallChains (orderNerveRealizationOpenStar P) 1) :
    boundary 1 (orderSmallHomotopy1 c) = c.val - orderSmallSingularApproximation1 c -
      orderSmallHomotopy0 (smallBoundary (orderNerveRealizationOpenStar P) 0 c) := by
  have he : (boundary 1).comp orderSmallHomotopy1 =
      (smallChains (orderNerveRealizationOpenStar P) 1).subtype - orderSmallSingularApproximation1 -
        orderSmallHomotopy0.comp (smallBoundary (orderNerveRealizationOpenStar P) 0) := by
    apply orderSmallSingle_spans
    intro σ
    simp only [LinearMap.comp_apply, LinearMap.sub_apply, orderSmallHomotopy1_single]
    exact (orderSmallHomotopyOneFill_exists σ).choose_spec.2
  exact DFunLike.congr_fun he c

end FiniteChains.Comb
