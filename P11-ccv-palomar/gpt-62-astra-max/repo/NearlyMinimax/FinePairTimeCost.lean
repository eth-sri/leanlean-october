module

public import NearlyMinimax.FinePairHyperplanePacket
public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

@[expose] public section

/-! Exact Lebesgue-time cost of the genuine time/field carrier. -/
noncomputable section
open MeasureTheory Set
open scoped BigOperators
namespace NearlyMinimax
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 500000

theorem finePairTimeFieldMeasure_abs_time_integral (d : ℕ) [NeZero d]
    {lo hi : ℝ} (hlo : 0 ≤ lo) (horder : lo ≤ hi) :
    (∫ e, |e.1| ∂finePairTimeFieldMeasure d lo hi) =
      (hi ^ 2 - lo ^ 2) / 2 := by
  rw [integral_congr_ae (by
    filter_upwards [(Measure.ae_compProd_of_ae_fst (finePairFieldKernel d) measurableSet_Icc
        (ae_restrict_mem measurableSet_Icc))] with e he
    exact abs_of_nonneg (hlo.trans he.1)), finePairTimeFieldMeasure_fst_integral,
    integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le horder, integral_id]

theorem finePairTimeMatrix_cost_integral {ι : Type*} [Fintype ι]
    (d : ℕ) [NeZero d] {lo hi : ℝ} (hlo : 0 ≤ lo) (horder : lo ≤ hi) (A : ι → ι → ℝ) :
    (∫ e, separatedMatrixCost (finePairTimeMatrix d A) e ∂finePairTimeFieldMeasure d lo hi) =
      (∑ i, ∑ j, |A i j|) * ((hi ^ 2 - lo ^ 2) / 2) := by
  simp_rw [finePairTimeMatrix_cost]
  rw [integral_mul_const, finePairTimeFieldMeasure_abs_time_integral d hlo horder, mul_comm]

end NearlyMinimax
