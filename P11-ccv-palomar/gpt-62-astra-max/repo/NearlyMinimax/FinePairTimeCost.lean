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
    (lo hi : ℝ) (hlo : 0 ≤ lo) (horder : lo ≤ hi) :
    (∫ e : ℝ × FinePairFieldMark d, |e.1| ∂finePairTimeFieldMeasure d lo hi) =
      (hi ^ 2 - lo ^ 2) / 2 := by
  have he : (fun e : ℝ × FinePairFieldMark d => |e.1|) =ᵐ[finePairTimeFieldMeasure d lo hi]
      (fun e => e.1) := by
    filter_upwards [finePairTimeFieldMeasure_ae_time d lo hi] with e he
    exact abs_of_nonneg (hlo.trans he.1)
  rw [integral_congr_ae he, finePairTimeFieldMeasure_fst_integral,
    integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le horder, integral_id]

theorem finePairTimeMatrix_cost_integral {ι : Type*} [Fintype ι]
    (d : ℕ) [NeZero d] (lo hi : ℝ) (hlo : 0 ≤ lo) (horder : lo ≤ hi) (A : ι → ι → ℝ) :
    (∫ e, separatedMatrixCost (finePairTimeMatrix d A) e ∂finePairTimeFieldMeasure d lo hi) =
      (∑ i, ∑ j, |A i j|) * ((hi ^ 2 - lo ^ 2) / 2) := by
  simp_rw [finePairTimeMatrix_cost]
  rw [integral_mul_const, finePairTimeFieldMeasure_abs_time_integral d lo hi hlo horder, mul_comm]

end NearlyMinimax
