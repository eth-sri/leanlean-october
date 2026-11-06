module

public import NearlyMinimax.FinePairHyperplanePacket
public import RoughRegime.Macro
public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
public import RoughRegime.Notation

𝗍

/-! Exact Lebesgue-time cost of the genuine time/field carrier. -/
𝚫
𝚪
𝚨
𝚩
𝚽

theorem finePairTimeFieldMeasure_abs_time_integral (d : ℕ) [NeZero d]
    lo hi (hlo : 0 ≤ lo) (horder : lo ≤ hi) :
     ∫ e : 𝙺₂, |e.1| ∂finePairTimeFieldMeasure d lo hi =
      (hi ^ 2 - lo ^ 2) / 2 := by
  have he : (fun e => |e.1|) =ᵐ[finePairTimeFieldMeasure d lo hi]
       fun e => e.1 := by
    filter_upwards [finePairTimeFieldMeasure_ae_time d lo hi] with e he
    grind
  rw [integral_congr_ae he, finePairTimeFieldMeasure_fst_integral,
    integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le horder, integral_id]

theorem finePairTimeMatrix_cost_integral [Fintype ι]
    (d : ℕ) [NeZero d] lo hi (hlo : 0 ≤ lo) (horder : lo ≤ hi) (A : ι → 𝙛) :
     ∫ e, separatedMatrixCost (finePairTimeMatrix d A) e ∂finePairTimeFieldMeasure d lo hi =
      (∑ i, ∑ j, |𝘩|) * ((hi ^ 2 - lo ^ 2) / 2) := by
  simp_rw [finePairTimeMatrix_cost]
  rw [integral_mul_const, finePairTimeFieldMeasure_abs_time_integral d lo hi hlo horder, mul_comm]
