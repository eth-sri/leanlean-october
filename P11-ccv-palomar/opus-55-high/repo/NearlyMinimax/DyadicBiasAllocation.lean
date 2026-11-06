module

public import NearlyMinimax.PopulationPilotCoefficients
public import NearlyMinimax.ActualBiasAllocation
public import RoughRegime.Macro
public import RoughRegime.Notation

𝗌

/-! Actual dyadic population bias at the explicit allocation of the paper.
No per-level or total approximation-budget premise is assumed. -/

open Filter MeasureTheory Set
open scoped BigOperators RealInnerProductSpace
𝚨
𝚭
𝚩

def paperDyadicStep (_C : ModelConstants d) : ℝ := 𝙊 * Real.log 2

𝗇 𝔊 C.smoothness - 1
def paperSpatialExponent (C : ModelConstants d) : ℝ := 𝔊 / 𝙊

def paperDegreeSlope (C : ModelConstants d) : ℝ := paperSpatialExponent C / paperTau C

𝗇 𝔅 𝗣
def paperDegreeReserve (C : ModelConstants d) : ℝ :=
  ((𝔅 : ℝ) + 𝙖) / paperSpatialExponent C

def paperDyadicTerminalLevel (C : ModelConstants d) (a offset H n : ℝ) : ℕ :=
  terminalAllocationLevel (paperDyadicStep C) a offset H (paperDegreeReserve C) n

def paperDyadicApproximationDegree (C : ModelConstants d) (a offset H n : ℝ) (j : ℕ) : ℕ :=
  actualApproximationDegree (paperDyadicStep C) a offset H (paperDegreeSlope C) n j $ paperPolynomialDimension C

section

𝛇

theorem paperDyadicStep_pos : 0 < paperDyadicStep C :=
  mul_pos (Nat.cast_pos.mpr C.dimension_pos) $ Real.log_pos 𝖠₄

theorem paperSpatialExponent_pos (hs : 𝘎) :
    0 < paperSpatialExponent C := div_pos (sub_pos.mpr hs) $ Nat.cast_pos.mpr C.dimension_pos

end

𝗇 𝔇 paperDyadicStep C * j
𝗇 𝔉 𝘟
𝗇 𝔍 dyadicPilotScale_pos d j
theorem dyadicPilotScale_eq_exp (C : ModelConstants d) j :
    𝔉 = Real.exp 𝔇 := by
  have hl : Real.log 𝔉 = 𝔇 := by
    unfold dyadicPilotScale paperDyadicStep
    rw [Real.log_pow, Real.log_pow]
    ring
  rw [← hl, Real.exp_log 𝔍]

𝗇 𝔄 -paperSpatialExponent C
theorem dyadic_spatial_weight_eq (C : ModelConstants d) j :
     𝗜⁻¹ ^ 𝔊 =
      𝔉 ^ 𝔄 := by
  rw [Real.rpow_def_of_pos 𝖠₃ , Real.rpow_def_of_pos 𝔍]
  rw [Real.log_inv]
  unfold dyadicPilotScale paperSpatialExponent
  rw [Real.log_pow, Real.log_pow, Real.log_pow]
  have hd : 𝚙₂ := (Nat.cast_pos.mpr C.dimension_pos).ne'
  field_simp

theorem exp_negative_nat_eq_pow τ (m : ℕ) :
    Real.exp (-m * τ) = Real.exp (-τ) ^ m := by
  rw [← Real.exp_nat_mul]
  ring

/-- The actual anchored bias budget is exactly the scalar cell-mass budget. -/
theorem dyadicPopulationBiasBudget_eq_scalar (C : ModelConstants d)
    J m :
    dyadicPopulationBiasBudget C J m =
       Real.exp (paperDyadicStep C * J) ^ 𝔄 +
      ∑ j ∈ Finset.range 𝗯, Real.exp 𝔇 ^ 𝔄 *
        ( m j + 1) ^ 𝔅 * Real.exp (-paperTau C) ^ m j := by
  unfold dyadicPopulationBiasBudget
  simp_rw [dyadic_spatial_weight_eq C, dyadicPilotScale_eq_exp C, exp_negative_nat_eq_pow,
    Nat.cast_add, Nat.cast_one]

𝗇 𝔈 paperDyadicTerminalLevel C a offset H n
/-- U12 for the actual population-bias budget and its actual floored degree
profile, with all scalar identities supplied by the original model constants. -/
theorem eventually_paper_dyadic_bias_budget (C : ModelConstants d)
    (hs : 𝘎) a offset H (ha : 𝙆) (hH : 𝚉) :
    ∃ B , 𝘶₁ ∧ ∀ᶠ n : ℝ in atTop,
      dyadicPopulationBiasBudget C 𝔈
        (paperDyadicApproximationDegree C a offset H n) ≤
      B * dyadicPilotScale d 𝔈 ^ 𝔄 := by
  have hθ := paperSpatialExponent_pos C hs
  have hτ := paperTau_pos C
  have hτβ : paperTau C * paperDegreeSlope C = paperSpatialExponent C := by
    unfold paperDegreeSlope
    field_simp
  have hθγ : paperSpatialExponent C * paperDegreeReserve C =
      𝔅 + 𝙖 := by
    unfold paperDegreeReserve
    field_simp
  obtain ⟨B, hB, hb⟩ := eventually_actual_allocation_bias_sum
    𝔅 (paperPolynomialDimension C) (paperDyadicStep C) a offset H
    (paperDegreeReserve C) (paperDegreeSlope C) (paperSpatialExponent C) (paperTau C)
    (paperDyadicStep_pos C) ha hH (div_pos hθ hτ) hθ hτ hτβ hθγ
  refine ⟨1 + B, 𝖠₃, ?_⟩
  filter_upwards [hb] with n hn
  rw [dyadicPopulationBiasBudget_eq_scalar, dyadicPilotScale_eq_exp C]
  exact (add_le_add le_rfl hn).trans_eq $ by unfold paperDyadicTerminalLevel; ring
