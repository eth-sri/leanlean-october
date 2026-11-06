module

public import NearlyMinimax.PopulationPilotCoefficients
public import NearlyMinimax.ActualBiasAllocation

@[expose] public section

/-! Actual dyadic population bias at the explicit allocation of the paper.
No per-level or total approximation-budget premise is assumed. -/

noncomputable section
open Filter MeasureTheory Set
open scoped BigOperators RealInnerProductSpace
namespace NearlyMinimax
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false

section
variable {d : ℕ}

def paperDyadicStep  (_C : ModelConstants d)  := (d : ℝ) * Real.log 2

def paperSpatialExponent  (C : ModelConstants d)  := (C.smoothness - 1) / (d : ℝ)

def paperDegreeSlope  (C : ModelConstants d)  := paperSpatialExponent C / paperTau C

def paperDegreeReserve  (C : ModelConstants d)  :=
  ((anchoredDimension d C.order : ℝ) + 1 / 2) / paperSpatialExponent C

def paperDyadicTerminalLevel  (C : ModelConstants d) a offset H n  :=
  terminalAllocationLevel (paperDyadicStep C) a offset H (paperDegreeReserve C) n

def paperDyadicApproximationDegree  (C : ModelConstants d) a offset H n j  :=
  actualApproximationDegree (paperDyadicStep C) a offset H (paperDegreeSlope C) n j (paperPolynomialDimension C)

section
variable (C : ModelConstants d)

theorem paperDyadicStep_pos   : 0 < paperDyadicStep C :=
  mul_pos (Nat.cast_pos.mpr C.dimension_pos) (Real.log_pos (by norm_num))

theorem paperSpatialExponent_pos   (hs : 1 < C.smoothness) :
    0 < paperSpatialExponent C := div_pos (sub_pos.mpr hs) (Nat.cast_pos.mpr C.dimension_pos)

theorem dyadicPilotScale_eq_exp   j :
    dyadicPilotScale d j = Real.exp (paperDyadicStep C * j) := by
  have hl : Real.log (dyadicPilotScale d j) = paperDyadicStep C * (j : ℝ) := by
    unfold dyadicPilotScale paperDyadicStep
    rw [Real.log_pow, Real.log_pow]
    ring
  rw [← hl, Real.exp_log (dyadicPilotScale_pos d j)]

theorem dyadic_spatial_weight_eq   j :
    ((2 ^ j)⁻¹) ^ (C.smoothness - 1) =
      (dyadicPilotScale d j) ^ (-paperSpatialExponent C) := by
  rw [Real.rpow_def_of_pos (by positivity), Real.rpow_def_of_pos (dyadicPilotScale_pos d j)]
  rw [Real.log_inv]
  unfold dyadicPilotScale paperSpatialExponent
  rw [Real.log_pow, Real.log_pow, Real.log_pow]
  
  have hd : (d : ℝ) ≠ 0 := (Nat.cast_pos.mpr C.dimension_pos).ne'
  field_simp
end

end


theorem exp_negative_nat_eq_pow τ (m : ℕ) :
    Real.exp (-m * τ) = (Real.exp (-τ)) ^ m := by
  rw [← Real.exp_nat_mul]
  
  ring

section
variable {d : ℕ} (C : ModelConstants d)

/-- The actual anchored bias budget is exactly the scalar cell-mass budget. -/
theorem dyadicPopulationBiasBudget_eq_scalar 
    J m :
    dyadicPopulationBiasBudget C J m =
      (Real.exp (paperDyadicStep C * J)) ^ (-paperSpatialExponent C) +
      ∑ j ∈ Finset.range (J + 1), (Real.exp (paperDyadicStep C * j)) ^ (-paperSpatialExponent C) *
        ((m j) + 1) ^ anchoredDimension d C.order * (Real.exp (-paperTau C)) ^ m j := by
  unfold dyadicPopulationBiasBudget
  simp_rw [dyadic_spatial_weight_eq C, dyadicPilotScale_eq_exp C, exp_negative_nat_eq_pow,
    Nat.cast_add, Nat.cast_one]

/-- U12 for the actual population-bias budget and its actual floored degree
profile, with all scalar identities supplied by the original model constants. -/
theorem eventually_paper_dyadic_bias_budget 
    (hs : 1 < C.smoothness) a offset H (ha : 0 < a) (hH : 0 < H) :
    ∃ B : ℝ, 0 < B ∧ ∀ᶠ n : ℝ in atTop,
      dyadicPopulationBiasBudget C (paperDyadicTerminalLevel C a offset H n)
        (paperDyadicApproximationDegree C a offset H n) ≤
      B * (dyadicPilotScale d (paperDyadicTerminalLevel C a offset H n)) ^ (-paperSpatialExponent C) := by
  have hθ := paperSpatialExponent_pos C hs
  have hτ := paperTau_pos C
  have hβ : 0 < paperDegreeSlope C := div_pos hθ hτ
  have hτβ : paperTau C * paperDegreeSlope C = paperSpatialExponent C := mul_div_cancel₀ _ hτ.ne'
  have hθγ : paperSpatialExponent C * paperDegreeReserve C =
      (anchoredDimension d C.order : ℝ) + 1 / 2 := mul_div_cancel₀ _ hθ.ne'
  obtain ⟨B, hB, hb⟩ := eventually_actual_allocation_bias_sum
    (anchoredDimension d C.order) (paperPolynomialDimension C) (paperDyadicStep C) a offset H
    (paperDegreeReserve C) (paperDegreeSlope C) (paperSpatialExponent C) (paperTau C)
    (paperDyadicStep_pos C) ha hH hβ hθ hτ hτβ hθγ
  refine ⟨1 + B, by positivity, ?_⟩
  filter_upwards [hb] with n hn
  rw [dyadicPopulationBiasBudget_eq_scalar, dyadicPilotScale_eq_exp C]
  
  exact (add_le_add le_rfl hn).trans_eq (by unfold paperDyadicTerminalLevel; ring)
end


end NearlyMinimax
