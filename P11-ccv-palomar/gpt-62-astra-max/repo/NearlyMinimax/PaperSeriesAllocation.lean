module

public import NearlyMinimax.PaperDegreeGuards
public import NearlyMinimax.PilotSeriesEnvelope
public import NearlyMinimax.ActualVarianceAllocation

@[expose] public section

/-! The genuine factorial-pilot envelope is bounded by the scalar allocation.
Every degree and sample-denominator guard follows from the actual paper profile. -/
noncomputable section
open Filter
open scoped BigOperators
namespace NearlyMinimax
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false

section
variable {d : ℕ} (C : ModelConstants d) (A Λ : ℝ) (j m D : ℕ)

def paperPilotMomentFactor : ℝ :=
  A ^ 2 * (Fintype.card (incrementVariables (anchoredDimension d C.order)) *
    preconditionedPilotMomentConstant C C.order)

theorem paperPilotMomentFactor_nonneg :
    0 ≤ paperPilotMomentFactor C A := by
  exact mul_nonneg (sq_nonneg _) (mul_nonneg (Nat.cast_nonneg _) (preconditionedPilotMomentConstant_pos C _).le)

theorem dyadicPilotSeries_eq_factorialSeries :
    dyadicPilotSeries C A Λ j m = factorialSeries (m + anchoredDimension d C.order + 1)
      (paperPilotMomentFactor C A * dyadicPilotScale d j / Λ) := by
  unfold dyadicPilotSeries factorialSeries paperPilotMomentFactor
  simpa only [mul_assoc] using (Fin.sum_univ_eq_sum_range (fun k =>
    (k + 1).factorial *
      (A ^ 2 * dyadicFeatureEnergy C j / Λ) ^ (k + 1))
    (m + anchoredDimension d C.order + 1))

theorem factorialSeries_mono_argument {x y : ℝ} (hx : 0 ≤ x) (hxy : x ≤ y) :
    factorialSeries D x ≤ factorialSeries D y := by
  exact Finset.sum_le_sum fun k _ =>
    mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hx hxy _) (Nat.cast_nonneg _)

end

section
variable {d : ℕ} {C : ModelConstants d} {A a offset n Λ C₀ C_D : ℝ} (hn : 0 < n) (hΛ : n / 12 ≤ Λ)
include hn hΛ

/-- A genuine pilot block denominator and a fixed model constant dominate the
actual raw-feature moment argument. -/
theorem paper_pilot_series_argument_le
    (hC : 12 * paperPilotMomentFactor C A ≤ C₀) (j : ℕ) :
    paperPilotMomentFactor C A * dyadicPilotScale d j / Λ ≤ C₀ * dyadicPilotScale d j / n := by
  have hp := paperPilotMomentFactor_nonneg C A
  have hk := (dyadicPilotScale_pos d j).le
  have hΛpos  := (div_pos hn (by norm_num)).trans_le hΛ
  have hCpos  := (mul_nonneg (by norm_num) hp).trans hC
  apply (div_le_div_iff₀ hΛpos hn).mpr
  have hm := mul_le_mul_of_nonneg_right hC hk
  have hnΛ := mul_le_mul_of_nonneg_left hΛ (mul_nonneg hCpos hk)
  nlinarith

/-- Exact total degree and original normalization give a levelwise domination
by the already-proved scalar variance profile. -/
theorem paper_pilot_series_weight_le_profile (hΛn : Λ ≤ n)
    (hC : 0 < C₀) (hD : 0 < C_D) (hS : 0 < allocationWidth a offset n)
    (hcoef : 12 * paperPilotMomentFactor C A ≤ C₀) {j : ℕ}
    (hdegree : paperDyadicTotalDegree C a offset (C₀ * C_D) n j =
      Nat.floor (paperDegreeSlope C * quadraticProfile (allocationWidth a offset n)
        (allocationLevelPosition (paperDyadicStep C) a offset (C₀ * C_D) n j))) :
    dyadicPilotSeries C A Λ j (paperDyadicApproximationDegree C a offset (C₀ * C_D) n j) *
        max 1 (Λ / dyadicPilotScale d j) ≤
      profileVarianceWeight C₀ C_D (paperDegreeSlope C) (allocationWidth a offset n)
        (allocationLevelPosition (paperDyadicStep C) a offset (C₀ * C_D) n j) := by
  rw [((by unfold profileVarianceWeight; rw [actual_profileVarianceArgument_eq_cell_fraction j hC hD hn hS]; field_simp : profileVarianceWeight C₀ C_D (paperDegreeSlope C) (allocationWidth a offset n) (allocationLevelPosition (paperDyadicStep C) a offset (C₀ * C_D) n j) = factorialSeries (profileVarianceDegree (paperDegreeSlope C) (allocationWidth a offset n) (allocationLevelPosition (paperDyadicStep C) a offset (C₀ * C_D) n j)) (C₀ * Real.exp (paperDyadicStep C * ↑j) / n) * max 1 (n / Real.exp (paperDyadicStep C * ↑j)))), ← dyadicPilotScale_eq_exp C]
  rw [dyadicPilotSeries_eq_factorialSeries]
  have hΛpos  := (div_pos hn (by norm_num)).trans_le hΛ
  have hx : 0 ≤ paperPilotMomentFactor C A * dyadicPilotScale d j / Λ :=
    div_nonneg (mul_nonneg (paperPilotMomentFactor_nonneg C A) (dyadicPilotScale_pos _ _).le) hΛpos.le
  have hseries := factorialSeries_mono_argument
    (paperDyadicTotalDegree C a offset (C₀ * C_D) n j) hx
    (paper_pilot_series_argument_le hn hΛ hcoef j)
  rw [hdegree] at hseries
  change factorialSeries (paperDyadicTotalDegree C a offset (C₀ * C_D) n j) _ * _ ≤ _
  rw [hdegree]
  exact mul_le_mul hseries (max_le_max le_rfl (div_le_div_of_nonneg_right hΛn (dyadicPilotScale_pos _ _).le))
    (by positivity) (factorialSeries_nonneg _
      (div_nonneg (mul_nonneg hC.le (dyadicPilotScale_pos _ _).le) hn.le))

end

/-- Uniform comparison of the actual maximum series on the actual three-block
pilot sample with the scalar maximum at H=C₀ C_D. -/
theorem eventually_paper_dyadic_series_envelope_le {d : ℕ} {C : ModelConstants d}
    (hs : 1 < C.smoothness) (A a offset C₀ C_D : ℝ)
    (ha : 0 < a) (hC : 0 < C₀) (hD : 0 < C_D)
    (hcoef : 12 * paperPilotMomentFactor C A ≤ C₀) :
    ∀ᶠ n in atTop,
      dyadicSeriesEnvelope C A ((threeBlockSize n) / 2)
        (paperDyadicTerminalLevel C a offset (C₀ * C_D) n)
        (paperDyadicApproximationDegree C a offset (C₀ * C_D) n) ≤
      actualVarianceMaximum (paperDyadicStep C) a offset C₀ C_D (paperDegreeReserve C) (paperDegreeSlope C) n := by
  have hdegree  :=
    tendsto_natCast_atTop_atTop.eventually (eventually_paper_total_degree_eq_floor hs a offset (C₀ * C_D) ha)
  have hwidth  :=
    tendsto_natCast_atTop_atTop.eventually
      ((allocationWidth_tendsto_atTop ha offset).eventually (eventually_gt_atTop 0))
  filter_upwards [hdegree, hwidth, eventually_ge_atTop 6] with n hd hS h6
  have hn : (0 : ℝ) < n := by positivity
  have hΛ : n / 12 ≤ (threeBlockSize n : ℝ) / 2 := by linarith [threeBlockSize_fraction h6]
  have hΛn : (threeBlockSize n : ℝ) / 2 ≤ n := by
    have hm : threeBlockSize n ≤ n := by unfold threeBlockSize; omega
    have hmR : (threeBlockSize n : ℝ) ≤ n := by exact_mod_cast hm
    bound
  apply Finset.sup'_le
  intro j _
  apply (paper_pilot_series_weight_le_profile hn hΛ hΛn hC hD hS hcoef (hd j.val)).trans
  exact Finset.le_sup' (fun i => profileVarianceWeight C₀ C_D (paperDegreeSlope C) (allocationWidth a offset n)
      (allocationLevelPosition (paperDyadicStep C) a offset (C₀ * C_D) n i)) (Finset.mem_range.mpr j.isLt)

end NearlyMinimax
