module

public import HypoellipticAleksandrov.KineticAleksandrov.Counterexample.Geometry
public import Mathlib.Analysis.SpecialFunctions.SmoothTransition
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
public import Mathlib.Analysis.Convex.Deriv
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Tactic.Linarith

/-!
# A fixed convex flattening function

Integrating the smooth transition constructs the source's flattening function.
The function and its eventual affine offset are independent of the dilation scale.
-/

@[expose] public section

namespace HypoellipticAleksandrov.KineticAleksandrov.Counterexample

open MeasureTheory Set
open scoped ContDiff

/-- The fixed slope interpolating between zero and one on the source interval. -/
noncomputable def flatteningSlope (s : ℝ) : ℝ := Real.smoothTransition (s - 1)

/-- The convex primitive used to flatten the singular profile. -/
noncomputable def flatteningPsi (s : ℝ) : ℝ := ∫ t in (1 : ℝ)..s, flatteningSlope t

/-- The offset in the eventual affine formula for the flattening function. -/
noncomputable def flatteningOffset : ℝ := 2 - flatteningPsi 2

/-- The slope is infinitely differentiable. -/
theorem contDiff_flatteningSlope : ContDiff ℝ ∞ flatteningSlope :=
  Real.smoothTransition.contDiff.comp (contDiff_id.sub contDiff_const)

/-- The slope is nondecreasing. -/
theorem monotone_flatteningSlope : Monotone flatteningSlope := fun s t h => Real.smoothTransition.monotone (sub_le_sub_right h 1)

/-- The flattening primitive has the specified derivative. -/
theorem deriv_flatteningPsi (s : ℝ) : deriv flatteningPsi s = flatteningSlope s :=
  contDiff_flatteningSlope.continuous.deriv_integral flatteningSlope 1 s

/-- The flattening function is smooth of every finite order. -/
theorem contDiff_flatteningPsi : ContDiff ℝ ∞ flatteningPsi := by
  apply contDiff_infty_iff_deriv.2
  constructor
  · intro s
    exact (contDiff_flatteningSlope.continuous.integral_hasStrictDerivAt 1 s)
      |>.hasDerivAt.differentiableAt
  · simpa [funext deriv_flatteningPsi] using contDiff_flatteningSlope

section
variable (s : ℝ)

/-- The primitive is zero to the left of the flattening threshold. -/
theorem flatteningPsi_eq_zero (hs : s ≤ 1) : flatteningPsi s = 0 := by
  unfold flatteningPsi
  rw [intervalIntegral.integral_symm (a := s) (b := 1)]
  have he : (∫ t in s..1, flatteningSlope t) = ∫ t in s..1, 0 := by
    apply intervalIntegral.integral_congr
    rw [uIcc_of_le hs]
    intro t ht
    exact Real.smoothTransition.zero_of_nonpos (sub_nonpos.mpr ht.2)
  rw [he]
  simp

/-- The primitive is affine past the transition region. -/
theorem flatteningPsi_eq_affine (hs : 2 ≤ s) :
    flatteningPsi s = s - flatteningOffset := by
  have hi := contDiff_flatteningSlope.continuous
  have he : (∫ t in 2..s, flatteningSlope t) = ∫ t in 2..s, 1 := by
    apply intervalIntegral.integral_congr
    rw [uIcc_of_le hs]
    intro t ht
    exact Real.smoothTransition.one_of_one_le (by linarith only [ht.1])
  unfold flatteningOffset
  simp only [flatteningPsi]
  rw [← (intervalIntegral.integral_add_adjacent_intervals (hi.intervalIntegrable (μ := volume) 1 2) (hi.intervalIntegrable (μ := volume) 2 s)), he, intervalIntegral.integral_const]
  ring

end

/-- The transition primitive has strictly intermediate height at the upper threshold. -/
theorem flatteningPsi_two_bounds : 0 < flatteningPsi 2 ∧ flatteningPsi 2 < 1 := by
  have hc := contDiff_flatteningSlope.continuous
  have hpos := intervalIntegral.integral_lt_integral_of_continuousOn_of_le_of_exists_lt
    (by norm_num) continuous_const.continuousOn hc.continuousOn
    (fun t _ => Real.smoothTransition.nonneg (t - 1))
    (show ∃ t ∈ Icc 1 2, 0 < flatteningSlope t from
      ⟨3 / 2, by norm_num,
        Real.smoothTransition.pos_of_pos (by norm_num)⟩)
  have hlt := intervalIntegral.integral_lt_integral_of_continuousOn_of_le_of_exists_lt
    (by norm_num) hc.continuousOn continuous_const.continuousOn
    (fun t _ => Real.smoothTransition.le_one (t - 1))
    (show ∃ t ∈ Icc 1 2, flatteningSlope t < 1 from
      ⟨3 / 2, by norm_num,
        Real.smoothTransition.lt_one_of_lt_one (by norm_num)⟩)
  simpa [intervalIntegral.integral_zero, intervalIntegral.integral_const, flatteningPsi, show (2 - 1 : ℝ) = 1 by ring] using And.intro hpos hlt

/-- The affine offset lies strictly between the source's two thresholds. -/
theorem flatteningOffset_bounds : 1 < flatteningOffset ∧ flatteningOffset < 2 := by
  have hb := flatteningPsi_two_bounds
  unfold flatteningOffset
  constructor <;> linarith only [hb.1, hb.2]

section
variable (s : ℝ)

end

/-- The primitive is nonnegative at every nonnegative argument. -/
theorem flatteningPsi_nonneg (s : ℝ) : 0 ≤ flatteningPsi s := by
  by_cases h : s ≤ 1
  · rw [flatteningPsi_eq_zero s h]
  · exact intervalIntegral.integral_nonneg_of_forall (le_of_not_ge h)
      (fun t => Real.smoothTransition.nonneg (t - 1))

variable {d : ℕ} (H : XV d → ℝ) (alpha r : ℝ) (hr : 0 < r) (q : XV d)

end HypoellipticAleksandrov.KineticAleksandrov.Counterexample
