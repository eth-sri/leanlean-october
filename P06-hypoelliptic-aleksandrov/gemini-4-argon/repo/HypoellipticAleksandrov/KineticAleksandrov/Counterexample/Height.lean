module

public import HypoellipticAleksandrov.KineticAleksandrov.Counterexample.TimeCutoff
import Mathlib.Topology.Order.Basic
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Tactic.Linarith
import HypoellipticAleksandrov.Analysis.EuclideanNormCalculus
import HypoellipticAleksandrov.KineticAleksandrov.Operator
import Mathlib.Analysis.Calculus.FDeriv.Const
import Mathlib.Analysis.Calculus.FDeriv.Mul
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import HypoellipticAleksandrov.KineticAleksandrov.Counterexample.Geometry
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Analysis.Convex.Deriv
import Mathlib.Analysis.SpecialFunctions.SmoothTransition
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-!
# Terminal height of the explicit cutoff

The terminal value is a height estimate; an interior witness additionally uses continuity.
-/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.KineticAleksandrov.Counterexample
open Set Filter
open scoped Topology
open HypoellipticAleksandrov.Parabolic
open scoped BigOperators MatrixOrder
open MeasureTheory
open scoped ContDiff

/- The barrier takes the exact value one quarter at the terminal spatial origin. -/
theorem timeCutoff_height {d } (H : XV d → ℝ) (alpha r mu R : ℝ)
    (hH : H 0 = 0) (hr : 0 < r) (hmu : 0 < mu)
    (hsmall : flatteningOffset * Real.rpow r alpha ≤ 1 / 4) :
    3 / 8 ≤ timeCutoffProfile H alpha r mu R ⟨barrierTime mu, 0, 0⟩ := by
  have hf : flatProfile H flatteningPsi flatteningOffset alpha r (0 : XV d) = 1 - flatteningOffset * Real.rpow r alpha := by
    let q := (0 : XV d)
    have hq : H (0 : XV d) ≤ Real.rpow r alpha := by
      rw [hH]; exact (Real.rpow_pos_of_pos hr alpha).le
    unfold flatProfile
    simp only [Real.rpow_eq_pow] at hq ⊢
    rw [flatteningPsi_eq_zero _ ((div_le_one (Real.rpow_pos_of_pos hr alpha)).2 hq)]
    ring
  unfold timeCutoffProfile
  change 3 / 8 ≤ timeCutoffTheta
    (flatProfile H flatteningPsi flatteningOffset alpha r 0 -
      barrier mu R (⟨barrierTime mu, 0, 0⟩ : KineticPoint d))
  have _h_xinl_0 : Real.exp (-mu * barrierTime mu) = (1 / 8 : ℝ) := by
    have he : -mu * barrierTime mu = -Real.log 8 := by
      unfold barrierTime
      field_simp
    rw [he, Real.exp_neg, Real.exp_log (by norm_num)]
    norm_num
  have _h_inl_10 : barrier mu R (⟨barrierTime mu, 0, 0⟩ : KineticPoint d) = 1 / 4 := by
      simp only [barrier, _h_xinl_0, PDE.vecNormSq, PDE.vecDot,
        Pi.zero_apply, mul_zero, Finset.sum_const_zero, zero_div, sub_zero]
      norm_num

    /- A small flattening scale gives the terminal height required in Appendix C. -/
  rw [hf, _h_inl_10]
  have hl := timeCutoffTheta_lower (1 - flatteningOffset * Real.rpow r alpha - 1 / 4)
  linarith

/- The time trace is continuous even when the spatial profile is only continuous. -/
theorem continuous_timeCutoffProfile_time {d } (H : XV d → ℝ)
    (alpha r mu R : ℝ) (q : XV d) :
    Continuous (fun t => timeCutoffProfile H alpha r mu R ⟨t, q.1, q.2⟩) := by
  simpa only [timeCutoffProfile, barrier] using!
    contDiff_timeCutoffTheta.continuous.comp
      (continuous_const.sub
        ((Real.continuous_exp.comp (continuous_const.mul continuous_id)).mul
          continuous_const))

/- The terminal height is attained with a strict margin at an earlier positive time. -/
end HypoellipticAleksandrov.KineticAleksandrov.Counterexample
