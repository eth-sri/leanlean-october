/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.Correlations.Analytic.EquatorCorrectionBounds
public import DOZZ.GMC.SharpMoments.SeibergWeight

/-! Exact averaged insertion kernels outside the retained-region holes. -/

@[expose] public section
open MeasureTheory ProbabilityTheory
open scoped ENNReal
namespace DOZZ.Proofs

/-- Away from all roots, the all-finite Coulomb weight is an exponential of logarithms. -/
theorem coulomb_weight_exp_log {N : ℕ} (γ : ℝ) (α : Fin N → ℝ)
    (z : Fin N → ℂ) (x : ℂ) (hx : ∀ i, x ≠ z i) :
    coulombWeight γ α z 0 x = ENNReal.ofReal
      (Real.exp (∑ i, γ * α i * Real.log (normPlus x / ‖x - z i‖))) := by
  have hn : 0 < normPlus x := lt_of_lt_of_le one_pos (le_max_left ..)
  have hd (i : Fin N) : 0 < ‖x - z i‖ := norm_pos_iff.mpr (sub_ne_zero.mpr (hx i))
  unfold coulombWeight
  simp
  simp_rw [ENNReal.ofReal_rpow_of_pos (div_pos hn (hd _)),
    Real.rpow_def_of_pos (div_pos hn (hd _))]
  rw [← ENNReal.ofReal_prod_of_nonneg (fun _ _ => Real.exp_nonneg _), ← Real.exp_sum]
  grind

/-- Outside an insertion circle, averaging changes only the regular equator pin. -/
theorem retained_vertex_potential (x z : ℂ) (r : ℝ)
    (hx : Real.exp (-r) ≤ ‖x - z‖) :
    (∫ v, gffKernel x v ∂circleMeasure z r) =
      Real.log (normPlus x / ‖x - z‖) + equatorCircleMean z r := by
  have hn : 0 < normPlus x := lt_of_lt_of_le one_pos (le_max_left ..)
  rw [CirclePotential.integral_gffKernel_circleMeasure]
  unfold CirclePotential.innerPot
  rw [max_eq_left hx, Real.log_div hn.ne' (lt_of_lt_of_le (Real.exp_pos _) hx).ne']
  have hmean : CirclePotential.regAvg z r = equatorCircleMean z r := by
    unfold CirclePotential.regAvg equatorCircleMean
    exact (CirclePotential.integral_circleMeasure_eq_circleAverage
      CirclePotential.continuous_log_normPlus.measurable z r).symm
  linarith


end DOZZ.Proofs
