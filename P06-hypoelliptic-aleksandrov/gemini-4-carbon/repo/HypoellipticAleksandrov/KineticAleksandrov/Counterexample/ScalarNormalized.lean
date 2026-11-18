module

public import HypoellipticAleksandrov.KineticAleksandrov.Counterexample.ScalarNegativeJets
public import HypoellipticAleksandrov.KineticAleksandrov.Counterexample.ScalarMatching
import Mathlib.Tactic

/-!
# Normalized scalar tails

The common leading coefficient is an actual limit of the constructed function on both rays.
-/

@[expose] public noncomputable section

namespace HypoellipticAleksandrov.KineticAleksandrov.Counterexample

open Filter Asymptotics
open scoped Topology

/-- A three-degree lower power remainder gives the exact normalized limit. -/
theorem scalar_tail_ratio (f : ℝ → ℝ) (alpha c : ℝ)
    (hr : IsBigO atTop (fun s => f s - c * Real.rpow s alpha)
      (fun s => Real.rpow s (alpha - 3))) :
    Tendsto (fun s => f s / Real.rpow s alpha) atTop (𝓝 c) := by
  have hp : Tendsto (fun s => Real.rpow s (-3)) atTop (𝓝 0) := by
    simpa using
      tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < 3)
  have hzero := (Kummer.rpow_mul_isBigO_of_add_eq (fun s => f s - c * Real.rpow s alpha) (-alpha) (alpha - 3) (-3) (by simpa using hr) (by ring)).trans_tendsto hp
  have h := tendsto_const_nhds.add hzero (a := c)
  simp at h
  apply h.congr'
  filter_upwards [eventually_gt_atTop 0] with s hs
  simp
  rw [Real.rpow_neg hs.le]
  field_simp
  ring

/-- The actual joined profile has its specified positive-ray normalized limit. -/
theorem F_ratio_atTop (gamma : ScalarGamma) (Lam : ℝ) (hLam : 0 < Lam) :
    Tendsto (fun s => F gamma Lam s / Real.rpow |s| (3 * gamma.1))
      atTop (𝓝 (Real.rpow (9 * Lam) (-gamma.1))) := by
  apply (scalar_tail_ratio (Fplus gamma Lam) (3 * gamma.1) (Real.rpow (9 * Lam) (-gamma.1)) (Fplus_asymptotic gamma Lam hLam)).congr'
  filter_upwards [eventually_gt_atTop 0] with s hs
  simp [F, hs, abs_of_pos hs]

/-- The matched joined profile has the same negative-ray normalized limit. -/
theorem F_ratio_atBot (gamma : ScalarGamma) (Lam : ℝ) (hLam : 0 < Lam)
    (hmatch : Pgamma gamma.1 - Qgamma gamma.1 * Real.rpow Lam (-(1 / 3)) =
      Real.rpow Lam (-gamma.1)) :
    Tendsto (fun s => F gamma Lam s / Real.rpow |s| (3 * gamma.1))
      atBot (𝓝 (Real.rpow (9 * Lam) (-gamma.1))) := by
  have hb := Fminus_negative_ray_asymptotic_of_M_expansion
    Kummer.M_negative_expansion gamma Lam hLam
  rw [scalar_matching_trace_coefficient gamma Lam hLam hmatch] at hb
  have ht := (scalar_tail_ratio (fun s => Fminus gamma Lam (-s)) (3 * gamma.1) (Real.rpow (9 * Lam) (-gamma.1)) hb).comp tendsto_neg_atBot_atTop
  apply ht.congr'
  filter_upwards [eventually_lt_atBot 0] with s hs
  simp [Function.comp_def, F, hs, not_lt.mpr hs.le, abs_of_neg hs]

end HypoellipticAleksandrov.KineticAleksandrov.Counterexample
