/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import Mathlib.Analysis.Complex.Harmonic.Poisson
public import Mathlib.Topology.Order.Lattice
public import Mathlib.Tactic.Linarith
public import BergmanWeakType.Weighted.DiskSupermean

/-! # Truncation of functions satisfying the Poisson supermean inequality -/

@[expose] public section

noncomputable section

open Complex InnerProductSpace MeasureTheory Metric Real Set

namespace BergmanWeakType

def poissonExtension (R : ℝ) (v : ℂ → ℝ) (z : ℂ) : ℝ :=
  circleAverage (fun ζ ↦ poissonKernel 0 z ζ * v ζ) 0 R

theorem poissonExtension_eq_re {R : ℝ} {v : ℂ → ℝ} {z : ℂ}
    (hv : CircleIntegrable v 0 R) (hz : z ∉ sphere 0 |R|) :
    poissonExtension R v z =
      (circleAverage (fun ζ ↦ herglotzRieszKernel 0 z ζ • (v ζ : ℂ)) 0 R).re := by
  simpa only [poissonExtension, ← poissonKernel_eq_re_herglotzRieszKernel,
    Pi.smul_def, smul_eq_mul, Pi.mul_def] using
      (re_circleAverage_herglotzRieszKernel_smul hv hz).symm

theorem continuousOn_poissonExtension {R : ℝ} {v : ℂ → ℝ}
    (hv : CircleIntegrable v 0 R) :
    ContinuousOn (poissonExtension R v) (sphere (0 : ℂ) |R|)ᶜ := by
  have hvc : CircleIntegrable (fun ζ ↦ (v ζ : ℂ)) 0 R := by
    simp only [CircleIntegrable, intervalIntegrable_iff] at hv ⊢
    exact Complex.ofRealCLM.integrable_comp hv
  apply (continuous_re.comp_continuousOn
    (analyticOnNhd_circleAverage_herglotzRieszKernel_smul hvc).continuousOn).congr
  intro z hz
  exact poissonExtension_eq_re hv hz

theorem circleAverage_poissonExtension {R r : ℝ} {v : ℂ → ℝ}
    (hv : CircleIntegrable v 0 R) (hrR : |r| < |R|) :
    circleAverage (poissonExtension R v) 0 r = circleAverage v 0 R := by
  let F : ℂ → ℂ := fun z ↦
    circleAverage (fun ζ ↦ herglotzRieszKernel 0 z ζ • (v ζ : ℂ)) 0 R
  have hvc : CircleIntegrable (fun ζ ↦ (v ζ : ℂ)) 0 R := by
    simp only [CircleIntegrable, intervalIntegrable_iff] at hv ⊢
    exact Complex.ofRealCLM.integrable_comp hv
  have hF := analyticOnNhd_circleAverage_herglotzRieszKernel_smul hvc
  have hsub : closedBall (0 : ℂ) |r| ⊆ (sphere 0 |R|)ᶜ := by
    intro z hz
    have hz' : ‖z‖ ≤ |r| := by simpa using hz
    simpa using (hz'.trans_lt hrR).ne
  have hdiff : DifferentiableOn ℂ F (closedBall 0 |r|) :=
    fun z hz ↦ (hF z (hsub hz)).differentiableWithinAt
  have hcircle : CircleIntegrable F 0 r :=
    (hdiff.continuousOn.mono sphere_subset_closedBall).circleIntegrable'
  calc
    _ = circleAverage (Complex.reCLM ∘ F) 0 r :=
      circleAverage_congr_sphere fun z hz ↦ poissonExtension_eq_re hv
        (hsub (sphere_subset_closedBall hz))
    _ = (circleAverage F 0 r).re := Complex.reCLM.circleAverage_comp_comm hcircle
    _ = (F 0).re := by
      rw [(hdiff.mono closure_ball_subset_closedBall).diffContOnCl.circleAverage]
    _ = poissonExtension R v 0 := (poissonExtension_eq_re hv (hsub (by simp))).symm
    _ = circleAverage v 0 R := by
      apply circleAverage_congr_sphere
      intro ζ hζ
      have hζ' : ‖ζ‖ = |R| := by simpa using hζ
      have hR : 0 < |R| := (abs_nonneg r).trans_lt hrR
      have hRn : R ≠ 0 := abs_pos.mp hR
      simp [poissonKernel_def, hζ', hRn]

end BergmanWeakType
