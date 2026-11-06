module
public import TaoTrudgianYang2025.BProcessBaseline
public import TaoTrudgianYang2025.BetaReferencePhase
public import TaoTrudgianYang2025.HeathBrownModelJetCore
public import Mathlib

@[expose] public section

open Set Filter Expdb
open scoped Topology ContDiff
namespace TaoTrudgianYang2025

theorem iteratedDeriv_modelPhase_abs_le {σ : ℝ} (hσ : 0 ≤ σ)
    {u : ℝ} (hu : u ∈ Ioo (1 : ℝ) 2) (p : ℕ) :
    |iteratedDeriv p (modelPhase σ) u| ≤ modelPhaseJetCoefficient σ p := by
  have hm : ContDiffAt ℝ p (modelPhase σ) u :=
    Real.contDiffAt_rpow_const_of_ne (zero_lt_one.trans hu.1).ne'
  have hb := norm_iteratedDerivWithin_modelPhase_le hσ p ⟨hu.1.le,hu.2.le⟩
  rw [iteratedDerivWithin_eq_iteratedDeriv uniqueDiffOn_phaseInterval hm
    ⟨hu.1.le,hu.2.le⟩] at hb
  exact hb

theorem iteratedDeriv_modelPhase_lipschitz {σ : ℝ} (hσ : 0 ≤ σ)
    {u w : ℝ} (hu : u ∈ Ioo (1 : ℝ) 2) (hw : w ∈ Ioo (1 : ℝ) 2) (p : ℕ) :
    |iteratedDeriv p (modelPhase σ) u - iteratedDeriv p (modelPhase σ) w| ≤
      modelPhaseJetCoefficient σ (p+1) * |u-w| := by
  have hd : ∀ x ∈ Ioo (1 : ℝ) 2, DifferentiableAt ℝ (iteratedDeriv p (modelPhase σ)) x := by
    intro x hx
    exact (contDiffAt_iteratedDeriv_infty
      (Real.contDiffAt_rpow_const_of_ne (zero_lt_one.trans hx.1).ne') p).differentiableAt
        (by simp : (∞ : WithTop ℕ∞) ≠ 0)
  have hb : ∀ x ∈ Ioo (1 : ℝ) 2,
      ‖deriv (iteratedDeriv p (modelPhase σ)) x‖ ≤ modelPhaseJetCoefficient σ (p+1) := by
    intro x hx
    rw [← iteratedDeriv_succ]
    exact iteratedDeriv_modelPhase_abs_le hσ hx (p+1)
  exact Convex.norm_image_sub_le_of_norm_deriv_le hd hb (convex_Ioo 1 2) hw hu


