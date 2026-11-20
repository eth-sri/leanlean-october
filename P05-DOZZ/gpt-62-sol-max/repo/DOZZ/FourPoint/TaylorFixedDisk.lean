/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.GMC.SharpMoments.SeibergWeight
public import DOZZ.GMC.BallAnnulus.Ball
public import DOZZ.GMC.SharpMoments.SeibergDecomp

/-! A fixed retained disk controls inverse Coulomb moments even when bounded roots collide. -/

@[expose] public section
open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped ENNReal NNReal
namespace DOZZ.Proofs

/-- The fixed disk avoids every root in the closed unit disk. -/
noncomputable def coulombGuardWeight {N : ℕ} (γ : ℝ) (α : Fin N → ℝ) (αinf : ℝ) : ℝ :=
  (2 : ℝ) ^ (-∑ i, |γ * α i|) * (4 : ℝ) ^ (-|γ * αinf|)

theorem coulombGuardWeight_pos {N : ℕ} (γ : ℝ) (α : Fin N → ℝ) (αinf : ℝ) :
    0 < coulombGuardWeight γ α αinf := by
  unfold coulombGuardWeight
  positivity

theorem fixed_disk_norm_gt_two {x : ℂ} (hx : x ∈ Metric.closedBall (3 : ℂ) (1 / 8)) :
    2 < ‖x‖ := by
  rw [Metric.mem_closedBall, dist_eq_norm] at hx
  have h := norm_sub_norm_le (3 : ℂ) x
  rw [show ‖(3 : ℂ)‖ = 3 by norm_num, norm_sub_rev] at h
  linarith

theorem fixed_disk_subset_exterior {r : ℝ} (hr : r ≤ 1) :
    Metric.ball (3 : ℂ) (1 / 8) ⊆ {x | r ≤ ‖x‖} := fun _ hx =>
  hr.trans (by linarith [fixed_disk_norm_gt_two (Metric.ball_subset_closedBall hx)])

theorem fixed_guard_restrict_singleton (μ : Measure ℂ) {x : ℂ} (hx : ‖x‖ ≤ 1) :
    (μ.restrict (Metric.closedBall (3 : ℂ) (1 / 8))) {x} = 0 := by
  rw [Measure.restrict_apply (measurableSet_singleton _), singleton_inter_of_notMem, measure_empty]
  intro h
  linarith [fixed_disk_norm_gt_two h]

section
variable {N : ℕ} (γ : ℝ) (μ : Measure ℂ) (α : Fin N → ℝ) (y : Fin N → ℂ) (αinf : ℝ)
  (hy : ∀ i, ‖y i‖ ≤ 1)
include N hy

theorem coulombMass_fixed_disk_lower :
    ENNReal.ofReal (coulombGuardWeight γ α αinf) * μ (Metric.ball (3 : ℂ) (1 / 8)) ≤
      coulombMass γ μ α y αinf := by
  have h := coulombMass_ge_exterior_ball μ γ α y αinf
    (Rr := 2) (by norm_num) (fun j => by linarith [hy j])
  rw [coulombGuardWeight, ENNReal.ofReal_mul (by positivity)]
  convert h using 3 <;> norm_num

theorem coulombMass_fixed_disk_lower_restrict
    {D : Set ℂ} (hD : Metric.ball (3 : ℂ) (1 / 8) ⊆ D) :
    ENNReal.ofReal (coulombGuardWeight γ α αinf) * μ (Metric.ball (3 : ℂ) (1 / 8)) ≤
      coulombMass γ (μ.restrict D) α y αinf := by
  simpa only [Measure.restrict_apply measurableSet_ball, inter_eq_left.mpr hD] using
    coulombMass_fixed_disk_lower γ (μ.restrict D) α y αinf hy

end

theorem three_roots_in_unit_disk {z : ℂ} (hz : ‖z‖ ≤ 1) :
    ∀ i : Fin 3, ‖(![z, 0, 1] : Fin 3 → ℂ) i‖ ≤ 1 := by
  intro i
  fin_cases i <;> simp_all

/-- Negative powers convert a fixed positive lower mass bound to an upper bound. -/
theorem inverse_power_le_of_guard {I B : ℝ≥0∞} {w q : ℝ} (hw : 0 < w) (hq : 0 ≤ q)
    (hB : B ≠ ⊤) (hI : ENNReal.ofReal w * B ≤ I) :
    I ^ (-q) ≤ ENNReal.ofReal (w ^ (-q)) * B ^ (-q) := by
  have h := ENNReal.inv_le_inv.mpr (ENNReal.rpow_le_rpow hI hq)
  rwa [← ENNReal.rpow_neg, ← ENNReal.rpow_neg,
    ENNReal.mul_rpow_of_ne_top ENNReal.ofReal_ne_top hB, ENNReal.ofReal_rpow_of_pos hw] at h

section
variable {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (X : Ω → Distr) (hX : IsEquatorGFF P X)
  (γ : ℝ) (hγ : 0 < γ) (hγ2 : γ < 2) (M : Ω → Measure ℂ) (hM : IsGMCOf P X γ M)
include Ω X hX γ hγ hγ2 hM

/-- A uniform inverse bound for any mass dominating one fixed positive multiple of the disk.
This adapter does not assume the compared random mass itself is a GMC. -/
theorem inverse_fixed_disk_uniform
    (w q : ℝ) (hw : 0 < w) (hq : 0 ≤ q) :
    ∃ C : ℝ, 0 < C ∧ ∀ I : Ω → ℝ≥0∞,
      (∀ ω, ENNReal.ofReal w * M ω (Metric.ball (3 : ℂ) (1 / 8)) ≤ I ω) →
        (∫⁻ ω, I ω ^ (-q) ∂P) ≤ ENNReal.ofReal C := by
  have hp : -q < 4 / γ ^ 2 := lt_of_le_of_lt (neg_nonpos.mpr hq) (by positivity)
  obtain ⟨Cb, hCb, hball⟩ := equatorGFF_GMC_ball_moment_bound P X hX γ hγ hγ2 M hM
    (-q) hp {(3 : ℂ)} isCompact_singleton
  let ξ : ℝ := γ * Q γ * (-q) - γ ^ 2 * (-q) ^ 2 / 2
  let C : ℝ := w ^ (-q) * (Cb * (1 / 8 : ℝ) ^ ξ)
  refine ⟨C, by dsimp only [C]; positivity, ?_⟩
  intro I hI
  have hpoint (ω : Ω) : I ω ^ (-q) ≤
      ENNReal.ofReal (w ^ (-q)) * M ω (Metric.ball (3 : ℂ) (1 / 8)) ^ (-q) := by
    let _ := hM.1 ω
    exact inverse_power_le_of_guard hw hq (measure_ne_top _ _) (hI ω)
  have hbound := (hball 3 (Set.mem_singleton _) (1 / 8) (by norm_num) (by norm_num)).2
  calc
    _ ≤ ∫⁻ ω, ENNReal.ofReal (w ^ (-q)) * M ω (Metric.ball (3 : ℂ) (1 / 8)) ^ (-q) ∂P := lintegral_mono hpoint
    _ = ENNReal.ofReal (w ^ (-q)) * gmcMassMoment P M (Metric.ball (3 : ℂ) (1 / 8)) (-q) :=
      lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
    _ ≤ ENNReal.ofReal (w ^ (-q)) * ENNReal.ofReal (Cb * (1 / 8 : ℝ) ^ ξ) := mul_le_mul' le_rfl hbound
    _ = _ := (ENNReal.ofReal_mul (Real.rpow_pos_of_pos hw _).le).symm

/-- All inverse orders have a constant before bounded root configurations, including collisions.
Only the ball inverse-moment bound `equatorGFF_GMC_ball_moment_bound` is used; no full Seiberg
moment theorem is assumed here. -/
theorem coulomb_inverse_moment_uniform_roots
    {N : ℕ} (α : Fin N → ℝ) (αinf q : ℝ) (hq : 0 ≤ q) :
    ∃ C : ℝ, 0 < C ∧ ∀ y : Fin N → ℂ, (∀ i, ‖y i‖ ≤ 1) →
      (∫⁻ ω, (coulombMass γ (M ω) α y αinf) ^ (-q) ∂P) ≤ ENNReal.ofReal C := by
  obtain ⟨C, hC, h⟩ := inverse_fixed_disk_uniform P X hX γ hγ hγ2 M hM _ q
    (coulombGuardWeight_pos γ α αinf) hq
  exact ⟨C, hC, fun y hy => h _ fun ω => coulombMass_fixed_disk_lower γ (M ω) α y αinf hy⟩

end

end DOZZ.Proofs
