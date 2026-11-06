/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.GMC.SharpMoments.SeibergWeight
public import DOZZ.GMC.BallAnnulus.Ball
public import DOZZ.GMC.WeightedInverseMoment

/-! A fixed retained disk controls inverse Coulomb moments even when bounded roots collide. -/

public section
open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped ENNReal NNReal
namespace DOZZ.Proofs

variable {N : ℕ} (γ : ℝ) (μ : Measure ℂ) (α : Fin N → ℝ) (y : Fin N → ℂ)

include N γ μ α y in
/-- A disk around 3 avoids every root in the closed unit disk; its lower constant is uniform
in the roots and does not require a distinctness or a local charge-sum hypothesis. -/
theorem coulombMass_fixed_disk_lower  (αinf : ℝ) (hy : ∀ i, ‖y i‖ ≤ 1) :
    ENNReal.ofReal ((2 : ℝ) ^ (-∑ i, |γ * α i|) * (4 : ℝ) ^ (-|γ * αinf|)) *
      μ (Metric.ball (3 : ℂ) (1 / 8)) ≤ coulombMass γ μ α y αinf := by
  let w : ℝ := (2 : ℝ) ^ (-∑ i, |γ * α i|) * (4 : ℝ) ^ (-|γ * αinf|)
  have hw (x : ℂ) (hx : x ∈ Metric.ball (3 : ℂ) (1 / 8)) :
      ENNReal.ofReal w ≤ coulombWeight γ α y αinf x := by
    have hdist : ‖x - 3‖ < 1 / 8 := by simpa only [Metric.mem_ball, dist_eq_norm] using hx
    have hn3 : ‖(3 : ℂ)‖ = 3 := by norm_num
    have hlow : 2 < ‖x‖ := by
      have hh := norm_sub_norm_le (3 : ℂ) x
      rw [hn3, norm_sub_rev] at hh
      linarith only [hh, hdist]
    have hupp : ‖x‖ ≤ 4 := by
      have hh := norm_sub_norm_le x (3 : ℂ)
      rw [hn3] at hh
      linarith only [hh, hdist]
    have hweight := coulombWeight_ge_exterior γ α y αinf
      (Rr := 2) (by norm_num) (fun i => by linarith only [hy i]) hlow
    have hinf := ennreal_ofReal_le_rpow_ofReal_of_mem_Icc
      (L := 4) (y := ‖x‖) (by norm_num) (by linarith only [hlow]) hupp (γ * αinf)
    have hpos : 0 ≤ (2 : ℝ) ^ (-∑ i, |γ * α i|) := Real.rpow_nonneg (by norm_num) _
    calc
      ENNReal.ofReal w = ENNReal.ofReal ((2 : ℝ) ^ (-∑ i, |γ * α i|)) *
          ENNReal.ofReal ((4 : ℝ) ^ (-|γ * αinf|)) := ENNReal.ofReal_mul hpos
      _ ≤ _ := (mul_le_mul' le_rfl hinf).trans hweight
  calc
    ENNReal.ofReal w * μ (Metric.ball (3 : ℂ) (1 / 8)) =
        ∫⁻ x in Metric.ball (3 : ℂ) (1 / 8), ENNReal.ofReal w ∂μ := by simp
    _ ≤ ∫⁻ x in Metric.ball (3 : ℂ) (1 / 8), coulombWeight γ α y αinf x ∂μ :=
      setLIntegral_mono' measurableSet_ball hw
    _ ≤ coulombMass γ μ α y αinf := setLIntegral_le_lintegral _ _

include N γ μ α y in
/-- The fixed disk also survives every radial deletion of radius at most one. -/
theorem coulombMass_restrict_norm_fixed_disk_lower  (αinf r : ℝ)
    (hr : r ≤ 1) (hy : ∀ i, ‖y i‖ ≤ 1) :
    ENNReal.ofReal ((2 : ℝ) ^ (-∑ i, |γ * α i|) * (4 : ℝ) ^ (-|γ * αinf|)) *
      μ (Metric.ball (3 : ℂ) (1 / 8)) ≤
      coulombMass γ (μ.restrict {x : ℂ | r ≤ ‖x‖}) α y αinf := by
  have hsub : Metric.ball (3 : ℂ) (1 / 8) ⊆ {x : ℂ | r ≤ ‖x‖} := by
    intro x hx
    have hd : ‖x - 3‖ < 1 / 8 := by simpa only [Metric.mem_ball, dist_eq_norm] using hx
    have hn := norm_sub_norm_le (3 : ℂ) x
    rw [show ‖(3 : ℂ)‖ = 3 by norm_num, norm_sub_rev] at hn
    exact hr.trans (by linarith)
  simpa only [Measure.restrict_apply measurableSet_ball, inter_eq_left.mpr hsub] using
    coulombMass_fixed_disk_lower γ (μ.restrict {x : ℂ | r ≤ ‖x‖}) α y αinf hy

/-- All inverse orders have a constant before bounded root configurations, including collisions.
Only the ball inverse-moment bound `equatorGFF_GMC_ball_moment_bound` is used; no full Seiberg
moment theorem is assumed here. -/
theorem coulomb_inverse_moment_uniform_roots
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (X : Ω → Distr) (hX : IsEquatorGFF P X)
    (γ : ℝ) (hγ : 0 < γ) (hγ2 : γ < 2) (M : Ω → Measure ℂ) (hM : IsGMCOf P X γ M)
    {N : ℕ} (α : Fin N → ℝ) (αinf q : ℝ) (hq : 0 ≤ q) :
    ∃ C : ℝ, 0 < C ∧ ∀ y : Fin N → ℂ, (∀ i, ‖y i‖ ≤ 1) →
      (∫⁻ ω, (coulombMass γ (M ω) α y αinf) ^ (-q) ∂P) ≤ ENNReal.ofReal C := by
  let w : ℝ := (2 : ℝ) ^ (-∑ i, |γ * α i|) * (4 : ℝ) ^ (-|γ * αinf|)
  obtain ⟨C, hC, hb⟩ := gmc_inverse_moment_uniform_of_disk_lower
    P X hX γ hγ hγ2 M hM q w hq (by dsimp only [w]; positivity)
  refine ⟨C, hC, ?_⟩
  intro y hy
  exact hb _ fun ω => coulombMass_fixed_disk_lower γ (M ω) α y αinf hy

end DOZZ.Proofs
