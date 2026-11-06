/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.GMC.SharpMoments.SeibergWeight
public import DOZZ.GMC.BallAnnulus.Ball

/-! A fixed retained disk controls inverse Coulomb moments even when bounded roots collide. -/

@[expose] public section
open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped ENNReal NNReal
namespace DOZZ.Proofs

/-- A disk around 3 avoids every root in the closed unit disk; its lower constant is uniform
in the roots and does not require a distinctness or a local charge-sum hypothesis. -/
theorem coulombMass_fixed_disk_lower {N : ℕ} (γ : ℝ) (μ : Measure ℂ)
    (α : Fin N → ℝ) (y : Fin N → ℂ) (αinf : ℝ) (hy : ∀ i, ‖y i‖ ≤ 1) :
    ENNReal.ofReal ((2 : ℝ) ^ (-∑ i, |γ * α i|) * (4 : ℝ) ^ (-|γ * αinf|)) *
      μ (Metric.ball (3 : ℂ) (1 / 8)) ≤ coulombMass γ μ α y αinf := by
  let w : ℝ := 2 ^ (-∑ i, |γ * α i|) * (4 : ℝ) ^ (-|γ * αinf|)
  have hw (x : ℂ) (hx : x ∈ Metric.ball (3 : ℂ) (1 / 8)) :
      ENNReal.ofReal w ≤ coulombWeight γ α y αinf x := by
    have hdist : ‖x - 3‖ < 1 / 8 := by simpa only [Metric.mem_ball, dist_eq_norm] using hx
    have hn3 : ‖(3 : ℂ)‖ = 3 := by norm_num
    have hlow : 2 < ‖x‖ := by
      have hh := norm_sub_norm_le (3 : ℂ) x
      rw [hn3, norm_sub_rev] at hh
      linarith
    have hupp : ‖x‖ ≤ 4 := by
      have hh := norm_sub_norm_le x (3 : ℂ)
      linarith
    have hweight := coulombWeight_ge_exterior γ α y αinf
      (by norm_num) (fun i => by simp_all) hlow
    have hinf := ennreal_ofReal_le_rpow_ofReal_of_mem_Icc
      (by norm_num) (by linarith) hupp (γ * αinf)
    have hpos : 0 ≤ (2 : ℝ) ^ (-∑ i, |γ * α i|) := by positivity
    calc
      ENNReal.ofReal w = ENNReal.ofReal _ *
          ENNReal.ofReal _ := ENNReal.ofReal_mul hpos
      _ ≤ _ := (mul_le_mul' le_rfl hinf).trans hweight
  calc
    ENNReal.ofReal w * μ _ =
        ∫⁻ x in Metric.ball 3 _, ENNReal.ofReal w ∂μ := by simp
    _ ≤ ∫⁻ x in Metric.ball 3 _, coulombWeight γ α y αinf x ∂μ :=
      setLIntegral_mono' measurableSet_ball hw
    _ ≤ coulombMass γ μ α y αinf := setLIntegral_le_lintegral ..

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
  let w : ℝ := 2 ^ (-∑ i, |γ * α i|) * 4 ^ (-|γ * αinf|)
  have hw : 0 < w := by positivity
  have hp : -q < 4 / γ ^ 2 := lt_of_le_of_lt (neg_nonpos.mpr hq) (by positivity)
  obtain ⟨Cb, hCb, hball⟩ := equatorGFF_GMC_ball_moment_bound P X hX γ hγ hγ2 M hM
    (-q) hp {3} isCompact_singleton
  let ξ := γ * Q γ * (-q) - γ ^ 2 * (-q) ^ 2 / 2
  let C := w ^ (-q) * (Cb * (1 / 8) ^ ξ)
  have hC : 0 < C := by positivity
  refine ⟨C, hC, ?_⟩
  intro y hy
  have hpoint (ω : Ω) : (coulombMass γ (M ω) α y αinf) ^ (-q) ≤
      ENNReal.ofReal (w ^ (-q)) * (M ω (Metric.ball 3 (1 / 8))) ^ (-q) := by
    have hanti : (coulombMass γ (M ω) α y αinf) ^ (-q) ≤
        (ENNReal.ofReal w * M ω (Metric.ball 3 (1 / 8))) ^ (-q) := by
      rw [ENNReal.rpow_neg, ENNReal.rpow_neg]
      exact ENNReal.inv_le_inv.mpr (ENNReal.rpow_le_rpow (coulombMass_fixed_disk_lower γ (M ω) α y αinf hy) hq)
    have hfinite : M ω (Metric.ball 3 (1 / 8)) ≠ ⊤ := by
      let _ := hM.1 ω
      exact measure_ne_top _ _
    rwa [ENNReal.mul_rpow_of_ne_top ENNReal.ofReal_ne_top hfinite,
      ENNReal.ofReal_rpow_of_pos hw] at hanti
  have hbound := (hball 3 (Set.mem_singleton _) (1 / 8) (by norm_num) (by norm_num)).2
  calc
    (∫⁻ ω, (coulombMass γ (M ω) α y αinf) ^ (-q) ∂P) ≤
        ∫⁻ ω, ENNReal.ofReal _ * M ω _ ^ (-q) ∂P :=
      lintegral_mono hpoint
    _ = ENNReal.ofReal _ * gmcMassMoment P M _ (-q) :=
      lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
    _ ≤ ENNReal.ofReal _ * ENNReal.ofReal _ :=
      mul_le_mul' le_rfl hbound
    _ = ENNReal.ofReal C := (ENNReal.ofReal_mul (Real.rpow_pos_of_pos hw _).le).symm

end DOZZ.Proofs
