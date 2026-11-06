module

public import HypoellipticAleksandrov.KineticAleksandrov.Maximum.ComparisonGeometry
import Mathlib.Tactic.FieldSimp

/-! # Inward transport at the non-exit position faces -/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.KineticAleksandrov
open Set Filter
open scoped Topology

/- A vector with strictly inward normal component stays in the closed ball for short time. -/
theorem comparison_inward_segment {d } (Y V : PDE.Vec d) (r )
    (hY : PDE.vecNormSq Y ≤ r ^ 2)
    (hin : ¬ (PDE.vecNormSq Y = r ^ 2 ∧ 0 ≤ PDE.vecDot V Y)) :
    ∃ η : ℝ, 0 < η ∧ ∀ h : ℝ, 0 ≤ h → h < η →
      PDE.vecNormSq (Y + h • V) ≤ r ^ 2 := by
  by_cases hstrict : PDE.vecNormSq Y < r ^ 2
  · have hc : Continuous (fun h : ℝ => PDE.vecNormSq (Y + h • V)) :=
      PDE.continuous_vecNormSq.comp (continuous_const.add (continuous_id.smul continuous_const))
    have he : ∀ᶠ h in 𝓝 (0 : ℝ), PDE.vecNormSq (Y + h • V) < r ^ 2 := by
      apply hc.continuousAt.eventually_lt continuousAt_const
      simpa only [zero_smul, add_zero] using hstrict
    obtain ⟨η,hη,he⟩ := Metric.eventually_nhds_iff.mp he
    refine ⟨η,hη,fun h hh hhη => (he ?_).le⟩
    simpa only [Real.dist_eq, sub_zero, abs_of_nonneg hh] using hhη
  · have heq : PDE.vecNormSq Y = r ^ 2 := le_antisymm hY (le_of_not_gt hstrict)
    have hdot := lt_of_not_ge (fun h => hin ⟨heq,h⟩)
    have hnorm := PDE.vecNormSq_nonneg V
    have hden : 0 < PDE.vecNormSq V + 1 := by positivity
    refine ⟨-PDE.vecDot V Y / (PDE.vecNormSq V + 1), div_pos (neg_pos.mpr hdot) hden,?_⟩
    intro h hh hhη
    have hb : h * (PDE.vecNormSq V + 1) < -PDE.vecDot V Y :=
      (lt_div_iff₀ hden).mp hhη
    have hm : h * (2 * PDE.vecDot V Y + h * PDE.vecNormSq V) ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos hh (by linarith)
    have hd : PDE.vecDot Y (h • V) = h * PDE.vecDot V Y := by
      simp only [PDE.vecDot, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      ring
    rw [PDE.vecNormSq_add_expand, PDE.vecNormSq_smul, hd, heq]
    nlinarith only [hm]

/- Physical free transport remains in the closed cylinder at every non-exit point. -/
end HypoellipticAleksandrov.KineticAleksandrov
