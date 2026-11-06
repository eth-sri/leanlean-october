module

public import HypoellipticAleksandrov.KineticAleksandrov.Maximum.ComparisonGeometry
import Mathlib.Tactic.FieldSimp

/-! # Inward transport at the non-exit position faces -/

 public section

namespace HypoellipticAleksandrov.KineticAleksandrov
open Set
open scoped Topology

variable {d : ℕ}

/-- A vector with strictly inward normal component stays in the closed ball for short time. -/
theorem comparison_inward_segment  (Y V : PDE.Vec d) (r : ℝ)
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
  · have heq  := le_antisymm hY (le_of_not_gt hstrict)
    have hdot  := lt_of_not_ge (fun h => hin ⟨heq,h⟩)
    have hnorm := PDE.vecNormSq_nonneg V
    have hden : 0 < PDE.vecNormSq V + 1 := by positivity
    refine ⟨-PDE.vecDot V Y / (PDE.vecNormSq V + 1), div_pos (neg_pos.mpr hdot) hden,?_⟩
    intro h hh hhη
    have hb  :=
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

/-- Physical free transport remains in the closed cylinder at every non-exit point. -/
theorem comparison_freeTransport_stays
    (Z₀ : KineticPoint d) (R : ℝ) (hR : 0 < R) {P : KineticPoint d}
    (hP : P ∈ closure (forwardCylinder Z₀ R hR))
    (hnot : P ∉ exitBoundary Z₀ R hR) :
    ∃ η : ℝ, 0 < η ∧ ∀ h : ℝ, 0 ≤ h → h < η →
      (⟨P.time + h,P.position + h • P.velocity,P.velocity⟩ : KineticPoint d) ∈
        closure (forwardCylinder Z₀ R hR) := by

  rcases (closure_forwardCylinder_bounds Z₀ R hR hP) with ⟨⟨ht0,ht1⟩,hx,hv⟩
  change Z₀.time ≤ P.time at ht0
  change P.time ≤ Z₀.time + R ^ 2 at ht1



  obtain ⟨r,hr,hstay⟩ := comparison_inward_segment _ _ _ (by
      change PDE.vecNormSq (relativePosition Z₀ P - 0) ≤ (R ^ 3) ^ 2 at hx
      simpa only [sub_zero] using hx) (by
      intro hh
      apply hnot ((mem_exitBoundary_iff Z₀ P R hR).2 ⟨hP,Or.inr (Or.inr ?_)⟩)
      refine ⟨?_,hh.2⟩
      simpa only [PDE.euclideanSphere, PDE.euclideanSqDist, sub_zero, mem_ofPred_eq] using hh.1)
  refine ⟨min r (Z₀.time + R ^ 2 - P.time), lt_min hr (sub_pos.mpr (by
      apply lt_of_le_of_ne ht1
      intro heq
      exact hnot ((mem_exitBoundary_iff Z₀ P R hR).2 ⟨hP,Or.inl heq⟩))),?_⟩
  intro h hh hη
  rw [comparison_closure_forwardCylinder_eq]
  change (Z₀.time ≤ P.time + h ∧ P.time + h ≤ Z₀.time + R ^ 2) ∧
    relativePosition Z₀ ⟨P.time + h,P.position + h • P.velocity,P.velocity⟩ ∈
      PDE.euclideanClosedBall 0 (R ^ 3) ∧
    relativeVelocity Z₀ ⟨P.time + h,P.position + h • P.velocity,P.velocity⟩ ∈
      PDE.euclideanClosedBall 0 R
  refine ⟨⟨by linarith,by have := lt_of_lt_of_le hη (min_le_right _ _); linarith⟩,?_,hv⟩
  have heq : relativePosition Z₀ ⟨P.time + h,P.position + h • P.velocity,P.velocity⟩ =
      relativePosition Z₀ P + h • relativeVelocity Z₀ P := by
    ext i
    simp only [relativePosition, relativeVelocity, Pi.add_apply, Pi.sub_apply,
      Pi.smul_apply, smul_eq_mul]
    ring
  rw [heq]
  simpa only [PDE.euclideanClosedBall, PDE.euclideanSqDist, sub_zero, mem_ofPred_eq] using
    hstay h hh (lt_of_lt_of_le hη (min_le_left _ _))

end HypoellipticAleksandrov.KineticAleksandrov
