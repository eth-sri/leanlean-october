/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.GFF.EquatorDistribution
public import DOZZ.GFF.TorusFourierEvalIdentification

/-!
# DOZZ.GFF.EquatorDistributionBridge

The locally defined Fourier charts assemble to a measurable random distribution whose test
evaluations agree almost everywhere with the accepted G4 field.
-/

@[expose] public section

open MeasureTheory Filter Set Metric TopologicalSpace
open scoped Distributions ENNReal InnerProductSpace Topology lp

namespace DOZZ






/-- Every global test evaluation of the measurable distribution is almost everywhere the G4
isonormal evaluation on the same test. -/
theorem ae_equatorDistributionEval_eq_equatorFieldL2 (f : TestFn) :
    (fun ω => equatorDistributionEval ω f) =ᵐ[
      GaussianFields.scaleSpaceWhiteNoiseMeasure 2]
      (fun ω => equatorFieldL2 f ω) := by
  classical
  have sum_equatorPartitionCLM_range_eq_self_of_cutoff_eq_one (N : ℕ) (f : TestFn) (hcut : ∀ z ∈ tsupport f, equatorGlobalCutoff N z = 1) : (∑ n ∈ Finset.range (N + 1), equatorPartitionCLM n f) = f := by
    ext z
    calc
      (∑ n ∈ Finset.range (N + 1), equatorPartitionCLM n f) z =
          ∑ n ∈ Finset.range (N + 1), f z * equatorPartitionFunction n z := by
        simp only [FunLike.coe_sum, equatorPartitionCLM_apply, Finset.sum_apply]
      _ = f z * equatorGlobalCutoff N z := by
        rw [← Finset.mul_sum, sum_equatorPartitionFunction_range]
      _ = f z := by
        by_cases hz : z ∈ tsupport f
        · simp [hcut z hz]
        · have hfz : f z = 0 := by
            by_contra hne
            exact (fun hs => hz (subset_tsupport f hs)) (Function.mem_support.mpr hne)
          simp [hfz]
  have exists_nat_equatorPartition_reconstruction_radius : ∃ N : ℕ, ∀ z ∈ tsupport f, z ∈ closedBall 0 ((N : ℝ) + 2) := by
    obtain ⟨R, hR, hball⟩ :=
      f.hasCompactSupport.isBounded.subset_ball_lt (0 : ℝ) (0 : ℂ)
    obtain ⟨N, hN⟩ : ∃ N : ℕ, R + 1 < N := exists_nat_gt (R + 1)
    refine ⟨N, fun z hz => ?_⟩
    have : ‖z‖ < R := by
      simpa [mem_ball, dist_eq_norm] using hball hz
    simpa [mem_closedBall, dist_eq_norm] using (by linarith)
  have equatorPartitionCLM_support_subset_localBall n f : Function.support (equatorPartitionCLM n f) ⊆ ball 0 (gffLocalModeRadius (n + 5) - 1) := by
    have equatorPartitionCLM_support_subset : Function.support (equatorPartitionCLM n f) ⊆ closedBall 0 ((n : ℝ) + 3) := by
      apply Function.support_subset_iff'.2
      intro z hz
      change f z * equatorPartitionFunction n z = 0
      rw [equatorPartitionFunction_eq_zero_of_not_mem n hz]
      simp
    intro z hz
    simpa [mem_ball, dist_eq_norm] using (lt_of_le_of_lt (by simpa [mem_closedBall, dist_eq_norm] using (equatorPartitionCLM_support_subset hz)) (by rw [(show gffLocalModeRadius (n + 5) - 1 = (n : ℝ) + 5 by simp [gffLocalModeRadius])]; linarith))
  obtain ⟨Ntail, htail⟩ := exists_nat_equatorPartition_tail_zero f
  obtain ⟨Ncut, hcutSupport⟩ := exists_nat_equatorPartition_reconstruction_radius
  let N := max Ntail Ncut
  have htailN : ∀ n ≥ N + 1, equatorPartitionCLM n f = 0 := by
    intro n hn
    apply htail n
    omega
  have hcutN : ∀ z ∈ tsupport f, equatorGlobalCutoff N z = 1 := by
    intro z hz
    apply equatorGlobalCutoff_eq_one N
    exact closedBall_subset_closedBall (by
      have : (Ncut : ℝ) ≤ (N : ℝ) := by
        dsimp [N]
        exact_mod_cast Nat.le_max_right Ntail Ncut
      linarith) (hcutSupport z hz)
  have hlocal (n : ℕ) := ae_equatorLocalFourierEval_eq_equatorFieldL2 (n + 5)
      (equatorPartitionCLM n f) (equatorPartitionCLM_support_subset_localBall n f)
  let s := Finset.range (N + 1)
  have hsumLp' : equatorFieldL2 f =
      s.sum fun n => equatorFieldL2 (equatorPartitionCLM n f) := by
    calc
      equatorFieldL2 f = equatorFieldL2 (s.sum fun n => equatorPartitionCLM n f) :=
        (congrArg equatorFieldL2 (sum_equatorPartitionCLM_range_eq_self_of_cutoff_eq_one N f hcutN)).symm
      _ = s.sum fun n => equatorFieldL2 (equatorPartitionCLM n f) := (by simp only [map_sum])
  have hsumAE :
      (fun ω => equatorFieldL2 f ω) =ᵐ[
        GaussianFields.scaleSpaceWhiteNoiseMeasure 2]
        (fun ω => s.sum fun n => equatorFieldL2 (equatorPartitionCLM n f) ω) := by
    rw [hsumLp']
    exact Lp.coeFn_fun_finsetSum s (fun n => equatorFieldL2 (equatorPartitionCLM n f))
  filter_upwards [ae_equatorHaarCommonGood, (ae_all_iff.mpr hlocal), hsumAE] with ω hgood hlocalω hsumω
  rw [equatorDistributionEval, ite_eq_left hgood, equatorDistributionSeriesEval_eq_partialSum_of_tail_zero ω f N htailN]
  unfold equatorDistributionPartialSum
  calc
    _ = s.sum fun n => equatorFieldL2 (equatorPartitionCLM n f) ω := by
      apply Finset.sum_congr rfl
      intro n hn
      exact hlocalω n
    _ = equatorFieldL2 f ω := hsumω.symm

theorem ae_equatorGFFDistribution_apply_eq_equatorFieldL2 f :
    (fun ω => equatorGFFDistribution ω f) =ᵐ[
      GaussianFields.scaleSpaceWhiteNoiseMeasure 2]
      (fun ω => equatorFieldL2 f ω) :=
  ae_equatorDistributionEval_eq_equatorFieldL2 f

end DOZZ

end
