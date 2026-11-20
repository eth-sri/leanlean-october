/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.Statements.Defs.IsGMCOf
public import DOZZ.GMC.Moments.RegularizedScale
public import DOZZ.GMC.Moments.ChaosLawFDDLimit
public import DOZZ.GMC.Moments.ScaleLimit

/-! Exact affine scaling of arbitrary `IsGMCOf` limits on a compact logarithmic chart. -/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped Distributions ENNReal NNReal

namespace DOZZ.Proofs

/-- The exact-scale identity for arbitrary `IsGMCOf` versions, expressed jointly on finite
families of nonnegative compactly supported tests. The independent Gaussian comes from the
constant shift in the logarithmic covariance, and the affine Jacobian is `c^2`. -/
theorem gmc_affine_test_vector_law
    {Ω : Type*} [MeasurableSpace Ω] {m : ℕ}
    (P : Measure Ω) (X : Ω → Distr) (hX : IsEquatorGFF P X) (γ : ℝ)
    (M : Ω → Measure ℂ) (hM : IsGMCOf P X γ M)
    {a : ℂ} {c R : ℝ} (hc : 0 < c) (hc1 : c ≤ 1) (hR : 0 < R)
    (hRsmall : R < 1) (hTsmall : ‖a‖ + c * R < 1)
    (f : Fin m → BoundedContinuousFunction ℂ ℝ)
    (hf_nonneg : ∀ j x, 0 ≤ f j x)
    (hf_support : ∀ j, tsupport (f j : ℂ → ℝ) ⊆ Metric.closedBall a (c * R)) :
    Measure.map (fun ω j => ∫ x, f j x ∂M ω) P =
      Measure.map (fun p : Ω × ℝ => fun j =>
        c ^ 2 * Real.exp (γ * p.2 - γ ^ 2 / 2 * (-Real.log c)) *
          ∫ x, f j (a + c • x) ∂M p.1)
        (P.prod (gaussianReal 0 ⟨-Real.log c,
          neg_nonneg.mpr (Real.log_nonpos (le_of_lt hc) hc1)⟩)) := by
  classical
  obtain ⟨Xc, hXc, hMlim⟩ := hM.2
  let σ  := -Real.log c
  let G  := gaussianReal 0 ⟨σ,
    neg_nonneg.mpr (Real.log_nonpos (le_of_lt hc) hc1)⟩
  have hG : IsProbabilityMeasure G := by
    simpa [G, σ] using (ProbabilityTheory.instIsProbabilityMeasureGaussianReal 0
      ⟨-Real.log c, neg_nonneg.mpr (Real.log_nonpos (le_of_lt hc) hc1)⟩)
  let  := hX.1
  let  := hG
  let gap  := min (1 - R) (1 - (‖a‖ + c * R))
  have hgap : 0 < gap := by
    positivity
  have hsmallEvent : ∀ᶠ n : ℕ in atTop, Real.exp (-(n : ℝ)) < gap := by
    have hlim  :=
      Real.tendsto_exp_neg_atTop_nhds_zero.comp tendsto_natCast_atTop_atTop
    exact hlim.eventually (isOpen_Iio.mem_nhds hgap)
  obtain ⟨N, hN⟩ := eventually_atTop.1 hsmallEvent
  have hNgap  := le_of_lt (hN N le_rfl)
  have hsourceCut (n : ℕ) (x : {z : ℂ // z ∈ Metric.closedBall (0 : ℂ) R}) :
      ‖x.1‖ + Real.exp (-((N + n : ℕ) : ℝ)) ≤ 1 := by
    have hxR : ‖x.1‖ ≤ R := by
      have hxmem  := x.2
      change dist x.1 0 ≤ R at hxmem
      simpa only [dist_zero_right] using hxmem
    have hn : (N : ℝ) ≤ ((N + n : ℕ) : ℝ) := by simp
    have hexp  :=
      Real.exp_le_exp.mpr (neg_le_neg hn)
    have hgapS : gap ≤ 1 - R := by dsimp [gap]; exact min_le_left _ _
    linarith [hexp.trans hNgap]
  have htargetCut (n : ℕ) (x : {z : ℂ // z ∈ Metric.closedBall (0 : ℂ) R}) :
      ‖a + c • x.1‖ + Real.exp (-(((N + n : ℕ) : ℝ) - Real.log c)) ≤ 1 := by
    have hxR : ‖x.1‖ ≤ R := by
      have hxmem  := x.2
      change dist x.1 0 ≤ R at hxmem
      simpa only [dist_zero_right] using hxmem
    have hnorm : ‖a + c • x.1‖ ≤ ‖a‖ + c * R := by
      calc
        ‖a + c • x.1‖ ≤ ‖a‖ + ‖c • x.1‖ := norm_add_le _ _
        _ = ‖a‖ + c * ‖x.1‖ := by rw [norm_smul, Real.norm_eq_abs, abs_of_pos hc]
        _ ≤ ‖a‖ + c * R := by nlinarith [mul_le_mul_of_nonneg_left hxR (le_of_lt hc)]
    have hexpScale (s : ℝ) : Real.exp (-(s - Real.log c)) ≤ Real.exp (-s) := by
      calc
        Real.exp (-(s - Real.log c)) = Real.exp (-s) * c := by
          rw [show -(s - Real.log c) = (-s) + Real.log c by ring, Real.exp_add,
            Real.exp_log hc]
        _ = c * Real.exp (-s) := by ring
        _ ≤ Real.exp (-s) := by
          calc
            c * Real.exp (-s) ≤ 1 * Real.exp (-s) :=
              mul_le_mul_of_nonneg_right hc1 (Real.exp_nonneg _)
            _ = Real.exp (-s) := one_mul _
    have hn : (N : ℝ) ≤ ((N + n : ℕ) : ℝ) := by simp
    have hexp := (hexpScale _).trans <|
          Real.exp_le_exp.mpr (neg_le_neg hn)
    have hgapT : gap ≤ 1 - (‖a‖ + c * R) := by
      dsimp [gap]
      exact min_le_right _ _
    linarith [hexp.trans hNgap]
  let affine : ContinuousMap ℂ ℂ := ⟨fun x => a + c • x, by fun_prop⟩
  let g  := fun j => (f j).compContinuous affine
  let scaleFactor  := fun w => c ^ 2 * Real.exp (γ * w - γ ^ 2 / 2 * σ)
  have hscaleFactor : Measurable scaleFactor := by
    dsimp [scaleFactor]
    fun_prop
  let scaleSeq  := fun n => ((N + n : ℕ) : ℝ)
  have hscaleSeq : Tendsto scaleSeq atTop atTop := by
    dsimp [scaleSeq]
    simpa only [Nat.cast_add] using
      (tendsto_atTop_add_const_left atTop (N : ℝ) tendsto_natCast_atTop_atTop)
  let targetSeq  := fun n => scaleSeq n - Real.log c
  have htargetSeq : Tendsto targetSeq atTop atTop := by
    dsimp [targetSeq]
    simpa [sub_eq_add_neg] using
      (tendsto_atTop_add_const_right atTop (-Real.log c) hscaleSeq)
  let targetCutoff  := fun n ω j =>
    ∫ x, f j x ∂regularizedGMC P Xc γ (targetSeq n) ω
  let baseCutoff  := fun n ω j =>
    ∫ x, g j x ∂regularizedGMC P Xc γ (scaleSeq n) ω
  let limitTarget  := fun ω j => ∫ x, f j x ∂M ω
  let limitBase  := fun ω j => ∫ x, g j x ∂M ω
  let cutoffProduct : ℕ → Ω × ℝ → Fin m → ℝ := fun n p j =>
    scaleFactor p.2 * baseCutoff n p.1 j
  let limitProduct : Ω × ℝ → Fin m → ℝ := fun p j =>
    scaleFactor p.2 * limitBase p.1 j
  have hconvTarget (j : Fin m) :
      TendstoInMeasure P (fun n ω => targetCutoff n ω j) atTop
        (fun ω => limitTarget ω j) := by
    change TendstoInMeasure P
      ((fun r ω => ∫ x, f j x ∂regularizedGMC P Xc γ r ω) ∘ targetSeq) atTop
      (fun ω => ∫ x, f j x ∂M ω)
    exact (hMlim (f j)).comp htargetSeq
  have hconvBase (j : Fin m) :
      TendstoInMeasure P (fun n ω => baseCutoff n ω j) atTop
        (fun ω => limitBase ω j) := by
    change TendstoInMeasure P
      ((fun r ω => ∫ x, g j x ∂regularizedGMC P Xc γ r ω) ∘ scaleSeq) atTop
      (fun ω => ∫ x, g j x ∂M ω)
    exact (hMlim (g j)).comp hscaleSeq
  have hcutTarget (n : ℕ) (j : Fin m) : AEMeasurable (fun ω => targetCutoff n ω j) P :=
    regularizedGMC_test_integral_aemeasurable P X hX Xc hXc γ _ (f j) (f j).continuous.measurable
  have hcutBase (n : ℕ) (j : Fin m) : AEMeasurable (fun ω => baseCutoff n ω j) P :=
    regularizedGMC_test_integral_aemeasurable P X hX Xc hXc γ _ (g j) (g j).continuous.measurable
  have hcutTargetVec (n : ℕ) : AEMeasurable (targetCutoff n) P := by
    apply aemeasurable_pi_iff.2
    intro j
    exact hcutTarget n j
  have hcutProduct (n : ℕ) : AEMeasurable (cutoffProduct n) (P.prod G) := by
    apply aemeasurable_pi_iff.2
    intro j
    have hfst : Measure.map (fun p : Ω × ℝ => p.1) (P.prod G) = P := measurePreserving_fst.map_eq
    have hbase : AEMeasurable (fun p : Ω × ℝ => baseCutoff n p.1 j) (P.prod G) := by
      have hbase' : AEMeasurable (fun ω => baseCutoff n ω j)
          (Measure.map (fun p : Ω × ℝ => p.1) (P.prod G)) := by
        rw [hfst]
        exact hcutBase n j
      change AEMeasurable
        ((fun ω => baseCutoff n ω j) ∘ (fun p : Ω × ℝ => p.1)) (P.prod G)
      exact hbase'.comp_aemeasurable measurable_fst.aemeasurable
    have hfactor : AEMeasurable (fun p : Ω × ℝ => scaleFactor p.2) (P.prod G) :=
      hscaleFactor.comp_aemeasurable measurable_snd.aemeasurable
    exact (hfactor.mul hbase)
  have hlimitTarget : AEMeasurable limitTarget P := by
    apply aemeasurable_pi_iff.2
    intro j
    exact (hconvTarget j).aemeasurable (fun n => hcutTarget n j)
  have hlimitProduct : AEMeasurable limitProduct (P.prod G) := by
    apply aemeasurable_pi_iff.2
    intro j
    have hbaseP  :=
      (hconvBase j).aemeasurable (fun n => hcutBase n j)
    have hfst : Measure.map (fun p : Ω × ℝ => p.1) (P.prod G) = P := measurePreserving_fst.map_eq
    have hbase : AEMeasurable (fun p : Ω × ℝ => limitBase p.1 j) (P.prod G) := by
      have hbase' : AEMeasurable (fun ω => limitBase ω j)
          (Measure.map (fun p : Ω × ℝ => p.1) (P.prod G)) := by
        simpa
      change AEMeasurable
        ((fun ω => limitBase ω j) ∘ (fun p : Ω × ℝ => p.1)) (P.prod G)
      exact hbase'.comp_aemeasurable measurable_fst.aemeasurable
    have hfactor : AEMeasurable (fun p : Ω × ℝ => scaleFactor p.2) (P.prod G) :=
      hscaleFactor.comp_aemeasurable measurable_snd.aemeasurable
    exact hfactor.mul hbase
  have hcutLaw (n : ℕ) : Measure.map (targetCutoff n) P =
      Measure.map (cutoffProduct n) (P.prod G) := by
    have h := regularizedGMC_affine_cutoff_test_vector_law P X hX Xc hXc γ
      (a := a) (c := c) (R := R) (r := scaleSeq n) hc hc1 hR
      (hsourceCut n) (htargetCut n) f hf_nonneg hf_support
    assumption
  have hconvProduct (j : Fin m) :
      TendstoInMeasure (P.prod G) (fun n p => cutoffProduct n p j) atTop
        (fun p => limitProduct p j) :=
    tendstoInMeasure_mul_snd_of_tendstoInMeasure
      (fun n ω => baseCutoff n ω j) (fun ω => limitBase ω j) scaleFactor
      hscaleFactor (hconvBase j)
  exact gmc_limit_test_vector_law targetCutoff cutoffProduct limitTarget limitProduct
    (fun n => hcutTargetVec n) hcutProduct hlimitTarget hlimitProduct hcutLaw
    hconvTarget hconvProduct

end DOZZ.Proofs
