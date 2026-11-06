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
    {Ω : Type*} [MeasurableSpace Ω] {m}
    (P : Measure Ω) X (hX : IsEquatorGFF P X) γ
    (M : Ω → Measure ℂ) (hM : IsGMCOf P X γ M)
    {a} {c R} (hc : 0 < c) (hc1 : c ≤ 1) (hR : 0 < R)
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
  let σ : ℝ := -Real.log c
  let G := gaussianReal 0 ⟨σ,
    neg_nonneg.mpr (Real.log_nonpos (le_of_lt hc) hc1)⟩
  have hG : IsProbabilityMeasure G := by
    simpa [G, σ] using (ProbabilityTheory.instIsProbabilityMeasureGaussianReal 0
      ⟨-Real.log c, neg_nonneg.mpr (Real.log_nonpos (le_of_lt hc) hc1)⟩)
  let : IsProbabilityMeasure P := hX.1
  let : IsProbabilityMeasure G := hG
  let : IsProbabilityMeasure (P.prod G) := inferInstance
  let gap : ℝ := min (1 - R) (1 - (‖a‖ + c * R))
  obtain ⟨N, hN⟩ := eventually_atTop.1 (show ∀ᶠ n : ℕ in atTop, Real.exp (-(n : ℝ)) < gap by exact (Real.tendsto_exp_neg_atTop_nhds_zero.comp tendsto_natCast_atTop_atTop).eventually (isOpen_Iio.mem_nhds (by dsimp [gap]; exact lt_min (by linarith) (by linarith))))
  have hNgap : Real.exp (-(N : ℝ)) ≤ gap := le_of_lt (hN N le_rfl)
  have hsourceUnit : ∀ x ∈ Metric.closedBall (0 : ℂ) R, ‖x‖ ≤ 1 := by
    intro x hx
    have hxR : ‖x‖ ≤ R := by
      have hxmem := hx
      change dist x 0 ≤ R at hxmem
      simpa only [dist_zero_right] using hxmem
    exact hxR.trans hRsmall.le
  have htargetUnit : ∀ x ∈ Metric.closedBall a (c * R), ‖x‖ ≤ 1 := by
    intro x hx
    calc
      ‖x‖ = ‖(x - a) + a‖ := by congr 1; abel
      _ ≤ ‖x - a‖ + ‖a‖ := norm_add_le _ _
      _ ≤ c * R + ‖a‖ := by nlinarith [(by change dist x a ≤ c * R at hx; simpa only [dist_eq_norm] using hx)]
      _ ≤ 1 := by linarith [hTsmall]
  have hsourceCut (n : ℕ) (x : {z : ℂ // z ∈ Metric.closedBall (0 : ℂ) R}) :
      ‖x.1‖ + Real.exp (-((N + n : ℕ) : ℝ)) ≤ 1 := by
    have : ‖x.1‖ ≤ R := by
      have hxmem : x.1 ∈ Metric.closedBall (0 : ℂ) R := x.2
      change dist x.1 0 ≤ R at hxmem
      simpa only [dist_zero_right] using hxmem
    have : gap ≤ 1 - R := by dsimp [gap]; exact min_le_left _ _
    linarith [(Real.exp_le_exp.mpr (neg_le_neg (by exact_mod_cast Nat.le_add_right N n)) : Real.exp (-((N + n : ℕ) : ℝ)) ≤ Real.exp (-(N : ℝ))).trans hNgap]
  have htargetCut (n : ℕ) (x : {z : ℂ // z ∈ Metric.closedBall (0 : ℂ) R}) :
      ‖a + c • x.1‖ + Real.exp (-(((N + n : ℕ) : ℝ) - Real.log c)) ≤ 1 := by
    have hxR : ‖x.1‖ ≤ R := by
      have hxmem := x.2
      change dist x.1 0 ≤ R at hxmem
      simpa only [dist_zero_right] using hxmem
    have : ‖a + c • x.1‖ ≤ ‖a‖ + c * R := by
      calc
        ‖a + c • x.1‖ ≤ ‖a‖ + ‖c • x.1‖ := norm_add_le _ _
        _ = ‖a‖ + c * ‖x.1‖ := by rw [norm_smul, Real.norm_eq_abs, abs_of_pos hc]
        _ ≤ ‖a‖ + c * R := by nlinarith [mul_le_mul_of_nonneg_left hxR (le_of_lt hc)]
    have hexpScale s : Real.exp (-(s - Real.log c)) ≤ Real.exp (-s) := by
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
    have : gap ≤ 1 - (‖a‖ + c * R) := by
      dsimp [gap]
      exact min_le_right _ _
    linarith [((hexpScale _).trans <| Real.exp_le_exp.mpr (neg_le_neg (by exact_mod_cast Nat.le_add_right N n)) : Real.exp (-(((N + n : ℕ) : ℝ) - Real.log c)) ≤ Real.exp (-(N : ℝ))).trans hNgap]
  let affine : ContinuousMap ℂ ℂ := ⟨fun x => a + c • x, by fun_prop⟩
  let g : Fin m → BoundedContinuousFunction ℂ ℝ := fun j => (f j).compContinuous affine
  have htargetZero (j : Fin m) := boundedContinuousFunction_eq_zero_off_tsupport_subset (f j)
      (Metric.closedBall a (c * R)) (hf_support j)
  have hbaseZero j : ∀ x, x ∉ Metric.closedBall (0 : ℂ) R → g j x = 0 := by
    intro x hx
    change f j (a + c • x) = 0
    apply htargetZero j
    intro hy
    obtain ⟨y, hyball, hyEq⟩ := (show a + c • x ∈ (fun y : ℂ => a + c • y) '' Metric.closedBall (0 : ℂ) R by rw [(complex_affine_image_closedBall hc)]; exact hy)
    have hxy : x = y := (show Function.Injective (fun x => a + c • x) by intro x y hxy; exact (smul_right_injective ℂ hc.ne') (add_left_cancel hxy)) (by simpa using hyEq.symm)
    exact hx (hxy ▸ hyball)
  let scaleFactor : ℝ → ℝ := fun w => c ^ 2 * Real.exp (γ * w - γ ^ 2 / 2 * σ)
  have hscaleFactor : Measurable scaleFactor := by
    dsimp [scaleFactor]
    fun_prop
  let scaleSeq : ℕ → ℝ := fun n => ((N + n : ℕ) : ℝ)
  have hscaleSeq : Tendsto scaleSeq atTop atTop := by
    dsimp [scaleSeq]
    simpa only [Nat.cast_add] using
      (tendsto_atTop_add_const_left atTop (N : ℝ) tendsto_natCast_atTop_atTop)
  let targetSeq : ℕ → ℝ := fun n => scaleSeq n - Real.log c
  let targetCutoff : ℕ → Ω → Fin m → ℝ := fun n ω j =>
    ∫ x, f j x ∂regularizedGMC P Xc γ (targetSeq n) ω
  let baseCutoff : ℕ → Ω → Fin m → ℝ := fun n ω j =>
    ∫ x, g j x ∂regularizedGMC P Xc γ (scaleSeq n) ω
  let limitTarget : Ω → Fin m → ℝ := fun ω j => ∫ x, f j x ∂M ω
  let limitBase : Ω → Fin m → ℝ := fun ω j => ∫ x, g j x ∂M ω
  let cutoffProduct : ℕ → Ω × ℝ → Fin m → ℝ := fun n p j =>
    scaleFactor p.2 * baseCutoff n p.1 j
  let limitProduct : Ω × ℝ → Fin m → ℝ := fun p j =>
    scaleFactor p.2 * limitBase p.1 j
  have hconvTarget j :
      TendstoInMeasure P (fun n ω => targetCutoff n ω j) atTop
        (fun ω => limitTarget ω j) := by
    change TendstoInMeasure P
      ((fun r ω => ∫ x, f j x ∂regularizedGMC P Xc γ r ω) ∘ targetSeq) atTop
      (fun ω => ∫ x, f j x ∂M ω)
    exact (hMlim (f j)).comp (by dsimp [targetSeq]; simpa [sub_eq_add_neg] using (tendsto_atTop_add_const_right atTop (-Real.log c) hscaleSeq))
  have hconvBase j :
      TendstoInMeasure P (fun n ω => baseCutoff n ω j) atTop
        (fun ω => limitBase ω j) := by
    change TendstoInMeasure P
      ((fun r ω => ∫ x, g j x ∂regularizedGMC P Xc γ r ω) ∘ scaleSeq) atTop
      (fun ω => ∫ x, g j x ∂M ω)
    exact (hMlim (g j)).comp hscaleSeq
  have hcutTarget n j : AEMeasurable
      (fun ω => targetCutoff n ω j) P := by
    apply regularizedGMC_test_integral_aemeasurable P X hX Xc hXc γ (targetSeq n)
      (Metric.closedBall a (c * R)) Metric.isClosed_closedBall.measurableSet htargetUnit
      (f j) (f j).continuous.measurable (htargetZero j)
  have hcutBase n j : AEMeasurable
      (fun ω => baseCutoff n ω j) P := by
    apply regularizedGMC_test_integral_aemeasurable P X hX Xc hXc γ (scaleSeq n)
      (Metric.closedBall (0 : ℂ) R) Metric.isClosed_closedBall.measurableSet hsourceUnit
      (g j) (g j).continuous.measurable (hbaseZero j)
  have hcutTargetVec n : AEMeasurable (targetCutoff n) P := by
    apply aemeasurable_pi_iff.2
    intro j
    exact hcutTarget n j
  have hlimitTarget : AEMeasurable limitTarget P := by
    apply aemeasurable_pi_iff.2
    intro j
    exact (hconvTarget j).aemeasurable (fun n => hcutTarget n j)
  have hcutLaw n : Measure.map (targetCutoff n) P =
      Measure.map (cutoffProduct n) (P.prod G) := by
    simpa [targetCutoff, cutoffProduct, baseCutoff, scaleFactor, scaleSeq,
      targetSeq, σ, G, g, BoundedContinuousFunction.compContinuous_apply, affine] using (regularizedGMC_affine_cutoff_test_vector_law P X hX Xc hXc γ (a := a) (c := c) (R := R) (r := scaleSeq n) hc hc1 hR (hsourceCut n) (htargetCut n) hsourceUnit htargetUnit f hf_nonneg hf_support)
  have hconvProduct j :
      TendstoInMeasure (P.prod G) (fun n p => cutoffProduct n p j) atTop
        (fun p => limitProduct p j) :=
    tendstoInMeasure_mul_snd_of_tendstoInMeasure
      (fun n ω => baseCutoff n ω j) (fun ω => limitBase ω j) scaleFactor
      hscaleFactor (hconvBase j)
  exact gmc_limit_test_vector_law targetCutoff cutoffProduct limitTarget limitProduct
    (fun n => hcutTargetVec n) (fun n => by apply aemeasurable_pi_iff.2; intro j; exact ((hscaleFactor.comp_aemeasurable measurable_snd.aemeasurable).mul (by change AEMeasurable ((fun ω => baseCutoff n ω j) ∘ (fun p : Ω × ℝ => p.1)) (P.prod G); exact (show AEMeasurable (fun ω => baseCutoff n ω j) (Measure.map (fun p : Ω × ℝ => p.1) (P.prod G)) by rw [(show Measure.map (fun p : Ω × ℝ => p.1) (P.prod G) = P by exact measurePreserving_fst.map_eq)]; exact hcutBase n j).comp_aemeasurable measurable_fst.aemeasurable))) hlimitTarget (by apply aemeasurable_pi_iff.2; intro j; exact (hscaleFactor.comp_aemeasurable measurable_snd.aemeasurable).mul (by change AEMeasurable ((fun ω => limitBase ω j) ∘ (fun p : Ω × ℝ => p.1)) (P.prod G); exact (show AEMeasurable (fun ω => limitBase ω j) (Measure.map (fun p : Ω × ℝ => p.1) (P.prod G)) by rw [(show Measure.map (fun p : Ω × ℝ => p.1) (P.prod G) = P by exact measurePreserving_fst.map_eq)]; exact ((hconvBase j).aemeasurable (fun n => hcutBase n j))).comp_aemeasurable measurable_fst.aemeasurable)) hcutLaw
    hconvTarget hconvProduct

end DOZZ.Proofs
