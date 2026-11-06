/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.GMC.Moments.RegularizedScale
public import DOZZ.GMC.Moments.OpenBallApproximation
public import DOZZ.GMC.Moments.CutoffSubunit
public import DOZZ.GMC.Construction.RegularizedGMCExpectedMeasure
public import DOZZ.GMC.Moments.ChaosLawFDDLimit
public import DOZZ.GMC.Moments.ScaleLimit
public import DOZZ.GMC.Moments.ExactScaleBallMoment
import Mathlib.Tactic

/-! Exact affine scaling for open-ball masses of the finite circle-cutoff chaos. -/

public section

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped Distributions ENNReal NNReal BoundedContinuousFunction

namespace DOZZ.Proofs

variable {Ω : Type*} [_inst1 : MeasurableSpace Ω] (P : Measure Ω) (X : Ω → Distr) (hX : IsEquatorGFF P X) (Xc : Ω → ℂ → ℝ → ℝ) (hXc : IsCircleAverage P X Xc) (γ : ℝ) {a : ℂ} {c R r : ℝ} (hc : 0 < c) (hc1 : c ≤ 1) (hR : 0 < R) (hsourceCut : ∀ x : {z : ℂ // z ∈ Metric.closedBall (0 : ℂ) R}, ‖x.1‖ + Real.exp (-r) ≤ 1) (htargetCut : ∀ x : {z : ℂ // z ∈ Metric.closedBall (0 : ℂ) R}, ‖a + c • x.1‖ + Real.exp (-(r - Real.log c)) ≤ 1) (hsourceUnit : ∀ x ∈ Metric.closedBall (0 : ℂ) R, ‖x‖ ≤ 1) (htargetUnit : ∀ x ∈ Metric.closedBall a (c * R), ‖x‖ ≤ 1)

include Ω _inst1 P X hX Xc hXc γ a c R r hc hc1 hR hsourceCut htargetCut hsourceUnit htargetUnit in
/-- The finite-cutoff affine test-vector law passes to open-ball masses. The cutoff radius is
scaled together with the disk, and the common Gaussian shift contributes the same scalar as in
the test-vector identity. -/
theorem regularizedGMC_affine_openBall_mass_law
     :
    Measure.map (fun ω : Ω =>
      (regularizedGMC P Xc γ (r - Real.log c) ω (Metric.ball a (c * R))).toReal) P =
    Measure.map (fun q : Ω × ℝ =>
      c ^ 2 * Real.exp (γ * q.2 - γ ^ 2 / 2 * (-Real.log c)) *
        (regularizedGMC P Xc γ r q.1 (Metric.ball 0 R)).toReal)
      (P.prod (gaussianReal 0 ⟨-Real.log c,
        neg_nonneg.mpr (Real.log_nonpos hc.le hc1)⟩)) := by
  classical
  have hP  := hX.1
  let G  := gaussianReal 0 ⟨-Real.log c,
    neg_nonneg.mpr (Real.log_nonpos hc.le hc1)⟩
  have hG : IsProbabilityMeasure G := (ProbabilityTheory.instIsProbabilityMeasureGaussianReal 0
      ⟨-Real.log c, neg_nonneg.mpr (Real.log_nonpos hc.le hc1)⟩)

  let f : ℕ → BoundedContinuousFunction ℂ ℝ := fun n => openBallAffineApprox a c R n
  let g : ℕ → BoundedContinuousFunction ℂ ℝ := fun n => openBallApprox 0 R n
  have hfSupport (n : ℕ) : tsupport (f n : ℂ → ℝ) ⊆ Metric.closedBall a (c * R) :=
    openBallAffineApprox_tsupport_subset hc n
  have hgSupport (n : ℕ) : tsupport (g n : ℂ → ℝ) ⊆ Metric.closedBall 0 R :=
    openBallApprox_tsupport_subset 0 R n
  have hfzero (n : ℕ) (x : ℂ) (hx : x ∉ Metric.closedBall a (c * R)) : f n x = 0 :=
    boundedContinuousFunction_eq_zero_off_tsupport_subset (f n)
      (Metric.closedBall a (c * R)) (hfSupport n) x hx
  have hgzero (n : ℕ) (x : ℂ) (hx : x ∉ Metric.closedBall 0 R) : g n x = 0 :=
    boundedContinuousFunction_eq_zero_off_tsupport_subset (g n)
      (Metric.closedBall 0 R) (hgSupport n) x hx
  have hfNonneg (n : ℕ) : ∀ x, 0 ≤ f n x := by
    intro x
    exact (openBallApproxFun_bounds 0 R n _).1
  have htargetMeas (n : ℕ) : AEMeasurable
      (fun ω => ∫ x, f n x ∂regularizedGMC P Xc γ (r - Real.log c) ω) P := regularizedGMC_test_integral_aemeasurable P X hX Xc hXc γ
      (r - Real.log c) (Metric.closedBall a (c * R))
      Metric.isClosed_closedBall.measurableSet htargetUnit (f n) (f n).continuous.measurable
      (hfzero n)
  have hsourceMeas (n : ℕ) : AEMeasurable
      (fun ω => ∫ x, g n x ∂regularizedGMC P Xc γ r ω) P := regularizedGMC_test_integral_aemeasurable P X hX Xc hXc γ r
      (Metric.closedBall 0 R) Metric.isClosed_closedBall.measurableSet hsourceUnit
      (g n) (g n).continuous.measurable (hgzero n)
  let targetCutoff : ℕ → Ω → Fin 1 → ℝ := fun n ω _ =>
    ∫ x, f n x ∂regularizedGMC P Xc γ (r - Real.log c) ω
  let sourceCutoff : ℕ → Ω × ℝ → Fin 1 → ℝ := fun n q _ =>
    c ^ 2 * Real.exp (γ * q.2 - γ ^ 2 / 2 * (-Real.log c)) *
      ∫ x, g n x ∂regularizedGMC P Xc γ r q.1
  have htargetCutoffMeas (n : ℕ) : AEMeasurable (targetCutoff n) P := aemeasurable_pi_iff.2 (fun _ => htargetMeas n)
  have hsourceCutoffMeas (n : ℕ) : AEMeasurable (sourceCutoff n) (P.prod G) := by
    apply aemeasurable_pi_iff.2
    intro j
    have hfst : Measure.map (fun q : Ω × ℝ => q.1) (P.prod G) = P :=
      measurePreserving_fst.map_eq
    have hbase : AEMeasurable
        (fun q : Ω × ℝ => ∫ x, g n x ∂regularizedGMC P Xc γ r q.1) (P.prod G) := by
      have hbase' : AEMeasurable
          (fun ω => ∫ x, g n x ∂regularizedGMC P Xc γ r ω)
          (Measure.map (fun q : Ω × ℝ => q.1) (P.prod G)) := by
        rw [hfst]
        exact hsourceMeas n
      exact hbase'.comp_aemeasurable measurable_fst.aemeasurable
    fun_prop
  let targetLimit : Ω → Fin 1 → ℝ := fun ω _ =>
    (regularizedGMC P Xc γ (r - Real.log c) ω (Metric.ball a (c * R))).toReal
  let sourceLimit : Ω × ℝ → Fin 1 → ℝ := fun q _ =>
    c ^ 2 * Real.exp (γ * q.2 - γ ^ 2 / 2 * (-Real.log c)) *
      (regularizedGMC P Xc γ r q.1 (Metric.ball 0 R)).toReal
  have htargetLimitMeas : AEMeasurable targetLimit P := by
    apply aemeasurable_pi_iff.2
    intro j
    have hm := regularizedGMC_mass_aemeasurable P X hX Xc hXc γ
      (r - Real.log c) (Metric.ball a (c * R)) Metric.isOpen_ball.measurableSet
    exact ENNReal.measurable_toReal.comp_aemeasurable hm
  have hsourceLimitMeas : AEMeasurable sourceLimit (P.prod G) := by
    apply aemeasurable_pi_iff.2
    intro j
    have hm := regularizedGMC_mass_aemeasurable P X hX Xc hXc γ r
      (Metric.ball 0 R) Metric.isOpen_ball.measurableSet
    fun_prop
  have htargetConvCoord (j : Fin 1) :
      TendstoInMeasure P (fun n ω => targetCutoff n ω j) atTop
        (fun ω => targetLimit ω j) := by
    have hfinite := regularizedGMC_finite_ae P X hX Xc hXc γ (r - Real.log c)
    have hpoint (ω : Ω) (hω : IsFiniteMeasure
        (regularizedGMC P Xc γ (r - Real.log c) ω)) :
        Tendsto (fun n => ∫ x, f n x ∂regularizedGMC P Xc γ (r - Real.log c) ω)
          atTop (𝓝 ((regularizedGMC P Xc γ (r - Real.log c) ω
            (Metric.ball a (c * R))).toReal)) := openBallAffineApprox_integral_tendsto hc
        (regularizedGMC P Xc γ (r - Real.log c) ω)
    exact tendstoInMeasure_of_tendsto_ae
      (fun n => (htargetMeas n).aestronglyMeasurable)
      (hfinite.mono fun ω hω => hpoint ω hω)
  have hsourceConvCoord :
      TendstoInMeasure P (fun n ω => ∫ x, g n x ∂regularizedGMC P Xc γ r ω) atTop
        (fun ω => (regularizedGMC P Xc γ r ω (Metric.ball 0 R)).toReal) := by
    have hfinite := regularizedGMC_finite_ae P X hX Xc hXc γ r
    have hpoint (ω : Ω) (hω : IsFiniteMeasure (regularizedGMC P Xc γ r ω)) :
        Tendsto (fun n => ∫ x, g n x ∂regularizedGMC P Xc γ r ω) atTop
          (𝓝 ((regularizedGMC P Xc γ r ω (Metric.ball 0 R)).toReal)) := openBallApprox_integral_tendsto 0 R
        (regularizedGMC P Xc γ r ω)
    exact tendstoInMeasure_of_tendsto_ae
      (fun n => (hsourceMeas n).aestronglyMeasurable)
      (hfinite.mono fun ω hω => hpoint ω hω)

  have hsourceConvCoordProd (j : Fin 1) :
      TendstoInMeasure (P.prod G) (fun n q => sourceCutoff n q j) atTop
        (fun q => sourceLimit q j) := tendstoInMeasure_mul_snd_of_tendstoInMeasure
      (fun n ω => ∫ x, g n x ∂regularizedGMC P Xc γ r ω)
      (fun ω => (regularizedGMC P Xc γ r ω (Metric.ball 0 R)).toReal)
      (fun w => c ^ 2 * Real.exp (γ * w - γ ^ 2 / 2 * (-Real.log c)))
      (by fun_prop) hsourceConvCoord

  have hcutoffLaw (n : ℕ) : Measure.map (targetCutoff n) P =
      Measure.map (sourceCutoff n) (P.prod G) := by
    let fvec : Fin 1 → BoundedContinuousFunction ℂ ℝ := fun _ => f n
    have h := regularizedGMC_affine_cutoff_test_vector_law P X hX Xc hXc γ
      (a := a) (c := c) (R := R) (r := r) hc hc1 hR hsourceCut htargetCut
      hsourceUnit htargetUnit fvec (fun _ => hfNonneg n) (fun _ => hfSupport n)
    have hvalues : (fun q : Ω × ℝ => fun j : Fin 1 =>
        c ^ 2 * Real.exp (γ * q.2 - γ ^ 2 / 2 * (-Real.log c)) *
          ∫ x, fvec j (a + c • x) ∂regularizedGMC P Xc γ r q.1) = sourceCutoff n := by
      funext q j
      have htest (x : ℂ) : f n (a + c • x) = g n x :=
        openBallAffineApprox_comp_affine a c R hc.ne' n x
      grind
    grind
  have hvecLaw := gmc_limit_test_vector_law targetCutoff sourceCutoff targetLimit sourceLimit
    (fun n => htargetCutoffMeas n) (fun n => hsourceCutoffMeas n)
    htargetLimitMeas hsourceLimitMeas hcutoffLaw
    (fun j => htargetConvCoord j)
    (fun j => hsourceConvCoordProd j)
  let eval : (Fin 1 → ℝ) → ℝ := fun v => v 0
  have heval : Measurable eval := by fun_prop
  have hleft : Measure.map eval (Measure.map targetLimit P) =
      Measure.map (fun ω => targetLimit ω 0) P := by
    rw [AEMeasurable.map_map_of_aemeasurable heval.aemeasurable htargetLimitMeas]
    abel
  have hright : Measure.map eval (Measure.map sourceLimit (P.prod G)) =
      Measure.map (fun q => sourceLimit q 0) (P.prod G) := by
    rw [AEMeasurable.map_map_of_aemeasurable heval.aemeasurable hsourceLimitMeas]
    abel
  grind

include Ω _inst1 P X hX Xc hXc γ a c R r hc hc1 hR hsourceCut htargetCut hsourceUnit htargetUnit in
/-- Every real moment of a finite-cutoff open-ball mass obeys the exact affine scaling law. -/
theorem regularizedGMC_affine_openBall_moment_scale

    (p : ℝ) :
    ∫⁻ ω, ENNReal.rpow
      (regularizedGMC P Xc γ (r - Real.log c) ω (Metric.ball a (c * R))) p ∂P =
      ENNReal.ofReal (c ^ (2 * p + γ ^ 2 * p / 2 - γ ^ 2 * p ^ 2 / 2)) *
        ∫⁻ ω, ENNReal.rpow (regularizedGMC P Xc γ r ω (Metric.ball 0 R)) p ∂P := by
  classical
  let G  := gaussianReal 0 ⟨-Real.log c,
    neg_nonneg.mpr (Real.log_nonpos hc.le hc1)⟩
  have hG : IsProbabilityMeasure G := (ProbabilityTheory.instIsProbabilityMeasureGaussianReal 0
      ⟨-Real.log c, neg_nonneg.mpr (Real.log_nonpos hc.le hc1)⟩)
  have hPG : IsProbabilityMeasure (P.prod G) := by
    let hP  := hX.1
    let hG'  := hG
    infer_instance
  let targetMass  := fun ω =>
    regularizedGMC P Xc γ (r - Real.log c) ω (Metric.ball a (c * R))
  let sourceMass  := fun ω =>
    regularizedGMC P Xc γ r ω (Metric.ball 0 R)
  let targetCoord  := fun ω => (targetMass ω).toReal
  let sourceCoord : Ω × ℝ → ℝ := fun q =>
    c ^ 2 * Real.exp (γ * q.2 - γ ^ 2 / 2 * (-Real.log c)) *
      (sourceMass q.1).toReal
  let scaleFactor  := fun w =>
    c ^ 2 * Real.exp (γ * w - γ ^ 2 / 2 * (-Real.log c))
  have htargetMassMeas  :=
    regularizedGMC_mass_aemeasurable P X hX Xc hXc γ (r - Real.log c)
      (Metric.ball a (c * R)) Metric.isOpen_ball.measurableSet
  have hsourceMassMeas  :=
    regularizedGMC_mass_aemeasurable P X hX Xc hXc γ r
      (Metric.ball 0 R) Metric.isOpen_ball.measurableSet
  have htargetCoordMeas : AEMeasurable targetCoord P :=
    ENNReal.measurable_toReal.comp_aemeasurable htargetMassMeas
  have hsourceCoordMeas : AEMeasurable sourceCoord (P.prod G) := by
    fun_prop
  have hmassLaw := regularizedGMC_affine_openBall_mass_law P X hX Xc hXc γ
    (a := a) (c := c) (R := R) (r := r) hc hc1 hR hsourceCut htargetCut
    hsourceUnit htargetUnit
  change Measure.map targetCoord P = Measure.map sourceCoord (P.prod G) at hmassLaw
  let ψ  := fun x => ENNReal.rpow (ENNReal.ofReal x) p
  have hψ : Measurable ψ := by dsimp [ψ]; fun_prop
  have htargetFinite := regularizedGMC_finite_ae P X hX Xc hXc γ (r - Real.log c)
  have hsourceFinite := regularizedGMC_finite_ae P X hX Xc hXc γ r
  have hleft : ∫⁻ ω, ENNReal.rpow (targetMass ω) p ∂P =
      ∫⁻ y, ψ y ∂Measure.map targetCoord P := by
    calc
      _ = ∫⁻ ω, ψ (targetCoord ω) ∂P := by
        apply lintegral_congr_ae
        filter_upwards [htargetFinite] with ω hω
        have hnotTop : targetMass ω ≠ ∞ := measure_ne_top _ _
        change ENNReal.rpow (targetMass ω) p =
          ENNReal.rpow (ENNReal.ofReal ((targetMass ω).toReal)) p
        rw [ENNReal.ofReal_toReal hnotTop]
      _ = _ := by rw [lintegral_map' hψ.aemeasurable htargetCoordMeas]
  have hright : ∫⁻ y, ψ y ∂Measure.map sourceCoord (P.prod G) =
      ∫⁻ q, ψ (sourceCoord q) ∂P.prod G := by
    rw [lintegral_map' hψ.aemeasurable hsourceCoordMeas]
  have hbaseMomentMeas : AEMeasurable
      (fun ω => ENNReal.rpow (sourceMass ω) p) P :=
    ENNReal.continuous_rpow_const.measurable.comp_aemeasurable hsourceMassMeas
  have hfactorMomentMeas : AEMeasurable
      (fun w => ENNReal.rpow (ENNReal.ofReal (scaleFactor w)) p) G := by
    have hscale : Measurable scaleFactor := by dsimp [scaleFactor]; fun_prop
    exact (ENNReal.continuous_rpow_const.measurable.comp
      (ENNReal.measurable_ofReal.comp hscale)).aemeasurable
  have hprod : ∫⁻ q, ψ (sourceCoord q) ∂P.prod G =
      (∫⁻ ω, ENNReal.rpow (sourceMass ω) p ∂P) *
        (∫⁻ w, ENNReal.rpow (ENNReal.ofReal (scaleFactor w)) p ∂G) := by
    calc
      _ = ∫⁻ q, ENNReal.rpow (sourceMass q.1) p *
            ENNReal.rpow (ENNReal.ofReal (scaleFactor q.2)) p ∂P.prod G := by
        apply lintegral_congr_ae
        have hfiniteProd : ∀ᵐ q ∂P.prod G,
            IsFiniteMeasure (regularizedGMC P Xc γ r q.1) :=
          (Measure.quasiMeasurePreserving_fst (μ := P) (ν := G)).ae
            (regularizedGMC_finite_ae P X hX Xc hXc γ r)
        filter_upwards [hfiniteProd] with q hq
        have hnotTop : sourceMass q.1 ≠ ∞ := measure_ne_top _ _
        have hscalePos : 0 < scaleFactor q.2 := by dsimp [scaleFactor]; positivity
        change ENNReal.rpow
          (ENNReal.ofReal (scaleFactor q.2 * (sourceMass q.1).toReal)) p = _
        rw [ENNReal.ofReal_mul' ENNReal.toReal_nonneg,
          ENNReal.ofReal_toReal hnotTop]
        simpa [mul_comm] using
          (ENNReal.mul_rpow_of_ne_top (x := ENNReal.ofReal (scaleFactor q.2))
            (y := sourceMass q.1) ENNReal.ofReal_ne_top hnotTop p)
      _ = _ := by rw [lintegral_prod_mul hbaseMomentMeas hfactorMomentMeas]
  calc
    _ = ∫⁻ y, ψ y ∂Measure.map targetCoord P := hleft
    _ = ∫⁻ y, ψ y ∂Measure.map sourceCoord (P.prod G) := by rw [hmassLaw]
    _ = ∫⁻ q, ψ (sourceCoord q) ∂P.prod G := hright
    _ = (∫⁻ ω, ENNReal.rpow (sourceMass ω) p ∂P) *
          (∫⁻ w, ENNReal.rpow (ENNReal.ofReal (scaleFactor w)) p ∂G) := hprod
    _ = _ := by
      rw [gaussianScaleFactor_rpow_integral γ c p hc hc1]
      ac_rfl

/-- A finite-cutoff ball mass at scales no finer than its cutoff has the exact subunit scaling
bound obtained from the reference half-disk intensity. -/
theorem regularizedGMC_openBall_subunit_scale_bound
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (X : Ω → Distr) (hX : IsEquatorGFF P X)
    (Xc : Ω → ℂ → ℝ → ℝ) (hXc : IsCircleAverage P X Xc)
    (γ : ℝ) (z : ℂ) (s δ p : ℝ)
    (hs : 0 < s) (hs1 : s ≤ 1 / 2) (hδ : 0 < δ) (hδs : δ ≤ s)
    (hchart : ‖z‖ + 2 * s ≤ 1) (hp : 0 ≤ p) (hp1 : p ≤ 1) :
    ∫⁻ ω, ENNReal.rpow
      (regularizedGMC P Xc γ (Real.log (1 / δ)) ω (Metric.ball z s)) p ∂P ≤
      ENNReal.ofReal ((2 * s) ^
        (2 * p + γ ^ 2 * p / 2 - γ ^ 2 * p ^ 2 / 2)) *
        (1 + gmcReferenceMeasure (Metric.ball 0 (1 / 2))) := by
  let c  := 2 * s
  let r  := Real.log (1 / δ) + Real.log c
  have hc : 0 < c := by dsimp [c]; positivity
  have hc1 : c ≤ 1 := by dsimp [c]; linarith
  have hδc : Real.exp (-r) = δ / c := by
    have hδrec : Real.exp (-Real.log (1 / δ)) = δ := by
      rw [Real.exp_neg, Real.exp_log (by positivity)]
      field_simp
    have hcrec : Real.exp (-Real.log c) = c⁻¹ := by
      rw [Real.exp_neg, Real.exp_log hc]
    rw [show -r = -Real.log (1 / δ) + -Real.log c by dsimp [r]; ring,
      Real.exp_add, hδrec, hcrec]
    dsimp [c]
    field_simp
  have htargetCutoff : Real.exp (-(r - Real.log c)) = δ := by
    have hr : r - Real.log c = Real.log (1 / δ) := by
      dsimp [r]
      ring
    rw [hr]
    exact exp_neg_log_one_div hδ
  have hsourceCut : ∀ x : {w : ℂ // w ∈ Metric.closedBall (0 : ℂ) (1 / 2 : ℝ)},
      ‖x.1‖ + Real.exp (-r) ≤ 1 := by
    intro x
    have hx : ‖x.1‖ ≤ (1 / 2 : ℝ) := by
      continuity
    have hδcHalf : δ / c ≤ (1 / 2 : ℝ) := by
      field_simp <;> nlinarith
    rw [hδc]
    linarith
  have htargetCut : ∀ x : {w : ℂ // w ∈ Metric.closedBall (0 : ℂ) (1 / 2 : ℝ)},
      ‖z + c • x.1‖ + Real.exp (-(r - Real.log c)) ≤ 1 := by
    intro x
    have hx : ‖x.1‖ ≤ (1 / 2 : ℝ) := by
      simpa [Metric.mem_closedBall, dist_zero_right] using x.2
    have hnorm : ‖z + c • x.1‖ ≤ ‖z‖ + s := by
      calc
        ‖z + c • x.1‖ ≤ ‖z‖ + ‖c • x.1‖ := norm_add_le _ _
        _ = ‖z‖ + c * ‖x.1‖ := by simp [abs_of_pos hc]
        _ ≤ ‖z‖ + c * (1 / 2 : ℝ) := by
          simp_all
        _ = ‖z‖ + s := by dsimp [c]; ring
    grind
  have hsourceUnit : ∀ x ∈ Metric.closedBall (0 : ℂ) (1 / 2 : ℝ), ‖x‖ ≤ 1 := by
    intro x hx
    have hx' : ‖x‖ ≤ (1 / 2 : ℝ) := by
      simp_all
    linarith
  have hrad : c * (1 / 2 : ℝ) = s := by dsimp [c]; ring
  have htargetUnit : ∀ x ∈ Metric.closedBall z (c * (1 / 2 : ℝ)), ‖x‖ ≤ 1 := by
    intro x hx
    have hx'' : ‖x - z‖ ≤ s := by
      have hx' : ‖x - z‖ ≤ c * (1 / 2 : ℝ) := by
        simpa [Metric.mem_closedBall, dist_eq_norm] using hx
      rw [hrad] at hx'
      exact hx'
    have hnorm : ‖x‖ ≤ ‖z‖ + s := by
      calc
        ‖x‖ = ‖(x - z) + z‖ := by congr 1; ring
        _ ≤ ‖x - z‖ + ‖z‖ := norm_add_le _ _
        _ ≤ s + ‖z‖ := add_le_add hx'' le_rfl
        _ = ‖z‖ + s := by ring
    exact le_trans hnorm (by nlinarith [hchart])
  have hscale := regularizedGMC_affine_openBall_moment_scale P X hX Xc hXc γ
    (a := z) (c := c) (R := (1 / 2 : ℝ)) (r := r) hc hc1
    (by norm_num) hsourceCut htargetCut hsourceUnit htargetUnit p
  have htargetParam : r - Real.log c = Real.log (1 / δ) := by
    dsimp [r]
    ring
  rw [htargetParam, hrad] at hscale
  have hbase := regularizedGMC_subunit_moment_le P X hX Xc hXc γ r
    (Metric.ball 0 (1 / 2)) Metric.isOpen_ball.measurableSet p hp hp1
  calc
    _ = ENNReal.ofReal (c ^
          (2 * p + γ ^ 2 * p / 2 - γ ^ 2 * p ^ 2 / 2)) *
        ∫⁻ ω, ENNReal.rpow
          (regularizedGMC P Xc γ r ω (Metric.ball 0 (1 / 2))) p ∂P := hscale
    _ ≤ ENNReal.ofReal (c ^
          (2 * p + γ ^ 2 * p / 2 - γ ^ 2 * p ^ 2 / 2)) *
        (1 + gmcReferenceMeasure (Metric.ball 0 (1 / 2))) :=
      by gcongr
    _ = _ := rfl

end DOZZ.Proofs
