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

/-! Exact affine scaling for open-ball masses of the finite circle-cutoff chaos. -/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped Distributions ENNReal NNReal BoundedContinuousFunction

namespace DOZZ.Proofs

variable {Ω : Type*} [MeasurableSpace Ω]

/-- A finite-cutoff ball mass at scales no finer than its cutoff has the exact subunit scaling
bound obtained from the reference half-disk intensity. -/
theorem regularizedGMC_openBall_subunit_scale_bound
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
  classical
  let : IsProbabilityMeasure P := hX.1
  let c := 2 * s
  let r' := Real.log (1 / δ)
  let r := r' + Real.log c
  have hc : 0 < c := by positivity
  have hc1 : c ≤ 1 := by linarith
  have hrad : c * (1 / 2 : ℝ) = s := by dsimp [c]; ring
  have hrr : r - Real.log c = r' := add_sub_cancel_right _ _
  have hexp_r' : Real.exp (-r') = δ := by
    rw [Real.exp_neg, Real.exp_log (by positivity), one_div, inv_inv]
  have hsourceCut (x : {w : ℂ // w ∈ Metric.closedBall (0 : ℂ) (1 / 2)}) :
      ‖x.1‖ + Real.exp (-r) ≤ 1 := by
    have hx : ‖x.1‖ ≤ 1 / 2 := by simpa [Metric.mem_closedBall] using x.2
    have hδc : Real.exp (-r) = δ / c := by
      rw [show -r = -r' + -Real.log c by dsimp [r]; ring, Real.exp_add, hexp_r',
        Real.exp_neg, Real.exp_log hc, div_eq_mul_inv]
    rw [hδc]
    linarith [(div_le_iff₀ hc).2 (show δ ≤ 1 / 2 * c by dsimp [c]; linarith)]
  have htargetCut (x : {w : ℂ // w ∈ Metric.closedBall (0 : ℂ) (1 / 2)}) :
      ‖z + c • x.1‖ + Real.exp (-(r - Real.log c)) ≤ 1 := by
    have hx : ‖x.1‖ ≤ 1 / 2 := by simpa [Metric.mem_closedBall] using x.2
    have hnorm : ‖z + c • x.1‖ ≤ ‖z‖ + s :=
      (norm_add_le _ _).trans (by
        rw [norm_smul, Real.norm_eq_abs, abs_of_pos hc]
        dsimp [c] at *; linarith [mul_le_mul_of_nonneg_left hx hc.le])
    rw [hrr, hexp_r']; linarith
  have hsourceUnit (x : ℂ) (hx : x ∈ Metric.closedBall (0 : ℂ) (1 / 2)) : ‖x‖ ≤ 1 := by
    have : ‖x‖ ≤ 1 / 2 := by simpa [Metric.mem_closedBall] using hx
    linarith
  have htargetUnit (x : ℂ) (hx : x ∈ Metric.closedBall z (c * (1 / 2))) : ‖x‖ ≤ 1 := by
    rw [hrad, Metric.mem_closedBall, dist_eq_norm] at hx
    linarith [norm_sub_norm_le x z]
  let G := gaussianReal 0 ⟨-Real.log c, neg_nonneg.mpr (Real.log_nonpos hc.le hc1)⟩
  let : IsProbabilityMeasure G :=
    ProbabilityTheory.instIsProbabilityMeasureGaussianReal 0 _
  let S : ℝ → ℝ := fun w => c ^ 2 * Real.exp (γ * w - γ ^ 2 / 2 * (-Real.log c))
  have hSm : Measurable S := by dsimp [S]; fun_prop
  let tMass : Ω → ℝ≥0∞ := fun ω => regularizedGMC P Xc γ (r - Real.log c) ω (Metric.ball z (c * (1 / 2)))
  let sMass : Ω → ℝ≥0∞ := fun ω => regularizedGMC P Xc γ r ω (Metric.ball 0 (1 / 2))
  have htMassM := regularizedGMC_mass_aemeasurable P X hX Xc hXc γ (r - Real.log c)
    (Metric.ball z (c * (1 / 2))) Metric.isOpen_ball.measurableSet
  have hsMassM := regularizedGMC_mass_aemeasurable P X hX Xc hXc γ r
    (Metric.ball 0 (1 / 2)) Metric.isOpen_ball.measurableSet
  let tLim : Ω → Fin 1 → ℝ := fun ω _ => (tMass ω).toReal
  let sLim : Ω × ℝ → Fin 1 → ℝ := fun q _ => S q.2 * (sMass q.1).toReal
  have htLimM : AEMeasurable tLim P :=
    aemeasurable_pi_iff.2 fun _ => ENNReal.measurable_toReal.comp_aemeasurable htMassM
  have hsLimM : AEMeasurable sLim (P.prod G) :=
    aemeasurable_pi_iff.2 fun _ => (hSm.comp measurable_snd).aemeasurable.mul
      ((ENNReal.measurable_toReal.comp_aemeasurable hsMassM).comp_quasiMeasurePreserving
        Measure.quasiMeasurePreserving_fst)
  have hvecLaw : Measure.map tLim P = Measure.map sLim (P.prod G) := by
    let f : ℕ → BoundedContinuousFunction ℂ ℝ := openBallAffineApprox z c (1 / 2)
    let g : ℕ → BoundedContinuousFunction ℂ ℝ := openBallApprox 0 (1 / 2)
    have hfSupp (n : ℕ) := openBallAffineApprox_tsupport_subset (a := z) (R := 1 / 2) hc n
    have htargetMeas (n : ℕ) := regularizedGMC_test_integral_aemeasurable P X hX Xc hXc γ
      (r - Real.log c) _ Metric.isClosed_closedBall.measurableSet htargetUnit (f n)
      (f n).continuous.measurable fun x hx =>
        boundedContinuousFunction_eq_zero_off_tsupport_subset (f n) _ (hfSupp n) x hx
    have hsourceMeas (n : ℕ) := regularizedGMC_test_integral_aemeasurable P X hX Xc hXc γ r _
      Metric.isClosed_closedBall.measurableSet hsourceUnit (g n) (g n).continuous.measurable
      fun x hx => boundedContinuousFunction_eq_zero_off_tsupport_subset (g n) _
        (openBallApprox_tsupport_subset 0 (1 / 2) n) x hx
    have htargetConv : TendstoInMeasure P
        (fun n ω => ∫ x, f n x ∂regularizedGMC P Xc γ (r - Real.log c) ω) atTop
        (fun ω => (tMass ω).toReal) :=
      tendstoInMeasure_of_tendsto_ae (fun n => (htargetMeas n).aestronglyMeasurable)
        ((regularizedGMC_finite_ae P X hX Xc hXc γ (r - Real.log c)).mono fun ω hω => by
          let : IsFiniteMeasure (regularizedGMC P Xc γ (r - Real.log c) ω) := hω
          simpa [f, tMass, Measure.real_def] using
            openBallAffineApprox_integral_tendsto hc (regularizedGMC P Xc γ (r - Real.log c) ω))
    have hsourceConv : TendstoInMeasure P
        (fun n ω => ∫ x, g n x ∂regularizedGMC P Xc γ r ω) atTop
        (fun ω => (sMass ω).toReal) :=
      tendstoInMeasure_of_tendsto_ae (fun n => (hsourceMeas n).aestronglyMeasurable)
        ((regularizedGMC_finite_ae P X hX Xc hXc γ r).mono fun ω hω => by
          let : IsFiniteMeasure (regularizedGMC P Xc γ r ω) := hω
          simpa [g, sMass, Measure.real_def] using
            openBallApprox_integral_tendsto 0 (1 / 2) (regularizedGMC P Xc γ r ω))
    exact gmc_limit_test_vector_law
      (fun n ω (_ : Fin 1) => ∫ x, f n x ∂regularizedGMC P Xc γ (r - Real.log c) ω)
      (fun n (q : Ω × ℝ) (_ : Fin 1) => S q.2 * ∫ x, g n x ∂regularizedGMC P Xc γ r q.1)
      tLim sLim
      (fun n => aemeasurable_pi_iff.2 fun _ => htargetMeas n)
      (fun n => aemeasurable_pi_iff.2 fun _ => (hSm.comp measurable_snd).aemeasurable.mul
        ((hsourceMeas n).comp_quasiMeasurePreserving Measure.quasiMeasurePreserving_fst))
      htLimM hsLimM
      (fun n => by
        have h := regularizedGMC_affine_cutoff_test_vector_law P X hX Xc hXc γ
          (a := z) (c := c) (R := 1 / 2) (r := r) hc hc1 (by norm_num) hsourceCut htargetCut
          hsourceUnit htargetUnit (fun _ : Fin 1 => f n)
          (fun _ x => (openBallApproxFun_bounds 0 (1 / 2) n _).1) (fun _ => hfSupp n)
        convert h using 2; ext q j; dsimp only [S]
        rw [integral_congr_ae (ae_of_all _ (openBallAffineApprox_comp_affine z c (1 / 2) hc.ne' n))])
      (fun _ => htargetConv)
      (fun _ => tendstoInMeasure_mul_snd_of_tendstoInMeasure
        (fun n ω => ∫ x, g n x ∂regularizedGMC P Xc γ r ω)
        (fun ω => (sMass ω).toReal) S hSm hsourceConv)
  let ψ : (Fin 1 → ℝ) → ℝ≥0∞ := fun v => (ENNReal.ofReal (v 0)) ^ p
  have hψ : Measurable ψ := by dsimp [ψ]; fun_prop
  have hintEq := congrArg (fun μ => ∫⁻ v, ψ v ∂μ) hvecLaw
  rw [lintegral_map' hψ.aemeasurable htLimM, lintegral_map' hψ.aemeasurable hsLimM] at hintEq
  have hL : (∫⁻ ω, ψ (tLim ω) ∂P) = ∫⁻ ω, tMass ω ^ p ∂P :=
    lintegral_congr_ae ((regularizedGMC_finite_ae P X hX Xc hXc γ (r - Real.log c)).mono
      fun ω hω => by
        let : IsFiniteMeasure _ := hω
        dsimp [ψ, tLim]; rw [ENNReal.ofReal_toReal (measure_ne_top _ _)])
  have hR : (∫⁻ q, ψ (sLim q) ∂P.prod G) =
      (∫⁻ ω, sMass ω ^ p ∂P) * ∫⁻ w, (ENNReal.ofReal (S w)) ^ p ∂G := by
    refine (lintegral_congr_ae ((Measure.quasiMeasurePreserving_fst (μ := P) (ν := G)).ae
      (regularizedGMC_finite_ae P X hX Xc hXc γ r) |>.mono fun q hq => ?_)).trans
      (lintegral_prod_mul (hsMassM.pow_const p) ((ENNReal.measurable_ofReal.comp hSm).pow_const p).aemeasurable)
    let : IsFiniteMeasure _ := hq
    dsimp [ψ, sLim]
    rw [ENNReal.ofReal_mul' ENNReal.toReal_nonneg, ENNReal.ofReal_toReal (measure_ne_top _ _),
      ENNReal.mul_rpow_of_ne_top ENNReal.ofReal_ne_top (measure_ne_top _ _), mul_comm]
  rw [hL, hR] at hintEq
  simp only [← ENNReal.rpow_eq_pow, S, G] at hintEq
  rw [gaussianScaleFactor_rpow_integral γ c p hc hc1, mul_comm] at hintEq
  simp only [tMass, sMass, hrr, hrad] at hintEq
  rw [hintEq]
  exact mul_le_mul_right (regularizedGMC_subunit_moment_le P X hX Xc hXc γ r
    (Metric.ball 0 (1 / 2)) Metric.isOpen_ball.measurableSet p hp hp1) _

end DOZZ.Proofs
