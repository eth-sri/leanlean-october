/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.GMC.Moments.ExactScaleBallMass

/-! Moment transfer through the exact affine open-ball mass law. -/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped Distributions ENNReal NNReal

namespace DOZZ.Proofs

/-- For a strictly positive finite real base, the extended-real power agrees with the real power.
This remains true for negative exponents, unlike the corresponding statement at zero. -/
private theorem ennreal_ofReal_rpow_of_pos {x p} (hx : 0 < x) :
    ENNReal.rpow (ENNReal.ofReal x) p = ENNReal.ofReal (x ^ p) := by
  apply (ENNReal.toReal_eq_toReal_iff' (ENNReal.rpow_ne_top_of_ne_zero (ne_of_gt (ENNReal.ofReal_pos.mpr hx)) ENNReal.ofReal_ne_top) ENNReal.ofReal_ne_top).1
  calc
    (ENNReal.rpow (ENNReal.ofReal x) p).toReal =
        (ENNReal.ofReal x).toReal ^ p := (ENNReal.toReal_rpow _ _).symm
    _ = x ^ p := by rw [ENNReal.toReal_ofReal hx.le]
    _ = (ENNReal.ofReal (x ^ p)).toReal := by
        rw [ENNReal.toReal_ofReal (Real.rpow_nonneg hx.le p)]

/-- The `p`th moment of the independent Gaussian scaling factor is exactly the power `c^ξ(p)`. -/
theorem gaussianScaleFactor_rpow_integral
    γ c p (hc : 0 < c) (hc1 : c ≤ 1) :
    ∫⁻ w, ENNReal.rpow
      (ENNReal.ofReal (c ^ 2 * Real.exp (γ * w - γ ^ 2 / 2 * (-Real.log c)))) p
      ∂gaussianReal 0 ⟨-Real.log c,
        neg_nonneg.mpr (Real.log_nonpos hc.le hc1)⟩ =
      ENNReal.ofReal (c ^ (2 * p + γ ^ 2 * p / 2 - γ ^ 2 * p ^ 2 / 2)) := by
  let σ : ℝ := -Real.log c
  let v : ℝ≥0 := ⟨σ, neg_nonneg.mpr (Real.log_nonpos hc.le hc1)⟩
  let G := gaussianReal 0 v
  let d := c ^ (2 * p) * Real.exp (-γ ^ 2 / 2 * p * σ)
  let t := γ * p
  let scale : ℝ → ℝ := fun w => c ^ 2 * Real.exp (γ * w - γ ^ 2 / 2 * σ)
  have hscale w : 0 < scale w := by positivity
  have hpoint w : ENNReal.rpow (ENNReal.ofReal (scale w)) p =
      ENNReal.ofReal (d * Real.exp (t * w)) := by
    rw [ennreal_ofReal_rpow_of_pos (hscale w)]
    have hpow : scale w ^ p = d * Real.exp (t * w) := by
      dsimp [scale, d, t, σ]
      rw [Real.mul_rpow (by positivity) (Real.exp_nonneg _),
        ← Real.rpow_natCast_mul hc.le 2 p,
        ← Real.exp_mul (γ * w - γ ^ 2 / 2 * (-Real.log c)) p,
        show (γ * w - γ ^ 2 / 2 * (-Real.log c)) * p =
          (-γ ^ 2 / 2 * p * (-Real.log c)) + (γ * p) * w by ring,
        Real.exp_add]
      ring_nf
    rw [hpow]
  have hconst : d * Real.exp ((v : ℝ) * t ^ 2 / 2) =
      c ^ (2 * p + γ ^ 2 * p / 2 - γ ^ 2 * p ^ 2 / 2) := by
    rw [Real.rpow_def_of_pos hc, show (v : ℝ) = -Real.log c by rfl]
    dsimp [d, t, v, σ]
    rw [Real.rpow_def_of_pos hc (2 * p), ← Real.exp_add, ← Real.exp_add]
    congr 1
    ring_nf
  calc
    _ = ∫⁻ w, ENNReal.ofReal (d * Real.exp (t * w)) ∂G := by
      apply lintegral_congr_ae
      exact ae_of_all G hpoint
    _ = ENNReal.ofReal (∫ w, d * Real.exp (t * w) ∂G) := by
      symm
      exact ofReal_integral_eq_lintegral_ofReal (by simpa [smul_eq_mul] using (show Integrable (fun w => Real.exp (t * w)) G by simpa [G, v, t] using ProbabilityTheory.integrable_exp_mul_gaussianReal (μ := 0) (v := v) t).const_mul d) (ae_of_all G fun w => mul_nonneg (by positivity) (Real.exp_nonneg _))
    _ = ENNReal.ofReal (d * ∫ w, Real.exp (t * w) ∂G) := by
      rw [integral_const_mul]
    _ = ENNReal.ofReal (c ^ (2 * p + γ ^ 2 * p / 2 - γ ^ 2 * p ^ 2 / 2)) := by
      rw [(show ∫ w, Real.exp (t * w) ∂G = Real.exp ((v : ℝ) * t ^ 2 / 2) by simpa [ProbabilityTheory.mgf, G, mul_comm] using (congrFun (ProbabilityTheory.mgf_fun_id_gaussianReal (μ := 0) (v := v)) t)), hconst]
    _ = _ := by rfl

/-- Exact scaling of an open-ball moment for every `IsGMCOf` version and every real order. At zero
mass the extended-power convention is retained, in particular zero to a negative power is
infinite. -/
theorem gmc_affine_openBall_moment_scale
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) X (hX : IsEquatorGFF P X) γ
    (hγ : 0 < γ) (hγ2 : γ < 2)
    (M : Ω → Measure ℂ) (hM : IsGMCOf P X γ M)
    {a} {c R} (hc : 0 < c) (hc1 : c ≤ 1)
    (hR : 0 < R) (hRsmall : R < 1) (hTsmall : ‖a‖ + c * R < 1)
    p :
    gmcMassMoment P M (Metric.ball a (c * R)) p =
    ENNReal.ofReal (c ^ (2 * p + γ ^ 2 * p / 2 - γ ^ 2 * p ^ 2 / 2)) *
      gmcMassMoment P M (Metric.ball 0 R) p := by
  classical
  let G := gaussianReal 0 ⟨-Real.log c,
    neg_nonneg.mpr (Real.log_nonpos hc.le hc1)⟩
  let : IsProbabilityMeasure P := hX.1
  have hG : IsProbabilityMeasure G := by
    simpa [G] using (ProbabilityTheory.instIsProbabilityMeasureGaussianReal 0
      ⟨-Real.log c, neg_nonneg.mpr (Real.log_nonpos hc.le hc1)⟩)
  let : IsProbabilityMeasure G := hG
  let : IsProbabilityMeasure (P.prod G) := inferInstance
  let scaleFactor : ℝ → ℝ := fun w =>
    c ^ 2 * Real.exp (γ * w - γ ^ 2 / 2 * (-Real.log c))
  let t : Ω → Fin 1 → ℝ := fun ω _ => (M ω (Metric.ball a (c * R))).toReal
  let s : Ω × ℝ → Fin 1 → ℝ := fun q _ =>
    scaleFactor q.2 * (M q.1 (Metric.ball 0 R)).toReal
  have hLaw := gmc_affine_openBall_mass_law P X hX γ hγ hγ2 M hM
    (a := a) (c := c) (R := R) hc hc1 hR hRsmall hTsmall
  change Measure.map t P = Measure.map s (P.prod G) at hLaw
  have htCoord : AEMeasurable
      (fun ω => (M ω (Metric.ball a (c * R))).toReal) P := ENNReal.measurable_toReal.comp_aemeasurable
      (gmc_set_mass_aemeasurable_of_isGMCOf P X hX γ hγ hγ2 M hM
        (Metric.ball a (c * R)) Metric.isOpen_ball.measurableSet)
  let ψ : (Fin 1 → ℝ) → ℝ≥0∞ := fun v => ENNReal.rpow (ENNReal.ofReal (v 0)) p
  have hψ : Measurable ψ := by
    dsimp [ψ]
    fun_prop
  have hleft : gmcMassMoment P M (Metric.ball a (c * R)) p =
      ∫⁻ v, ψ v ∂Measure.map t P := by
    rw [gmcMassMoment, lintegral_map' hψ.aemeasurable (aemeasurable_pi_iff.2
      (fun j => by simpa [t] using htCoord))]
    apply lintegral_congr_ae
    filter_upwards with ω
    let : IsFiniteMeasure (M ω) := hM.1 ω
    simp [ψ, t, ENNReal.ofReal_toReal (measure_ne_top (M ω) _)]
  have hprod :
      (∫⁻ q, ENNReal.rpow
          (ENNReal.ofReal (scaleFactor q.2 * (M q.1 (Metric.ball 0 R)).toReal)) p
          ∂P.prod G) =
        gmcMassMoment P M (Metric.ball 0 R) p *
          ∫⁻ w, ENNReal.rpow (ENNReal.ofReal (scaleFactor w)) p ∂G := by
    rw [show (fun q : Ω × ℝ =>
        ENNReal.rpow
          (ENNReal.ofReal (scaleFactor q.2 * (M q.1 (Metric.ball 0 R)).toReal)) p) =
        (fun q => ENNReal.rpow (M q.1 (Metric.ball 0 R)) p *
          ENNReal.rpow (ENNReal.ofReal (scaleFactor q.2)) p) by
      funext q
      let : IsFiniteMeasure (M q.1) := hM.1 q.1
      have hmassTop : M q.1 (Metric.ball 0 R) ≠ ∞ := measure_ne_top (M q.1) _
      rw [ENNReal.ofReal_mul' ENNReal.toReal_nonneg,
        ENNReal.ofReal_toReal hmassTop]
      simpa [mul_comm] using
        (ENNReal.mul_rpow_of_ne_top (x := ENNReal.ofReal (scaleFactor q.2))
          (y := M q.1 (Metric.ball 0 R)) ENNReal.ofReal_ne_top hmassTop p)]
    rw [lintegral_prod_mul (show AEMeasurable (fun ω => ENNReal.rpow (M ω (Metric.ball 0 R)) p) P by exact ENNReal.continuous_rpow_const.measurable.comp_aemeasurable (gmc_set_mass_aemeasurable_of_isGMCOf P X hX γ hγ hγ2 M hM (Metric.ball 0 R) Metric.isOpen_ball.measurableSet)) (show AEMeasurable (fun w => ENNReal.rpow (ENNReal.ofReal (scaleFactor w)) p) G by exact ENNReal.continuous_rpow_const.measurable.comp_aemeasurable (ENNReal.measurable_ofReal.comp_aemeasurable (show Measurable scaleFactor by dsimp [scaleFactor]; fun_prop).aemeasurable)), gmcMassMoment]
  calc
    gmcMassMoment P M (Metric.ball a (c * R)) p =
        ∫⁻ v, ψ v ∂Measure.map t P := hleft
    _ = ∫⁻ v, ψ v ∂Measure.map s (P.prod G) := (by rw [hLaw])
    _ = ∫⁻ q, ENNReal.rpow
        (ENNReal.ofReal (scaleFactor q.2 * (M q.1 (Metric.ball 0 R)).toReal)) p
        ∂P.prod G := (by rw [lintegral_map' hψ.aemeasurable (aemeasurable_pi_iff.2 (fun j => by simpa [s] using (show AEMeasurable (fun q : Ω × ℝ => scaleFactor q.2 * (M q.1 (Metric.ball 0 R)).toReal) (P.prod G) by change AEMeasurable (fun q : Ω × ℝ => scaleFactor q.2 * (M q.1 (Metric.ball 0 R)).toReal) (P.prod G); exact (show AEMeasurable (fun q : Ω × ℝ => scaleFactor q.2) (P.prod G) by exact (show Measurable scaleFactor by dsimp [scaleFactor]; fun_prop).comp_aemeasurable measurable_snd.aemeasurable).mul (by change AEMeasurable ((fun ω => (M ω (Metric.ball 0 R)).toReal) ∘ (fun q : Ω × ℝ => q.1)) (P.prod G); exact (show AEMeasurable (fun ω => (M ω (Metric.ball 0 R)).toReal) (Measure.map (fun q : Ω × ℝ => q.1) (P.prod G)) by rw [measurePreserving_fst.map_eq]; exact (ENNReal.measurable_toReal.comp_aemeasurable (gmc_set_mass_aemeasurable_of_isGMCOf P X hX γ hγ hγ2 M hM (Metric.ball 0 R) Metric.isOpen_ball.measurableSet))).comp_aemeasurable measurable_fst.aemeasurable))))])
    _ = gmcMassMoment P M (Metric.ball 0 R) p *
        ∫⁻ w, ENNReal.rpow (ENNReal.ofReal (scaleFactor w)) p ∂G := hprod
    _ = _ := by
      rw [gaussianScaleFactor_rpow_integral γ c p hc hc1]
      ac_rfl

/-- The exact scaling identity transports finiteness of every open-ball moment between an affine
subdisk and its reference disk, for positive, zero, or negative orders. -/
theorem gmc_affine_openBall_moment_finite_iff
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) X (hX : IsEquatorGFF P X) γ
    (hγ : 0 < γ) (hγ2 : γ < 2)
    (M : Ω → Measure ℂ) (hM : IsGMCOf P X γ M)
    {a} {c R} (hc : 0 < c) (hc1 : c ≤ 1)
    (hR : 0 < R) (hRsmall : R < 1) (hTsmall : ‖a‖ + c * R < 1)
    p :
    gmcMassMoment P M (Metric.ball a (c * R)) p < ⊤ ↔
      gmcMassMoment P M (Metric.ball 0 R) p < ⊤ := by
  let ξ : ℝ := 2 * p + γ ^ 2 * p / 2 - γ ^ 2 * p ^ 2 / 2
  rw [(gmc_affine_openBall_moment_scale P X hX γ hγ hγ2 M hM (a := a) (c := c) (R := R) hc hc1 hR hRsmall hTsmall p), show 2 * p + γ ^ 2 * p / 2 - γ ^ 2 * p ^ 2 / 2 = ξ by rfl]
  constructor
  · intro h
    exact ENNReal.lt_top_of_mul_ne_top_right (ne_of_lt h) (ne_of_gt (ENNReal.ofReal_pos.mpr (Real.rpow_pos_of_pos hc ξ)))
  · intro h
    exact lt_top_iff_ne_top.mpr (ENNReal.mul_ne_top (ne_of_lt (ENNReal.ofReal_lt_top : ENNReal.ofReal (c ^ ξ) < ⊤)) (ne_of_lt h))

end DOZZ.Proofs
