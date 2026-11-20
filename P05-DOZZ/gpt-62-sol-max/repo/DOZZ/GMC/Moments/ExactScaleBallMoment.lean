/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.GMC.Moments.ExactScaleBallMass
public import DOZZ.MeasureTheory.PowerSums
public import DOZZ.GMC.Moments.PositiveExponent

/-! Moment transfer through the exact affine open-ball mass law. -/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped Distributions ENNReal NNReal

namespace DOZZ.Proofs

/-- The `p`th moment of the independent Gaussian scaling factor is exactly the power `c^ξ(p)`. -/
theorem gaussianScaleFactor_rpow_integral
    (γ c p : ℝ) (hc : 0 < c) (hc1 : c ≤ 1) :
    ∫⁻ w, ENNReal.rpow
      (ENNReal.ofReal (c ^ 2 * Real.exp (γ * w - γ ^ 2 / 2 * (-Real.log c)))) p
      ∂gaussianReal 0 ⟨-Real.log c,
        neg_nonneg.mpr (Real.log_nonpos hc.le hc1)⟩ =
      ENNReal.ofReal (c ^ (gmcScaleExponent γ p)) := by
  let σ  := -Real.log c
  let v : ℝ≥0 := ⟨σ, neg_nonneg.mpr (Real.log_nonpos hc.le hc1)⟩
  let G  := gaussianReal 0 v
  let d  := c ^ (2 * p) * Real.exp (-γ ^ 2 / 2 * p * σ)
  let t  := γ * p
  let scale  := fun w => c ^ 2 * Real.exp (γ * w - γ ^ 2 / 2 * σ)
  have hscale (w : ℝ) : 0 < scale w := by positivity
  have hpoint (w : ℝ) : ENNReal.rpow (ENNReal.ofReal (scale w)) p =
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
  have hExpInt : Integrable (fun w : ℝ => Real.exp (t * w)) G := by
    apply ProbabilityTheory.integrable_exp_mul_gaussianReal
  have hScaleInt : Integrable (fun w : ℝ => d * Real.exp (t * w)) G := by
    simpa [smul_eq_mul] using hExpInt.const_mul d
  have hExp : ∫ w, Real.exp (t * w) ∂G = Real.exp ((v : ℝ) * t ^ 2 / 2) := by
    have hmgf := congrFun
      (ProbabilityTheory.mgf_fun_id_gaussianReal (μ := 0) (v := v)) t
    simpa [ProbabilityTheory.mgf, G, mul_comm] using hmgf
  have hconst : d * Real.exp ((v : ℝ) * t ^ 2 / 2) =
      c ^ (gmcScaleExponent γ p) := by
    rw [Real.rpow_def_of_pos hc, show (v : ℝ) = -Real.log c by rfl]
    dsimp [d, t, v, σ]
    rw [Real.rpow_def_of_pos hc (2 * p), ← Real.exp_add, ← Real.exp_add]
    congr 1
    unfold gmcScaleExponent
    ring
  have hNN : 0 ≤ᵐ[G] fun w : ℝ => d * Real.exp (t * w) :=
    ae_of_all G fun w => mul_nonneg (by positivity) (Real.exp_nonneg _)
  calc
    _ = ∫⁻ w, ENNReal.ofReal (d * Real.exp (t * w)) ∂G := by
      apply lintegral_congr_ae
      exact ae_of_all G hpoint
    _ = ENNReal.ofReal (∫ w, d * Real.exp (t * w) ∂G) := by
      symm
      exact ofReal_integral_eq_lintegral_ofReal hScaleInt hNN
    _ = ENNReal.ofReal (d * ∫ w, Real.exp (t * w) ∂G) := by
      rw [integral_const_mul]
    _ = ENNReal.ofReal (c ^ (gmcScaleExponent γ p)) := by
      rw [hExp, hconst]
    _ = _ := by rfl

/-- The real-valued scaling law gives the extended moments of the original masses,
provided both masses are almost surely finite. This includes negative orders and zero masses. -/
theorem gaussianScaleFactor_massMoment_of_law
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (γ c p : ℝ) (hc : 0 < c) (hc1 : c ≤ 1) (f g : Ω → ℝ≥0∞)
    (hf : AEMeasurable f P) (hg : AEMeasurable g P)
    (hf' : ∀ᵐ ω ∂P, f ω ≠ ∞) (hg' : ∀ᵐ ω ∂P, g ω ≠ ∞)
    (hlaw : Measure.map (fun ω => (f ω).toReal) P =
      Measure.map (fun q : Ω × ℝ => c ^ 2 * Real.exp (γ * q.2 - γ ^ 2 / 2 * (-Real.log c)) *
        (g q.1).toReal) (P.prod (gaussianReal 0 ⟨-Real.log c,
          neg_nonneg.mpr (Real.log_nonpos hc.le hc1)⟩))) :
    (∫⁻ ω, f ω ^ p ∂P) = ENNReal.ofReal (c ^ (gmcScaleExponent γ p)) *
      ∫⁻ ω, g ω ^ p ∂P := by
  let G := gaussianReal 0 ⟨-Real.log c, neg_nonneg.mpr (Real.log_nonpos hc.le hc1)⟩
  have : IsProbabilityMeasure G := ProbabilityTheory.instIsProbabilityMeasureGaussianReal 0 _
  let W (w : ℝ) := c ^ 2 * Real.exp (γ * w - γ ^ 2 / 2 * (-Real.log c))
  have hW : Measurable W := by dsimp [W]; fun_prop
  let ψ (x : ℝ) := ENNReal.ofReal x ^ p
  have hψ : Measurable ψ := by dsimp [ψ]; fun_prop
  let L (ω : Ω) := (f ω).toReal
  let R (q : Ω × ℝ) := W q.2 * (g q.1).toReal
  have hL : AEMeasurable L P := ENNReal.measurable_toReal.comp_aemeasurable hf
  have hR : AEMeasurable R (P.prod G) := (hW.comp measurable_snd).aemeasurable.mul
    (ENNReal.measurable_toReal.comp_aemeasurable hg).comp_fst
  change Measure.map L P = Measure.map R (P.prod G) at hlaw
  have he : (∫⁻ ω, ψ (L ω) ∂P) = ∫⁻ q, ψ (R q) ∂P.prod G := by
    rw [← lintegral_map' hψ.aemeasurable hL, hlaw, lintegral_map' hψ.aemeasurable hR]
  calc
    _ = ∫⁻ ω, ψ (L ω) ∂P := by
      apply lintegral_congr_ae
      filter_upwards [hf'] with ω hw
      simp only [ψ, L, ENNReal.ofReal_toReal hw]
    _ = ∫⁻ q, ψ (R q) ∂P.prod G := he
    _ = ∫⁻ q : Ω × ℝ, g q.1 ^ p * (ENNReal.ofReal (W q.2)) ^ p ∂P.prod G := by
      apply lintegral_congr_ae
      filter_upwards [(Measure.quasiMeasurePreserving_fst (μ := P) (ν := G)).ae hg'] with q hq
      change ENNReal.ofReal (W q.2 * (g q.1).toReal) ^ p = _
      rw [ENNReal.ofReal_mul' ENNReal.toReal_nonneg, ENNReal.ofReal_toReal hq,
        ENNReal.mul_rpow_of_ne_top ENNReal.ofReal_ne_top hq, mul_comm]
    _ = _ := by
      change (∫⁻ q : Ω × ℝ, g q.1 ^ p * (ψ ∘ W) q.2 ∂P.prod G) = _
      rw [lintegral_prod_mul (hg.pow_const p) (hψ.comp hW).aemeasurable, mul_comm]
      congr 1
      exact gaussianScaleFactor_rpow_integral γ c p hc hc1

section
variable {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (X : Ω → Distr) (hX : IsEquatorGFF P X)
  (γ : ℝ) (hγ : 0 < γ) (hγ2 : γ < 2) (M : Ω → Measure ℂ) (hM : IsGMCOf P X γ M) {a : ℂ} {c R : ℝ}
  (hc : 0 < c) (hc1 : c ≤ 1) (hR : 0 < R) (hRsmall : R < 1) (hTsmall : ‖a‖ + c * R < 1) (p : ℝ)
include Ω X hX γ hγ hγ2 hM hc hc1 hR hRsmall hTsmall

/-- Exact scaling of an open-ball moment for every `IsGMCOf` version and every real order. At zero
mass the extended-power convention is retained, in particular zero to a negative power is
infinite. -/
theorem gmc_affine_openBall_moment_scale :
    gmcMassMoment P M (Metric.ball a (c * R)) p =
    ENNReal.ofReal (c ^ (gmcScaleExponent γ p)) *
      gmcMassMoment P M (Metric.ball 0 R) p := by
  have := hX.1
  refine gaussianScaleFactor_massMoment_of_law P γ c p hc hc1 _ _ ?_ ?_
    (ae_of_all _ fun ω => @measure_ne_top _ _ (M ω) (hM.1 ω) _)
    (ae_of_all _ fun ω => @measure_ne_top _ _ (M ω) (hM.1 ω) _) ?_
  · exact gmc_set_mass_aemeasurable_of_isGMCOf P X hX γ hγ hγ2 M hM _ Metric.isOpen_ball.measurableSet
  · exact gmc_set_mass_aemeasurable_of_isGMCOf P X hX γ hγ hγ2 M hM _ Metric.isOpen_ball.measurableSet
  · exact gmc_affine_openBall_mass_law P X hX γ hγ hγ2 M hM hc hc1 hR hRsmall hTsmall

/-- The exact scaling identity transports finiteness of every open-ball moment between an affine
subdisk and its reference disk, for positive, zero, or negative orders. -/
theorem gmc_affine_openBall_moment_finite_iff :
    gmcMassMoment P M (Metric.ball a (c * R)) p < ⊤ ↔
      gmcMassMoment P M (Metric.ball 0 R) p < ⊤ := by
  have hscale := gmc_affine_openBall_moment_scale P X hX γ hγ hγ2 M hM
    (a := a) (c := c) (R := R) hc hc1 hR hRsmall hTsmall p
  let ξ  := gmcScaleExponent γ p
  have hfactorPos  :=
    ENNReal.ofReal_pos.mpr (Real.rpow_pos_of_pos hc ξ)
  have hfactorTop : ENNReal.ofReal (c ^ ξ) < ⊤ := ENNReal.ofReal_lt_top
  rw [hscale, show gmcScaleExponent γ p = ξ by rfl]
  constructor
  · intro h
    exact ENNReal.lt_top_of_mul_ne_top_right (ne_of_lt h) (ne_of_gt hfactorPos)
  · intro h
    have hne  :=
      ENNReal.mul_ne_top (ne_of_lt hfactorTop) (ne_of_lt h)
    exact lt_top_iff_ne_top.mpr hne

end

end DOZZ.Proofs
