module

public import RequestProject.CircleAnalysisNotation

public import RequestProject.DiskCoordinates

public import RequestProject.PhysicalHardySupport
public import RequestProject.CutFourier
public import RequestProject.ArcLength
public import RequestProject.HardyPrimitiveTrace
public import RequestProject.PlanarNotation

/-!
# Weighted Fourier coefficients of the supplied physical circle trace

Real C⁴ regularity near the closed disk implies the actual averaged Fourier
coefficients of `conj γ'` belong to weighted ℓ¹ of order one, and those of
`γ - γ 0` belong to weighted ℓ¹ of order two.  The estimates follow from
integration by parts and the periodic derivative summability theorem in
`CutFourier`; neither constant speed nor exterior holomorphicity is required.

The centered trace retains its actual average coefficient.  Absolute Fourier
reconstruction agrees with the physical function at every real parameter.
Holomorphicity in the open disk is used only for the support assertion imported
from `PhysicalHardySupport`, not as a substitute for the weighted estimates.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

open scoped ContDiff

namespace PolyaNeumann

open MeasureTheory Set Metric
open scoped ComplexConjugate

/-- Periodic real C⁴ regularity gives the two weighted estimates needed for
the physical primitive multiplier and the centered boundary coordinate. -/
theorem periodic_contDiff_four_fourier_weights {f : ℝ → ℂ}
    (hf : ContDiff ℝ 4 f) (hp : Function.Periodic f anglePeriod) :
    IsWL1 1 (angleCoeff (deriv f)) ∧
      IsWL1 2 (angleCoeff f) := by
  have hf1  :=
    (show ContDiff ℝ (3 + 1) f from hf).deriv'
  have hf2  :=
    (show ContDiff ℝ (2 + 1) (deriv f) from hf1).deriv'
  have hf3  :=
    (show ContDiff ℝ (1 + 1) (deriv (deriv f)) from hf2).deriv'
  have d1  :=
    fun x => (hf.differentiable (by norm_num) x).hasDerivAt
  have d2  :=
    fun x => (hf1.differentiable (by norm_num) x).hasDerivAt
  have d3  :=
    fun x => (hf2.differentiable (by norm_num) x).hasDerivAt
  
  have hp1 := deriv_periodic hp
  have hp2 := deriv_periodic hp1
  have hp3 := deriv_periodic hp2
  have p0 := (hp 0).symm
  simp only [zero_add] at p0
  have p1 := (hp1 0).symm
  simp only [zero_add] at p1
  have p2 := (hp2 0).symm
  simp only [zero_add] at p2
  
  have hs1  :=
    summable_norm_fourierCoeffOn_deriv d1 d2 d3 hf3.continuous p0 p1 p2
  have hs2  :=
    summable_norm_fourierCoeffOn_deriv d2 d3 (fun x => (hf3.differentiable_one x).hasDerivAt) hf3.continuous_deriv_one p1 p2 (by
        simpa only [zero_add] using (hp3 0).symm)
  have e1 (n : ℤ)  :=
    fourierCoeffOn_deriv d1 hf1.continuous p0 n
  have e2 (n : ℤ)  :=
    fourierCoeffOn_deriv d2 hf2.continuous p1 n
  have hs0 : Summable (fun n => ‖fourierCoeffOn Real.two_pi_pos f n‖) := by
    refine (hs1.add ((hasSum_ite_eq 0
      ‖fourierCoeffOn Real.two_pi_pos f 0‖).summable)).of_nonneg_of_le
      (by norm_num) (fun n => ?_)
    by_cases hn : n = 0
    · subst n
      simp
    · simp [*]
      have hn' : 1 ≤ |(n : ℝ)| := by
        rw [← Int.cast_abs, ← Int.cast_one, Int.cast_le]
        exact Int.one_le_abs hn
      nlinarith [norm_nonneg (fourierCoeffOn Real.two_pi_pos f n)]
  constructor
  · 
    refine (hs1.add hs2).congr fun n => ?_
    simp [e2, norm_mul, Complex.norm_I, one_mul, Complex.norm_intCast, Real.rpow_one, sobWeight]
    ring
  · 
    refine Summable.of_nonneg_of_le
      (fun n => mul_nonneg (Real.rpow_nonneg (sobWeight_pos n).le _)
        (norm_nonneg _)) (fun n => ?_) ((hs0.mul_left 2).add (hs2.mul_left 2))
    rw [e2, e1]
    simp only [norm_mul, Complex.norm_I, one_mul, Complex.norm_intCast,
      Real.rpow_two, sobWeight]
    have hnonneg : 0 ≤ (|(n : ℝ)| - 1) ^ 2 *
        ‖fourierCoeffOn Real.two_pi_pos f n‖ :=
      mul_nonneg (sq_nonneg _) (norm_nonneg _)
    nlinarith

theorem physicalWeights_fourierCoeffOn_conj (g : ℝ → ℂ) (n : ℤ) :
    angleCoeff (fun θ => conj (g θ)) n =
      conj (angleCoeff g (-n)) := by
  rw [fourierCoeffOn_eq_integral, fourierCoeffOn_eq_integral]
  simp only [sub_zero, Complex.real_smul, map_mul, Complex.conj_ofReal]
  congr 1
  rw [← intervalIntegral_conj]
  simp

/-- Conjugation reflects the Fourier indices and preserves the weighted ℓ¹ norm. -/
theorem isWL1_fourierCoeffOn_conj {s : ℝ} {g : ℝ → ℂ}
    (hg : IsWL1 s (angleCoeff g)) :
    IsWL1 s (angleCoeff (fun θ => conj (g θ))) := by
  
  
  refine (hg.comp_injective
    (neg_injective)).congr fun n => ?_
  simp [physicalWeights_fourierCoeffOn_conj, sobWeight, abs_neg]

/-- Actual physical coefficients satisfy both weighted hypotheses.  Real
smoothness near the closure suffices; no boundary parametrization is assumed. -/
theorem physicalCircleTrace_fourier_weights_of_neighborhood
    {R : ℝ} (hR : 1 < R) (F : ℂ → ℂ)
    (hFs : ContDiffOn ℝ 4 F (ball (0 : ℂ) R)) :
    IsWL1 1 (angleCoeff
      (fun θ => conj (deriv (physicalCircleTrace F) θ))) ∧
      IsWL1 2 (angleCoeff
        (fun θ => physicalCircleTrace F θ - physicalCircleTrace F 0)) := by
  have hγ := contDiff_physicalCircleTrace_of_neighborhood hR F hFs
  have hp := physicalCircleTrace_periodic F
  refine ⟨isWL1_fourierCoeffOn_conj
    (periodic_contDiff_four_fourier_weights hγ hp).1, ?_⟩
  exact (periodic_contDiff_four_fourier_weights
    (hγ.sub contDiff_const) (hp.comp (fun z => z - physicalCircleTrace F 0))).2

/-- Smooth supplied coordinates give the same finite weighted hypotheses. -/
theorem physicalCircleTrace_fourier_weights_of_smooth_neighborhood (Φ : SmoothDiskMap) :
    IsWL1 1 (angleCoeff
      (fun θ => conj (deriv Φ.boundary θ))) ∧
      IsWL1 2 (angleCoeff
        (fun θ => Φ.boundary θ - Φ.boundary 0)) :=
  physicalCircleTrace_fourier_weights_of_neighborhood Φ.one_lt_radius Φ.map
    (Φ.smooth.of_le (WithTop.coe_le_coe.mpr le_top))

/-- Absolutely convergent averaged Fourier reconstruction of a continuous
periodic physical function, at every real parameter. -/
theorem hardyFourierTrace_fourierCoeffOn_of_periodic {f : ℝ → ℂ}
    (hf : Continuous f) (hp : Function.Periodic f anglePeriod)
    (hs : Summable (fun n => ‖angleCoeff f n‖)) (θ : ℝ) :
    hardyFourierTrace (angleCoeff f) θ = f θ := by
  let u := AddCircle.equivIco anglePeriod 0 θ
  have hu : (u : ℝ) = (θ : ParamCircle) :=
    (AddCircle.equivIco anglePeriod 0).left_inv _
  
  have huv  := calc
      _ = _ := (hp.lift_coe _).symm
      _ = _ := congrArg hp.lift hu
      _ = _ := hp.lift_coe θ
  
  have hsum := hasSum_fourierCoeffOn hf (by simpa only [zero_add] using (hp 0).symm) hs.of_norm (by
      simpa only [zero_add] using u.property)
  have hsum' := hsum
  simp only [← hardy_fourier_exp, hu, huv] at hsum'
  exact hsum'.tsum_eq

/-- Reconstruction of the actual conjugated velocity from its weighted data. -/
theorem hardyFourierTrace_physical_conj_deriv_of_neighborhood
    {R : ℝ} (hR : 1 < R) (F : ℂ → ℂ)
    (hFs : ContDiffOn ℝ 4 F (ball (0 : ℂ) R)) (θ : ℝ) :
    hardyFourierTrace (angleCoeff
      (fun s => conj (deriv (physicalCircleTrace F) s))) θ =
      conj (deriv (physicalCircleTrace F) θ) := by
  
  have hc  :=
    Complex.continuous_conj.comp ((contDiff_physicalCircleTrace_of_neighborhood hR F hFs).continuous_deriv (by norm_num))
  
  have hw := (physicalCircleTrace_fourier_weights_of_neighborhood hR F hFs).1
  have hs : Summable (fun n => ‖fourierCoeffOn Real.two_pi_pos
      (fun s => conj (deriv (physicalCircleTrace F) s)) n‖) := by
    have hw' := hw
    simp only [IsWL1, Real.rpow_one] at hw'
    exact hw'.of_nonneg_of_le (fun _ => norm_nonneg _) (fun n =>
      le_mul_of_one_le_left (norm_nonneg _) (one_le_sobWeight n))
  exact hardyFourierTrace_fourierCoeffOn_of_periodic hc ((deriv_periodic (physicalCircleTrace_periodic F)).comp conj) hs θ

end PolyaNeumann

end
