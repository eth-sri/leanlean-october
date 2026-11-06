module

public import HypoellipticAleksandrov.Parabolic.SpatialDifferenceQuotientSmoothL2
public import HypoellipticAleksandrov.Parabolic.Dirichlet.LocalizedSpatialDifferenceQuotientL2
public import HypoellipticAleksandrov.Parabolic.Dirichlet.WeakTestFunctionSobolevJet
public import PDEFoundation.Sobolev.W1p.GraphEnergy
public import PDEFoundation.Calculus.RegularityOrder


/-!
# Sharp localized value bound on smooth Dirichlet tests

The global smooth difference-quotient estimate descends to the restricted
value class of an actual compactly supported smooth Dirichlet test without a
step-size collar assumption.
-/

 public section



open MeasureTheory
open scoped ENNReal

namespace HypoellipticAleksandrov.Parabolic.Dirichlet

variable {d : ℕ}

private theorem zeroExtend_value_eq_smoothWeakTest_ae
     {Ω : PDE.VelocityRegion d} (hΩ : IsOpen Ω)
    (φ : PDE.WeakTestFunction Ω) :
    ⇑(MeasureTheory.Lp.zeroExtendLinearIsometry hΩ.measurableSet
      (valueCLM hΩ
        (smoothCompactlySupportedH1HilbertGraphToH10HilbertGraph hΩ φ))) =ᵐ[volume] φ := by
  let f : PDE.ScalarLp Ω (2 ) := valueCLM hΩ
    (smoothCompactlySupportedH1HilbertGraphToH10HilbertGraph hΩ φ)
  have hvalue : ⇑f =ᵐ[PDE.volumeOn Ω] φ := ae_valueCLM_smoothCompactlySupportedH1HilbertGraph hΩ φ
  have hzero := MeasureTheory.Lp.coeFn_zeroExtendLinearIsometry hΩ.measurableSet f

  filter_upwards [hzero, (ae_imp_of_ae_restrict hvalue)] with y hzero hvalue
  rw [hzero]
  by_cases hy : y ∈ Ω
  · rw [Set.indicator_of_mem hy]
    exact hvalue hy
  · rw [Set.indicator_of_notMem hy]

    exact (image_eq_zero_of_notMem_tsupport (fun hsupport => hy (φ.tsupport_subset hsupport))).symm

private theorem localizedSpatialDifferenceQuotientL2_apply_smooth_ae
     {Ω inner outer : PDE.VelocityRegion d} {K : ℝ}
    (hΩ : IsOpen Ω) (η : PDE.QuantitativeSmoothCutoff inner outer K)
    (k : Fin d) (h : ℝ) (φ : PDE.WeakTestFunction Ω) :
    ⇑(localizedSpatialDifferenceQuotientL2 hΩ.measurableSet η k h
      (valueCLM hΩ
        (smoothCompactlySupportedH1HilbertGraphToH10HilbertGraph hΩ φ))) =ᵐ[PDE.volumeOn Ω]
      localizedSpatialDifferenceQuotient η k h φ := by
  let f : PDE.ScalarLp Ω (2 ) := valueCLM hΩ
    (smoothCompactlySupportedH1HilbertGraphToH10HilbertGraph hΩ φ)
  have hambient : ⇑(MeasureTheory.Lp.zeroExtendLinearIsometry hΩ.measurableSet f) =ᵐ[volume] φ := by
    exact zeroExtend_value_eq_smoothWeakTest_ae hΩ φ
  have hlocal := localizedSpatialDifferenceQuotientL2_apply_ae hΩ.measurableSet η k h f
  have hshifted := (measurePreserving_add_right (volume : Measure (PDE.Vec d))
    (h • PDE.basisVec k)).quasiMeasurePreserving.ae hambient
  filter_upwards [hlocal, ae_restrict_of_ae hambient,
    ae_restrict_of_ae hshifted] with y hlocal hambient hshifted
  rw [hlocal]
  simp only [localizedSpatialDifferenceQuotient_apply]
  rw [hambient, hshifted]

private theorem integrable_sq_smoothWeakTest_differenceQuotient
     {Ω : PDE.VelocityRegion d} (φ : PDE.WeakTestFunction Ω)
    (k : Fin d) (h : ℝ) :
    Integrable (fun y => ((φ (y + h • PDE.basisVec k) - φ y) / h) ^ 2)
      (volume ) := by
  let z  := h • PDE.basisVec k

  have htranslatesupport : HasCompactSupport (fun y  => φ (y + z)) := by

    exact (φ.hasCompactSupport.comp_homeomorph (Homeomorph.addRight z))


  have hqcontinuous : Continuous (fun y : PDE.Vec d => ((φ (y + z) - φ y) / h) ^ 2) :=
    by simpa only [div_eq_mul_inv, Pi.pow_def, Pi.mul_def] using
      ((show Continuous (fun y  => φ (y + z) - φ y) from (φ.contDiff.continuous.comp (Homeomorph.addRight z).continuous).sub φ.contDiff.continuous).mul continuous_const).pow 2
  have hqsupport : HasCompactSupport (fun y : PDE.Vec d => ((φ (y + z) - φ y) / h) ^ 2) :=
    (show HasCompactSupport (fun y  => φ (y + z) - φ y) by
        exact htranslatesupport.sub φ.hasCompactSupport).comp_left (g := fun x : ℝ => (x / h) ^ 2) (by simp)
  simpa only [z] using hqcontinuous.integrable_of_hasCompactSupport hqsupport

variable {inner outer : PDE.VelocityRegion d} {K : ℝ} (η : PDE.QuantitativeSmoothCutoff inner outer K) (f : PDE.ScalarField d)

private theorem integrable_sq_localizedSpatialDifferenceQuotient_smoothWeakTest
      (hf : ContDiff ℝ PDE.smoothOrder f)
    (k : Fin d) (h : ℝ) :
    Integrable (fun y => localizedSpatialDifferenceQuotient η k h f y ^ 2)
      (volume ) := by


  have hsupp : HasCompactSupport (((fun y => localizedSpatialDifferenceQuotient η k h f y ^ 2))) :=
    (localizedSpatialDifferenceQuotient_hasCompactSupport η k h f).comp_left
      (g := fun x : ℝ => x ^ 2) (by norm_num)
  exact ((ContDiff.localizedSpatialDifferenceQuotient hf η k h).continuous.pow 2).integrable_of_hasCompactSupport hsupp

private theorem sq_localizedSpatialDifferenceQuotient_le_sq_differenceQuotient
      (y : PDE.Vec d) (k : Fin d) (h : ℝ) :
    localizedSpatialDifferenceQuotient η k h f y ^ 2 ≤
      ((f (y + h • PDE.basisVec k) - f y) / h) ^ 2 := by
  let sharedTerm_f2bdaba179 := ((f (y + h • PDE.basisVec k) - f y) / h)
  rw [localizedSpatialDifferenceQuotient_apply]



  calc
    (η.toFun y * (sharedTerm_f2bdaba179)) ^ 2 =
        η.toFun y ^ 2 * (sharedTerm_f2bdaba179) ^ 2 := by ring
    _ ≤ (1 : ℝ) ^ 2 * (sharedTerm_f2bdaba179) ^ 2 :=
      mul_le_mul_of_nonneg_right ((sq_le_sq₀ (η.nonneg y) zero_le_one).mpr (η.le_one y)) (sq_nonneg _)
    _ = (sharedTerm_f2bdaba179) ^ 2 := by norm_num

variable {Ω : PDE.VelocityRegion d}

private theorem integral_sq_classicalGradient_eq_restrict

    (φ : PDE.WeakTestFunction Ω) :
    (∫ y, PDE.vecEuclideanNorm (PDE.classicalGradient φ y) ^ 2) =
      ∫ y, PDE.vecEuclideanNorm (PDE.classicalGradient φ y) ^ 2 ∂PDE.volumeOn Ω := by
  rw [← MeasureTheory.setIntegral_univ]
  rw [MeasureTheory.setIntegral_eq_of_subset_of_forall_diff_eq_zero MeasurableSet.univ
    (Set.subset_univ Ω)]
  intro y hy

  unfold PDE.classicalGradient

  rw [(fderiv_of_notMem_tsupport ℝ (fun hsupport => hy.2 (φ.tsupport_subset hsupport)))]
  simp [PDE.vecEuclideanNorm, PDE.vecNormSq, PDE.vecDot]

private theorem ae_norm_gradientCLM_smoothWeakTest_eq_classicalGradient
      (hΩ : IsOpen Ω)
    (φ : PDE.WeakTestFunction Ω) :
    (fun y => ‖gradientCLM hΩ
      (smoothCompactlySupportedH1HilbertGraphToH10HilbertGraph hΩ φ) y‖)
      =ᵐ[PDE.volumeOn Ω]
      fun y => PDE.vecEuclideanNorm (PDE.classicalGradient φ y) := by
  have hcoords : ∀ᵐ y : PDE.Vec d ∂PDE.volumeOn Ω, ∀ j : Fin d,
      gradientCLM hΩ
        (smoothCompactlySupportedH1HilbertGraphToH10HilbertGraph hΩ φ) y j =
        φ.partialDeriv j y := by
    apply ae_all_iff.mpr
    intro j
    exact ae_gradientCoordCLM_smoothCompactlySupportedH1HilbertGraph hΩ φ j
  filter_upwards [hcoords] with y hcoords
  have hvec : gradientCLM hΩ
      (smoothCompactlySupportedH1HilbertGraphToH10HilbertGraph hΩ φ) y =
      PDE.toHilbertVecField (PDE.classicalGradient φ) y := by
    apply (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin d => ℝ)).injective
    ext j
    exact hcoords j
  rw [hvec]
  exact PDE.norm_toHilbertVecField_apply _ _

/-- The localized quotient of an actual smooth zero-boundary test is
controlled by its weak-gradient `L²` norm. -/
theorem norm_localizedSpatialDifferenceQuotientL2_apply_smooth_le_gradient
     {Ω inner outer : PDE.VelocityRegion d} {K : ℝ}
    (hΩ : IsOpen Ω)
    (η : PDE.QuantitativeSmoothCutoff inner outer K)
    (k : Fin d) (h : ℝ) (φ : PDE.WeakTestFunction Ω) :
    ‖localizedSpatialDifferenceQuotientL2 hΩ.measurableSet η k h
        (valueCLM hΩ
          (smoothCompactlySupportedH1HilbertGraphToH10HilbertGraph hΩ φ))‖ ≤
      ‖gradientCLM hΩ
        (smoothCompactlySupportedH1HilbertGraphToH10HilbertGraph hΩ φ)‖ := ((sq_le_sq₀
      (norm_nonneg
        ((localizedSpatialDifferenceQuotientL2 (IsOpen.measurableSet hΩ) η k h)
          ((valueCLM hΩ) (smoothCompactlySupportedH1HilbertGraphToH10HilbertGraph hΩ φ))))
      (norm_nonneg ((gradientCLM hΩ) (smoothCompactlySupportedH1HilbertGraphToH10HilbertGraph hΩ φ)))).mp
  (Trans.trans
    (Trans.trans
      (Trans.trans
        (Trans.trans
          (Eq.symm
            (PDE.integral_sq_eq_sq_norm_of_ae_eq
              ((localizedSpatialDifferenceQuotientL2 (IsOpen.measurableSet hΩ) η k h)
                ((valueCLM hΩ) (smoothCompactlySupportedH1HilbertGraphToH10HilbertGraph hΩ φ)))
              (localizedSpatialDifferenceQuotient η k h φ.toFun)
              (id (localizedSpatialDifferenceQuotientL2_apply_smooth_ae hΩ η k h φ))))
          (Trans.trans
            (integral_mono_ae
              (Integrable.restrict
                (integrable_sq_localizedSpatialDifferenceQuotient_smoothWeakTest η φ.toFun φ.contDiff k h))
              (Integrable.restrict (integrable_sq_smoothWeakTest_differenceQuotient φ k h))
              (Filter.Eventually.of_forall fun y =>
                sq_localizedSpatialDifferenceQuotient_le_sq_differenceQuotient η φ.toFun y k h))
            (setIntegral_le_integral (integrable_sq_smoothWeakTest_differenceQuotient φ k h)
              (Filter.Eventually.of_forall fun y => sq_nonneg ((φ.toFun (y + h • PDE.basisVec k) - φ.toFun y) / h)))))
        (integral_sq_spatialDifferenceQuotient_le_integral_sq_classicalGradient φ.toFun φ.contDiff φ.hasCompactSupport k
          h))
      (integral_sq_classicalGradient_eq_restrict φ))
    (PDE.integral_norm_sq_eq_sq_norm_of_ae_eq_hilbert
      ((gradientCLM hΩ) (smoothCompactlySupportedH1HilbertGraphToH10HilbertGraph hΩ φ))
      (fun y => PDE.vecEuclideanNorm (PDE.classicalGradient φ.toFun y))
      (id (ae_norm_gradientCLM_smoothWeakTest_eq_classicalGradient hΩ φ)))))

end HypoellipticAleksandrov.Parabolic.Dirichlet
