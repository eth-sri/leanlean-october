module

public import RequestProject.PlanarTypes

public import RequestProject.PlanarGeometry

public import RequestProject.LocalConformalRegularPrincipal
public import RequestProject.CorrectedKernelSymm
public import RequestProject.ConormalNormalization
public import RequestProject.SobolevMultiplier

/-!
# The Fourier operator assembled from the genuine regular Neumann map

The definition uses the actual regular weak resolvent and the actual
corrected-kernel matrix. Its compact principal remainder is proved here.
Identification with the physical periodic boundary expression is a
separate mathematical statement, not an assumption of this file.
-/

@[expose] public section

open scoped ContDiff


noncomputable section

namespace PolyaNeumann

open Set Metric

private theorem normalizedAbs_symbol_sub_one  (hn : n ≠ 0) :
    normalizedInverseAbsSymbol n - 1 =
      ((sobWeight n ^ (-(1 : ℝ)) : ℝ) : ℂ) * normalizedInverseAbsSymbol n := by
  have hw  := (sobWeight_pos n).ne'
  have habs : |(n : ℝ)| ≠ 0 := abs_ne_zero.mpr (Int.cast_ne_zero.mpr hn)
  have hr : sobWeight n / |(n : ℝ)| - 1 =
      sobWeight n ^ (-(1 : ℝ)) * (sobWeight n / |(n : ℝ)|) := by
    rw [Real.rpow_neg (sobWeight_pos n).le, Real.rpow_one]
    grind only [sobWeight]
  simp  [normalizedInverseAbsSymbol, if_neg hn]
  exact_mod_cast hr

theorem normalizedInverseAbsOperator_sub_one_factorization :
    normalizedInverseAbsOperator - (1 : L2Z →L[ℂ] L2Z) =
      (sobolevSmoothing 1 zero_le_one).comp normalizedInverseAbsOperator -
        zeroModeProjection := by
  apply ContinuousLinearMap.ext
  intro b
  apply lp.ext
  funext n
  simp only [ContinuousLinearMap.sub_apply, ContinuousLinearMap.one_apply,
    ContinuousLinearMap.comp_apply, lp.coeFn_sub, Pi.sub_apply,
    normalizedInverseAbsOperator_apply, sobolevSmoothing, diagOp_apply,
    zeroModeProjection_apply]
  grind only [normalizedInverseAbsSymbol, normalizedAbs_symbol_sub_one]

theorem isCompactOperator_normalizedInverseAbsOperator_sub_one :
    IsCompactOperator (normalizedInverseAbsOperator - (1 : L2Z →L[ℂ] L2Z)) := by
  rw [normalizedInverseAbsOperator_sub_one_factorization]
  exact ((isCompactOperator_sobolevSmoothing zero_lt_one).comp_clm
    normalizedInverseAbsOperator).sub isCompactOperator_zeroModeProjection

def normalizedPeriodicRegularOperator {Ω : PlanarSet}
    (Q : NeumannH1 Ω →L[ℂ] L2Z) (E₀ E : ℝ)
    (W : ℝ → ComplexEnd Ell2)
    (hbase : Summable fun p => ‖correctedRemainderMatrix W 0 0 p‖ ^ 2) :
    L2Z →L[ℂ] L2Z :=
  (2 : ℂ) • (normalizedNeumannRegular Q E₀ E - normalizedInverseAbsOperator) +
    principalNormalized + hsMatrixOp (correctedRemainderMatrix W 0 0) hbase

theorem normalizedPeriodicRegularOperator_sub_four_posProj_compact
    {Ω : PlanarSet} (Q : NeumannH1 Ω →L[ℂ] L2Z) (E₀ E : ℝ)
    (W : ℝ → ComplexEnd Ell2)
    (hbase : Summable fun p => ‖correctedRemainderMatrix W 0 0 p‖ ^ 2)
    (hN : IsCompactOperator (normalizedNeumannRegular Q E₀ E - (1 : L2Z →L[ℂ] L2Z))) :
    IsCompactOperator (normalizedPeriodicRegularOperator Q E₀ E W hbase -
      (4 : ℂ) • posProj) := by
  have hdiff : IsCompactOperator (normalizedNeumannRegular Q E₀ E -
      normalizedInverseAbsOperator) := by
    have heq : normalizedNeumannRegular Q E₀ E - normalizedInverseAbsOperator =
        (normalizedNeumannRegular Q E₀ E - 1) - (normalizedInverseAbsOperator - 1) := by abel
    rw [heq]
    exact hN.sub isCompactOperator_normalizedInverseAbsOperator_sub_one
  have heq : normalizedPeriodicRegularOperator Q E₀ E W hbase - (4 : ℂ) • posProj =
      (2 : ℂ) • (normalizedNeumannRegular Q E₀ E - normalizedInverseAbsOperator) +
        (principalNormalized - (4 : ℂ) • posProj) +
          hsMatrixOp (correctedRemainderMatrix W 0 0) hbase := by
    unfold normalizedPeriodicRegularOperator
    abel
  rw [heq]
  exact ((hdiff.smul 2).add principal_normalized_sub_four_posProj_compact).add
    (isCompactOperator_hsMatrixOp _ hbase)

section PhysicalCoordinates

variable {R C } (hR : 1 < R) (F )
    (hFs : RealSmoothOnBall F R)
    (hb : Bornology.IsBounded (F '' unitDisk))
    (hL : IsLipschitzDomain (F '' unitDisk))
    (hhol : DifferentiableOn ℂ F unitDisk)
    (hinj : InjOn F unitDisk)
    (hC : DiskInverseJacobianBound F C)
    (e : OpenPartialHomeomorph ℂ ℂ) (he : (e : PlaneMap) = F)
    (hsource : closedUnitDisk ⊆ e.source)
    (hes : RealSmoothOn e.symm e.target)

include hb hhol hinj hC e he hsource hes in
theorem localConformal_normalizedPeriodicRegular_sub_four_posProj_compact
    {E₀ E : ℝ} (hE₀ : 0 ≤ E₀)
    (hunit : IsUnit (h1ComplementForm (F '' unitDisk) E₀ E))
    (W : ℝ → ComplexEnd Ell2)
    (hbase : Summable fun p => ‖correctedRemainderMatrix W 0 0 p‖ ^ 2) :
    IsCompactOperator (normalizedPeriodicRegularOperator
      (localConformalDiskHalfTrace hR F hFs hL) E₀ E W hbase - (4 : ℂ) • posProj) := normalizedPeriodicRegularOperator_sub_four_posProj_compact
    (localConformalDiskHalfTrace hR F hFs hL) E₀ E W hbase
    (isCompactOperator_localConformal_normalizedNeumannRegular_sub_one
      hR F hFs hb hL hhol hinj hC e he hsource hes hE₀ hunit)

end PhysicalCoordinates

end PolyaNeumann

end
