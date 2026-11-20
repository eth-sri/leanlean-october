module

public import RequestProject.DiskCoordinates

public import RequestProject.LocalConformalRegularPrincipal
public import RequestProject.CorrectedKernelSymm
public import RequestProject.ConormalNormalization
public import RequestProject.SobolevMultiplier
public import RequestProject.PlanarNotation

/-!
# The Fourier operator assembled from the genuine regular Neumann map

The definition uses the actual regular weak resolvent and the actual
corrected-kernel matrix. Its compact principal remainder is proved here.
Identification with the physical periodic boundary expression is a
separate mathematical statement, not an assumption of this file.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

open scoped ContDiff

namespace PolyaNeumann

open Set Metric

private theorem normalizedAbs_symbol_sub_one {n : ℤ} (hn : n ≠ 0) :
    normalizedInverseAbsSymbol n - 1 =
      ((sobWeight n ^ (-(1 : ℝ)) : ℝ) : ℂ) * normalizedInverseAbsSymbol n := by
  have hw  := (sobWeight_pos n).ne'
  have habs : |(n : ℝ)| ≠ 0 := (by positivity)
  have hr : sobWeight n / |(n : ℝ)| - 1 =
      sobWeight n ^ (-(1 : ℝ)) * (sobWeight n / |(n : ℝ)|) := by
    rw [Real.rpow_neg (sobWeight_pos n).le, Real.rpow_one]
    field_simp [hw, habs]
    simp [sobWeight]
  simp only [normalizedInverseAbsSymbol, if_neg hn]
  exact_mod_cast hr

theorem normalizedInverseAbsOperator_sub_one_factorization :
    normalizedInverseAbsOperator - (1 : FourierOp) =
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
  by_cases hn : n = 0
  · subst n
    simp [normalizedInverseAbsSymbol]
  · simp [if_neg hn, zero_mul, sub_zero]
    calc
      _ = (normalizedInverseAbsSymbol n - 1) * b n := by ring
      _ = _ := by rw [normalizedAbs_symbol_sub_one hn]; ring

theorem isCompactOperator_normalizedInverseAbsOperator_sub_one :
    IsCompactOperator (normalizedInverseAbsOperator - (1 : FourierOp)) := by
  rw [normalizedInverseAbsOperator_sub_one_factorization]
  exact ((isCompactOperator_sobolevSmoothing zero_lt_one).comp_clm
    normalizedInverseAbsOperator).sub isCompactOperator_zeroModeProjection

def normalizedPeriodicRegularOperator {Ω : Set ℂ}
    (Q : NeumannH1 Ω →L[ℂ] L2Z) (E₀ E : ℝ)
    (W : TransportPath)
    (hbase : Summable fun p => ‖correctedRemainderMatrix W 0 0 p‖ ^ 2) :
    FourierOp :=
  (2 : ℂ) • (normalizedNeumannRegular Q E₀ E - normalizedInverseAbsOperator) +
    principalNormalized + hsMatrixOp (correctedRemainderMatrix W 0 0) hbase

theorem normalizedPeriodicRegularOperator_sub_four_posProj_compact
    {Ω : Set ℂ} (Q : NeumannH1 Ω →L[ℂ] L2Z) (E₀ E : ℝ)
    (W : TransportPath)
    (hbase : Summable fun p => ‖correctedRemainderMatrix W 0 0 p‖ ^ 2)
    (hN : IsCompactOperator (normalizedNeumannRegular Q E₀ E - (1 : FourierOp))) :
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

theorem localConformal_normalizedPeriodicRegular_sub_four_posProj_compact (Φ : ConformalDiskMap)
    (e : OpenPartialHomeomorph ℂ ℂ) (he : (e : ℂ → ℂ) = Φ.map) (hsource : closedDisk ⊆ e.source)
    (hes : ContDiffOn ℝ ∞ e.symm e.target) {E₀ E : ℝ} (hE₀ : 0 ≤ E₀)
    (hunit : IsUnit (h1ComplementForm Φ.domain E₀ E)) (W : TransportPath)
    (hbase : Summable fun p => ‖correctedRemainderMatrix W 0 0 p‖ ^ 2) :
    IsCompactOperator (normalizedPeriodicRegularOperator
      (Φ.pulledBackHalfTrace Φ.lipschitzDomain) E₀ E W hbase - (4 : ℂ) • posProj) := normalizedPeriodicRegularOperator_sub_four_posProj_compact
    (Φ.pulledBackHalfTrace Φ.lipschitzDomain) E₀ E W hbase
    (isCompactOperator_localConformal_normalizedNeumannRegular_sub_one
      Φ e he hsource hes hE₀ hunit)

end PhysicalCoordinates

end PolyaNeumann

end
