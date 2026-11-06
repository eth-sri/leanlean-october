module

public import HypoellipticAleksandrov.Parabolic.Dirichlet.CutoffGradientSpatialDifferenceQuotientL2
public import HypoellipticAleksandrov.Parabolic.Dirichlet.LocalizedSpatialDifferenceQuotientL2
public import HypoellipticAleksandrov.Parabolic.Dirichlet.LocalizedSpatialDifferenceQuotientWeakTest
public import HypoellipticAleksandrov.Parabolic.Dirichlet.WeakTestFunctionSobolevJet

/-!
# Localized quotient smooth graph compatibility

This module identifies each `L²` gradient coordinate of the localized spatial
difference quotient of a bundled smooth test with its two quotient-level
product-rule terms.
-/

 public section



open Filter
open scoped ENNReal

namespace HypoellipticAleksandrov.Parabolic.Dirichlet

/-- The smooth localized quotient has the expected coordinatewise `L²`
product-rule representative in the spatial Sobolev jet. -/
theorem localizedSpatialDifferenceQuotientWeakTest_gradientCoord_eq
    {d : ℕ} {Ω inner outer : PDE.VelocityRegion d} {K : ℝ}
    (hΩ : IsOpen Ω)
    (η : PDE.QuantitativeSmoothCutoff inner outer K)
    (k : Fin d) (h : ℝ) (φ : PDE.WeakTestFunction Ω)
    (hηΩ : tsupport η.toFun ⊆ Ω)
    (hηshift : Set.MapsTo
      (fun y  => y + h • PDE.basisVec k)
      (tsupport η.toFun) Ω)
    (j : Fin d) :
    PDE.hilbertVectorLpCoord Ω (2 ) j
      (gradientCLM hΩ
        (smoothCompactlySupportedH1HilbertGraphToH10HilbertGraph hΩ
          (localizedSpatialDifferenceQuotientWeakTest η k h φ hηΩ))) =
      cutoffGradientSpatialDifferenceQuotientL2 hΩ.measurableSet η j k h
        (valueCLM hΩ
          (smoothCompactlySupportedH1HilbertGraphToH10HilbertGraph hΩ φ)) +
      localizedSpatialDifferenceQuotientL2 hΩ.measurableSet η k h
        (PDE.hilbertVectorLpCoord Ω (2 ) j
          (gradientCLM hΩ
            (smoothCompactlySupportedH1HilbertGraphToH10HilbertGraph hΩ φ))) := by
  let sharedTerm_5d1132d87c := ((PDE.hilbertVectorLpCoord Ω (2 ) j
    (gradientCLM hΩ (smoothCompactlySupportedH1HilbertGraphToH10HilbertGraph hΩ φ))))
  apply MeasureTheory.Lp.ext
  have hleftCoord := PDE.coeFn_hilbertVectorLpCoord Ω _ j
    (gradientCLM hΩ
      (smoothCompactlySupportedH1HilbertGraphToH10HilbertGraph hΩ
        (localizedSpatialDifferenceQuotientWeakTest η k h φ hηΩ)))
  have hleftJet := ae_gradientCoordCLM_smoothCompactlySupportedH1HilbertGraph hΩ
    (localizedSpatialDifferenceQuotientWeakTest η k h φ hηΩ) j

  have hgradientCoord := PDE.coeFn_hilbertVectorLpCoord Ω _ j
    (gradientCLM hΩ
      (smoothCompactlySupportedH1HilbertGraphToH10HilbertGraph hΩ φ))


  have hfirst := cutoffGradientSpatialDifferenceQuotientL2_apply_ae_of_ae_eq
    hΩ.measurableSet η j k h
    _ φ (ae_valueCLM_smoothCompactlySupportedH1HilbertGraph hΩ φ) hηshift
  have hsecond := localizedSpatialDifferenceQuotientL2_apply_ae_of_ae_eq
    hΩ.measurableSet η k h
    sharedTerm_5d1132d87c
    (fun y => φ.partialDeriv j y) (hgradientCoord.trans (ae_gradientCoordCLM_smoothCompactlySupportedH1HilbertGraph hΩ φ j)) hηshift
  have hadd := MeasureTheory.Lp.coeFn_add
    (cutoffGradientSpatialDifferenceQuotientL2 hΩ.measurableSet η j k h
      (valueCLM hΩ
        (smoothCompactlySupportedH1HilbertGraphToH10HilbertGraph hΩ φ)))
    (localizedSpatialDifferenceQuotientL2 hΩ.measurableSet η k h
      sharedTerm_5d1132d87c )
  filter_upwards [hleftCoord, hleftJet, hfirst, hsecond, hadd] with y hleftCoord
      hleftJet hfirst hsecond hadd
  rw [hleftCoord, hleftJet,
    localizedSpatialDifferenceQuotientWeakTest_partialDeriv, hadd]
  simp only [Pi.add_apply]
  rw [hfirst, hsecond]
  rfl

end HypoellipticAleksandrov.Parabolic.Dirichlet
