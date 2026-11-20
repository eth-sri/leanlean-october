module

public import HypoellipticAleksandrov.Parabolic.Dirichlet.LocalizedSpatialDifferenceQuotientSmoothCommutator
public import HypoellipticAleksandrov.Parabolic.Dirichlet.CompactlySupportedSpatialL2
public import HypoellipticAleksandrov.Parabolic.Dirichlet.ReverseTimeSpatialFormOperatorBase
public import HypoellipticAleksandrov.Parabolic.Dirichlet.ReverseTimeSourceBochner
public import HypoellipticAleksandrov.Parabolic.Dirichlet.TimeTests
public import HypoellipticAleksandrov.Parabolic.SpatialDifferenceQuotient
import HypoellipticAleksandrov.Parabolic.Dirichlet.LocalizedSpatialDifferenceQuotientH10PlateauLocality

/-!
# Smooth core for the arbitrary-`H¹₀` commutator

This module records the literal fixed-step commutator expression and proves it
on the dense compactly supported smooth core.  The arbitrary-`H¹₀` lifting
and its localized-field infrastructure remain in the canonical commutator
module.
-/

@[expose] public section

noncomputable section

open Filter MeasureTheory Set
open scoped BigOperators ENNReal RealInnerProductSpace Matrix.Norms.Elementwise

namespace HypoellipticAleksandrov.Parabolic.Dirichlet

section
variable {d : ℕ} {Ω inner : Set (PDE.Vec d)}

private theorem outerCutoff_mul_innerCutoff_eq {Kη Kχ : ℝ}
    (η : PDE.QuantitativeSmoothCutoff inner Ω Kη)
    (χ : PDE.QuantitativeSmoothCutoff (tsupport η.toFun) Ω Kχ)
    (y : PDE.Vec d) :
    χ y * η y = η y := by
  by_cases hy : η y = 0
  · simp [hy]
  · have hysupport : y ∈ tsupport η.toFun := subset_tsupport η.toFun hy
    rw [χ.eq_one_on_inner y hysupport, one_mul]

def h10CommutatorLhs {Kη : ℝ}
    (r₀ r₁ : ℝ) (h₀₁ : r₀ < r₁)
    (hΩ : IsOpen Ω) (hΩbounded : Bornology.IsBounded Ω)
    (a : CoefficientField d) (b : ℝ → PDE.Vec d → PDE.Vec d)
    (c : ℝ → PDE.Vec d → ℝ) (F : ℝ → PDE.Vec d → ℝ)
    (hFSmooth : IsSmoothOnClosedCylinder r₀ r₁ Ω F)
    (ζ : ReverseTimeScalarTest (r₁ - r₀))
    (η : PDE.QuantitativeSmoothCutoff inner Ω Kη)
    (k : Fin d) (h τ : ℝ)
    (hηshift : η.ShiftMapsInto k h Ω)
    (u : H10HilbertGraph hΩ) : ℝ :=
  let B := localizedSpatialDifferenceQuotientEnergyTestH10CLM
    hΩ η k h η.tsupport_subset hηshift
  ζ τ *
    (reverseTimeNegativeSourceRaw r₀ r₁ h₀₁ hΩ hΩbounded F hFSmooth τ (B u) -
      reverseTimeSpatialForm hΩ r₁ τ a b c u (B u))

end

def h10CommutatorRawLeaf
    {d : ℕ} {Ω : Set (PDE.Vec d)}
    (sourceD V : PDE.Vec d → ℝ)
    (aT aD : Fin d → Fin d → PDE.Vec d → ℝ)
    (E H U : Fin d → PDE.Vec d → ℝ)
    (driftT driftD : Fin d → PDE.Vec d → ℝ)
    (γT γD U₀ : PDE.Vec d → ℝ) : ℝ :=
  -(∫ y in Ω, sourceD y * V y ∂volume) -
    (∑ i : Fin d, ∑ j : Fin d, ∫ y in Ω,
      (aT i j y * E j y + aD i j y * U j y) * H i y ∂volume) -
    (∑ j : Fin d, ∫ y in Ω,
      (driftT j y * E j y + driftD j y * U j y) * V y ∂volume) +
    ∫ y in Ω, (γT y * V y + γD y * U₀ y) * V y ∂volume

section
variable {d : ℕ} {Ω inner : Set (PDE.Vec d)}

section
variable {Kη Kχ : ℝ} (r₀ r₁ : ℝ)

def h10CommutatorRawRhs (hΩ : IsOpen Ω)
    (a : CoefficientField d) (b : ℝ → PDE.Vec d → PDE.Vec d)
    (c : ℝ → PDE.Vec d → ℝ)
    (F : ℝ → PDE.Vec d → ℝ)
    (ζ : ReverseTimeScalarTest (r₁ - r₀))
    (η : PDE.QuantitativeSmoothCutoff inner Ω Kη)
    (χ : PDE.QuantitativeSmoothCutoff (tsupport η.toFun) Ω Kχ)
    (k : Fin d) (h τ : ℝ)
    (hηshift : η.ShiftMapsInto k h Ω)
    (u : H10HilbertGraph hΩ) : ℝ :=
  let A : H10HilbertGraph hΩ →L[ℝ] H10HilbertGraph hΩ :=
    localizedSpatialDifferenceQuotientH10CLM hΩ η k h η.tsupport_subset hηshift
  let V : PDE.Vec d → ℝ := fun y => valueCLM hΩ (A u) y
  let G : Fin d → PDE.Vec d → ℝ := fun i y =>
    PDE.hilbertVectorLpCoord Ω (2 : ℝ≥0∞) i (gradientCLM hΩ (A u)) y
  let W : Fin d → PDE.Vec d → ℝ := fun i y =>
    cutoffGradientSpatialDifferenceQuotientL2 hΩ.measurableSet η i k h (valueCLM hΩ u) y
  let E : Fin d → PDE.Vec d → ℝ := fun i y => G i y - W i y
  let H : Fin d → PDE.Vec d → ℝ := fun i y => G i y + W i y
  let U : Fin d → PDE.Vec d → ℝ := fun j y => η y *
    PDE.hilbertVectorLpCoord Ω (2 : ℝ≥0∞) j (gradientCLM hΩ u) y
  let U₀ : PDE.Vec d → ℝ := fun y => η y * valueCLM hΩ u y
  let source : TimeVelocity d → ℝ := fun z => F (r₁ - z.1) z.2
  let α : Fin d → Fin d → TimeVelocity d → ℝ := fun i j z =>
    reverseTimeCoefficient r₁ a z.1 z.2 i j
  let drift : Fin d → TimeVelocity d → ℝ := fun j z =>
    reverseTimeDivergenceDrift r₁ a b z.1 z.2 j
  let γ : TimeVelocity d → ℝ := fun z => reverseTimeScalarCoefficient r₁ c z.1 z.2
  let sourceD : PDE.Vec d → ℝ := fun y => ζ τ * η y *
    spatialDifferenceQuotient k h source (τ, y)
  let aT : Fin d → Fin d → PDE.Vec d → ℝ := fun i j y =>
    ζ τ * χ y * spatialTranslate k h (α i j) (τ, y)
  let aD : Fin d → Fin d → PDE.Vec d → ℝ := fun i j y =>
    ζ τ * χ y * spatialDifferenceQuotient k h (α i j) (τ, y)
  let driftT : Fin d → PDE.Vec d → ℝ := fun j y =>
    ζ τ * χ y * spatialTranslate k h (drift j) (τ, y)
  let driftD : Fin d → PDE.Vec d → ℝ := fun j y =>
    ζ τ * χ y * spatialDifferenceQuotient k h (drift j) (τ, y)
  let γT : PDE.Vec d → ℝ := fun y => ζ τ * χ y * spatialTranslate k h γ (τ, y)
  let γD : PDE.Vec d → ℝ := fun y =>
    ζ τ * χ y * spatialDifferenceQuotient k h γ (τ, y)
  h10CommutatorRawLeaf (Ω := Ω) sourceD V aT aD E H U driftT driftD γT γD U₀

/-- The literal fixed-step H¹₀ commutator identity. -/
def h10CommutatorFixedStepOutput (h₀₁ : r₀ < r₁)
    (hΩ : IsOpen Ω) (hΩbounded : Bornology.IsBounded Ω)
    (a : CoefficientField d) (b : ℝ → PDE.Vec d → PDE.Vec d)
    (c : ℝ → PDE.Vec d → ℝ)
    (F : ℝ → PDE.Vec d → ℝ)
    (hFSmooth : IsSmoothOnClosedCylinder r₀ r₁ Ω F)
    (ζ : ReverseTimeScalarTest (r₁ - r₀))
    (η : PDE.QuantitativeSmoothCutoff inner Ω Kη)
    (χ : PDE.QuantitativeSmoothCutoff (tsupport η.toFun) Ω Kχ)
    (k : Fin d) (h τ : ℝ)
    (hηshift : η.ShiftMapsInto k h Ω)
    (u : H10HilbertGraph hΩ) : Prop :=
  h10CommutatorLhs r₀ r₁ h₀₁ hΩ hΩbounded a b c F hFSmooth ζ η k h τ hηshift u =
    h10CommutatorRawRhs r₀ r₁ hΩ a b c F ζ η χ k h τ hηshift u

end

private def smoothCoreFactoredExpression {Kη : ℝ}
    (r₀ r₁ : ℝ) (a : CoefficientField d) (b : ℝ → PDE.Vec d → PDE.Vec d)
    (c F : ℝ → PDE.Vec d → ℝ) (ζ : ReverseTimeScalarTest (r₁ - r₀))
    (η : PDE.QuantitativeSmoothCutoff inner Ω Kη)
    (k : Fin d) (h τ : ℝ) (φ : PDE.WeakTestFunction Ω) : ℝ :=
  let source : TimeVelocity d → ℝ := fun z => F (r₁ - z.1) z.2
  let α : Fin d → Fin d → TimeVelocity d → ℝ := fun i j z =>
    reverseTimeCoefficient r₁ a z.1 z.2 i j
  let drift : Fin d → TimeVelocity d → ℝ := fun j z =>
    reverseTimeDivergenceDrift r₁ a b z.1 z.2 j
  let γ : TimeVelocity d → ℝ := fun z => reverseTimeScalarCoefficient r₁ c z.1 z.2
  let D : PDE.Vec d → ℝ := fun y =>
    (φ (y + h • PDE.basisVec k) - φ y) / h
  let Dg : Fin d → PDE.Vec d → ℝ := fun i y =>
    (φ.partialDeriv i (y + h • PDE.basisVec k) - φ.partialDeriv i y) / h
  let sourceSmooth : ℝ := ∫ y in Ω,
    spatialDifferenceQuotient k h source (τ, y) * η y ^ 2 * D y ∂volume
  let principalSmooth : Fin d → Fin d → ℝ := fun i j => ∫ y in Ω,
    (spatialTranslate k h (α i j) (τ, y) * Dg j y +
      spatialDifferenceQuotient k h (α i j) (τ, y) * φ.partialDeriv j y) *
      (2 * η y * PDE.classicalGradient η.toFun y i * D y + η y ^ 2 * Dg i y) ∂volume
  let driftSmooth : Fin d → ℝ := fun j => ∫ y in Ω,
    (spatialTranslate k h (drift j) (τ, y) * Dg j y +
      spatialDifferenceQuotient k h (drift j) (τ, y) * φ.partialDeriv j y) *
      (η y ^ 2 * D y) ∂volume
  let scalarSmooth : ℝ := ∫ y in Ω,
    (spatialTranslate k h γ (τ, y) * D y +
      spatialDifferenceQuotient k h γ (τ, y) * φ y) * (η y ^ 2 * D y) ∂volume
  ζ τ * (-sourceSmooth - (∑ i : Fin d, ∑ j : Fin d, principalSmooth i j) -
    (∑ j : Fin d, driftSmooth j) + scalarSmooth)

private theorem smoothCore_rawRhs_eq_factoredExpression {Kη Kχ : ℝ}
    (r₀ r₁ : ℝ) (hΩ : IsOpen Ω) (a : CoefficientField d)
    (b : ℝ → PDE.Vec d → PDE.Vec d) (c : ℝ → PDE.Vec d → ℝ)
    (F : ℝ → PDE.Vec d → ℝ)
    (ζ : ReverseTimeScalarTest (r₁ - r₀))
    (η : PDE.QuantitativeSmoothCutoff inner Ω Kη)
    (χ : PDE.QuantitativeSmoothCutoff (tsupport η.toFun) Ω Kχ)
    (k : Fin d) (h τ : ℝ)
    (hηshift : η.ShiftMapsInto k h Ω)
    (φ : PDE.WeakTestFunction Ω) :
    h10CommutatorRawRhs r₀ r₁ hΩ a b c F ζ η χ k h τ hηshift
      (smoothCompactlySupportedH1HilbertGraphToH10LinearMap hΩ φ) =
      smoothCoreFactoredExpression r₀ r₁ a b c F ζ η k h τ φ := by
  dsimp only [smoothCoreFactoredExpression]
  let u : H10HilbertGraph hΩ := smoothCompactlySupportedH1HilbertGraphToH10LinearMap hΩ φ
  let A := localizedSpatialDifferenceQuotientH10CLM hΩ η k h η.tsupport_subset hηshift
  let gc : Fin d → H10HilbertGraph hΩ →L[ℝ] PDE.ScalarLp Ω (2 : ℝ≥0∞) :=
    fun i => (PDE.hilbertVectorLpCoord Ω (2 : ℝ≥0∞) i).comp (gradientCLM hΩ)
  let V : PDE.Vec d → ℝ := fun y => valueCLM hΩ (A u) y
  let G : Fin d → PDE.Vec d → ℝ := fun i y =>
    PDE.hilbertVectorLpCoord Ω (2 : ℝ≥0∞) i (gradientCLM hΩ (A u)) y
  let W : Fin d → PDE.Vec d → ℝ := fun i y =>
    cutoffGradientSpatialDifferenceQuotientL2 hΩ.measurableSet η i k h
      (valueCLM hΩ u) y
  let E : Fin d → PDE.Vec d → ℝ := fun i y => G i y-W i y
  let H : Fin d → PDE.Vec d → ℝ := fun i y => G i y+W i y
  let U : Fin d → PDE.Vec d → ℝ := fun j y => η y*gc j u y
  let U₀ : PDE.Vec d → ℝ := fun y => η y*valueCLM hΩ u y
  let source : TimeVelocity d → ℝ := fun z => F (r₁-z.1) z.2
  let α : Fin d → Fin d → TimeVelocity d → ℝ := fun i j z => reverseTimeCoefficient r₁ a z.1 z.2 i j
  let drift : Fin d → TimeVelocity d → ℝ := fun j z => reverseTimeDivergenceDrift r₁ a b z.1 z.2 j
  let γ : TimeVelocity d → ℝ := fun z => reverseTimeScalarCoefficient r₁ c z.1 z.2
  let T (f : TimeVelocity d → ℝ) (y : PDE.Vec d) := spatialTranslate k h f (τ, y)
  let Q (f : TimeVelocity d → ℝ) (y : PDE.Vec d) := spatialDifferenceQuotient k h f (τ, y)
  let cχ (f : PDE.Vec d → ℝ) (y : PDE.Vec d) := ζ τ * χ y * f y
  let D (y : PDE.Vec d) := (φ (y + h • PDE.basisVec k) - φ y) / h
  let Dg (i : Fin d) (y : PDE.Vec d) :=
    (φ.partialDeriv i (y + h • PDE.basisVec k) - φ.partialDeriv i y) / h
  change h10CommutatorRawLeaf (Ω := Ω) (fun y => ζ τ * η y * Q source y) V
    (fun i j => cχ (T (α i j))) (fun i j => cχ (Q (α i j))) E H U
    (fun j => cχ (T (drift j))) (fun j => cχ (Q (drift j))) (cχ (T γ)) (cχ (Q γ)) U₀ = _
  have hv : ⇑(valueCLM hΩ u) =ᵐ[PDE.volumeOn Ω] φ :=
    ae_valueCLM_smoothCompactlySupportedH1HilbertGraph hΩ φ
  have hg i : ⇑(gc i u) =ᵐ[PDE.volumeOn Ω] φ.partialDeriv i :=
    (PDE.coeFn_hilbertVectorLpCoord Ω 2 i _).trans
      (ae_gradientCoordCLM_smoothCompactlySupportedH1HilbertGraph hΩ φ i)
  have hV : V=ᵐ[PDE.volumeOn Ω] fun y=>η y*D y := by
    change ⇑(((valueCLM hΩ).comp A) u) =ᵐ[PDE.volumeOn Ω] _
    dsimp only [A]
    rw [valueCLM_comp_localizedSpatialDifferenceQuotientH10CLM]
    exact localizedSpatialDifferenceQuotientL2_apply_ae_of_ae_eq
      hΩ.measurableSet η k h (valueCLM hΩ u) φ hv hηshift
  have hW i : W i =ᵐ[PDE.volumeOn Ω] fun y => PDE.classicalGradient η.toFun y i * D y :=
    cutoffGradientSpatialDifferenceQuotientL2_apply_ae_of_ae_eq
      hΩ.measurableSet η i k h (valueCLM hΩ u) φ hv hηshift
  have hDg i : ⇑(localizedSpatialDifferenceQuotientL2 hΩ.measurableSet η k h (gc i u))
      =ᵐ[PDE.volumeOn Ω] fun y => η y * Dg i y :=
    localizedSpatialDifferenceQuotientL2_apply_ae_of_ae_eq
      hΩ.measurableSet η k h (gc i u) (φ.partialDeriv i) (hg i) hηshift
  have hG i : G i =ᵐ[PDE.volumeOn Ω] fun y =>
      PDE.classicalGradient η.toFun y i * D y + η y * Dg i y := by
    dsimp only [G, A]
    rw [gradientCoord_localizedSpatialDifferenceQuotientH10CLM_eq]
    exact (Lp.coeFn_add _ _).trans ((hW i).add (hDg i))
  have hE i : E i =ᵐ[PDE.volumeOn Ω] fun y => η y * Dg i y := by
    filter_upwards [hG i, hW i] with y hG' hW'
    dsimp only [E]
    rw [hG', hW']
    ring
  have hH i : H i =ᵐ[PDE.volumeOn Ω] fun y =>
      2 * PDE.classicalGradient η.toFun y i * D y + η y * Dg i y := by
    filter_upwards [hG i, hW i] with y hG' hW'
    dsimp only [H]
    rw [hG', hW']
    ring
  have hU i : U i =ᵐ[PDE.volumeOn Ω] fun y => η y * φ.partialDeriv i y :=
    EventuallyEq.rfl.mul (hg i)
  have hU₀ : U₀ =ᵐ[PDE.volumeOn Ω] fun y => η y * φ y := EventuallyEq.rfl.mul hv
  have hsourceFactor : (∫ y in Ω, ζ τ * η y * Q source y * V y ∂volume) =
      ζ τ * ∫ y in Ω, Q source y * η y ^ 2 * D y ∂volume := by
    rw [← integral_const_mul]
    apply integral_congr_ae
    filter_upwards [hV] with y hy
    rw [hy]
    ring
  have hpair (q r : PDE.Vec d → ℝ) {X Y Z x y z w : PDE.Vec d → ℝ}
      (hx : X =ᵐ[PDE.volumeOn Ω] fun t => η t * x t)
      (hy : Y =ᵐ[PDE.volumeOn Ω] fun t => η t * y t)
      (hz : Z =ᵐ[PDE.volumeOn Ω] z) (hw : ∀ t, η t * z t = w t) :
      (∫ t in Ω, (cχ q t * X t + cχ r t * Y t) * Z t ∂volume) =
        ζ τ * ∫ t in Ω, (q t * x t + r t * y t) * w t ∂volume := by
    rw [← integral_const_mul]
    apply integral_congr_ae
    filter_upwards [hx, hy, hz] with t hxt hyt hzt
    rw [hxt, hyt, hzt, ← hw]
    calc
      _ = ζ τ * (χ t * η t) * ((q t * x t + r t * y t) * z t) := by dsimp [cχ]; ring
      _ = _ := by rw [outerCutoff_mul_innerCutoff_eq η χ t]; ring
  have hηV (y : PDE.Vec d) : η y * (η y * D y) = η y ^ 2 * D y := by ring
  have hηH (i : Fin d) (y : PDE.Vec d) :
      η y * (2 * PDE.classicalGradient η.toFun y i * D y + η y * Dg i y) =
        2 * η y * PDE.classicalGradient η.toFun y i * D y + η y ^ 2 * Dg i y := by ring
  have hprincipal (i j : Fin d) := hpair (T (α i j)) (Q (α i j)) (hE j) (hU j) (hH i) (hηH i)
  have hdrift (j : Fin d) := hpair (T (drift j)) (Q (drift j)) (hE j) (hU j) hV hηV
  unfold h10CommutatorRawLeaf
  rw [hsourceFactor, hpair (T γ) (Q γ) hV hU₀ hV hηV]
  simp only [hprincipal, hdrift, ← Finset.mul_sum, T, Q, D, Dg, source, α, drift, γ]
  ring

private theorem smoothCore_lhs_eq_factoredExpression {Kη : ℝ}
    (r₀ r₁ : ℝ) (h₀₁ : r₀ < r₁) (hΩ : IsOpen Ω)
    (hΩbounded : Bornology.IsBounded Ω) (a : CoefficientField d)
    (b : ℝ → PDE.Vec d → PDE.Vec d) (c : ℝ → PDE.Vec d → ℝ)
    (haSmooth : IsSmoothOnClosedCylinder r₀ r₁ Ω a)
    (hbSmooth : IsSmoothOnClosedCylinder r₀ r₁ Ω b)
    (hcSmooth : IsSmoothOnClosedCylinder r₀ r₁ Ω c)
    (F : ℝ → PDE.Vec d → ℝ)
    (hFSmooth : IsSmoothOnClosedCylinder r₀ r₁ Ω F)
    (ζ : ReverseTimeScalarTest (r₁ - r₀))
    (η : PDE.QuantitativeSmoothCutoff inner Ω Kη)
    (k : Fin d) (h τ : ℝ)
    (hηshift : η.ShiftMapsInto k h Ω)
    (hτ : τ ∈ Set.Icc 0 (r₁ - r₀)) (φ : PDE.WeakTestFunction Ω) :
    h10CommutatorLhs r₀ r₁ h₀₁ hΩ hΩbounded a b c F hFSmooth ζ η k h τ hηshift
      (smoothCompactlySupportedH1HilbertGraphToH10LinearMap hΩ φ) =
      smoothCoreFactoredExpression r₀ r₁ a b c F ζ η k h τ φ := by
  dsimp only [h10CommutatorLhs, smoothCoreFactoredExpression]
  have hsmooth := reverseTimeSource_sub_reverseTimeSpatialForm_smooth_energyTest_eq_commutator
    r₀ r₁ hΩ hΩbounded a b c haSmooth hbSmooth hcSmooth F hFSmooth τ hτ
      η k h φ η.tsupport_subset hηshift
  rw [reverseTimeNegativeSourceRaw_eq_sourceFunctional_of_mem_Icc
    r₀ r₁ h₀₁ hΩ hΩbounded F hFSmooth τ hτ]
  simpa only [spatialDifferenceQuotient_apply,
    spatialTranslate_apply, spatialShift_apply, reverseTimeCoefficient_apply,
    reverseTimeDivergenceDrift, reverseTimeScalarCoefficient_apply, mul_assoc] using
    (congrArg (fun x : ℝ => ζ τ * x) hsmooth)

/-- The literal fixed-step commutator identity on the dense smooth H¹₀ core. -/
theorem smoothCore_fixedStep_reverseTimeSource_sub_reverseTimeSpatialForm_eq_commutator {Kη Kχ : ℝ}
    (r₀ r₁ : ℝ) (h₀₁ : r₀ < r₁) (hΩ : IsOpen Ω)
    (hΩbounded : Bornology.IsBounded Ω) (a : CoefficientField d)
    (b : ℝ → PDE.Vec d → PDE.Vec d) (c : ℝ → PDE.Vec d → ℝ)
    (haSmooth : IsSmoothOnClosedCylinder r₀ r₁ Ω a)
    (hbSmooth : IsSmoothOnClosedCylinder r₀ r₁ Ω b)
    (hcSmooth : IsSmoothOnClosedCylinder r₀ r₁ Ω c)
    (F : ℝ → PDE.Vec d → ℝ)
    (hFSmooth : IsSmoothOnClosedCylinder r₀ r₁ Ω F)
    (ζ : ReverseTimeScalarTest (r₁ - r₀))
    (η : PDE.QuantitativeSmoothCutoff inner Ω Kη)
    (χ : PDE.QuantitativeSmoothCutoff (tsupport η.toFun) Ω Kχ)
    (k : Fin d) (h τ : ℝ)
    (hηshift : η.ShiftMapsInto k h Ω)
    (hτ : τ ∈ Set.Icc 0 (r₁ - r₀)) (φ : PDE.WeakTestFunction Ω) :
    h10CommutatorFixedStepOutput r₀ r₁ h₀₁ hΩ hΩbounded a b c F hFSmooth
      ζ η χ k h τ hηshift
      (smoothCompactlySupportedH1HilbertGraphToH10LinearMap hΩ φ) := by
  exact (smoothCore_lhs_eq_factoredExpression r₀ r₁ h₀₁ hΩ hΩbounded a b c haSmooth
    hbSmooth hcSmooth F hFSmooth ζ η k h τ hηshift hτ φ).trans
    (smoothCore_rawRhs_eq_factoredExpression r₀ r₁ hΩ a b c F ζ η χ k h τ hηshift φ).symm

end

end HypoellipticAleksandrov.Parabolic.Dirichlet
