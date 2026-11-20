module

public import HypoellipticAleksandrov.Parabolic.Dirichlet.SpatialCoordinateShiftCarrierGeometry
public import HypoellipticAleksandrov.Parabolic.SpatialDirectionalDifferenceQuotientBound
public import HypoellipticAleksandrov.Parabolic.Dirichlet.ReverseTimeInteriorCoefficientMajorant
public import HypoellipticAleksandrov.Parabolic.Dirichlet.ReverseTimeSmoothness
public import PDEFoundation.Sobolev.Cutoff.Basic

/-!
# Uniform reverse-time raw-amplitude majorants

This module turns the literal pointwise spatial derivative majorants from the
Caccioppoli estimate into the raw coefficient bounds required by
the localized difference-quotient argument.
-/

@[expose] public section

noncomputable section

namespace HypoellipticAleksandrov.Parabolic.Dirichlet

open Set
open scoped Matrix.Norms.Elementwise

section
variable {d : ℕ} {Ω inner : Set (PDE.Vec d)} {Kχ : ℝ} (r₀ r₁ : ℝ)
  (χ : PDE.QuantitativeSmoothCutoff inner Ω Kχ) (δ M : ℝ)
  (hcarrier : spatialCoordinateShiftCarrier (tsupport χ.toFun) δ ⊆ Ω) (a : CoefficientField d)
  (b : ℝ → PDE.Vec d → PDE.Vec d) (c F : ℝ → PDE.Vec d → ℝ)
  (ha : IsSmoothOnClosedCylinder r₀ r₁ Ω a) (hb : IsSmoothOnClosedCylinder r₀ r₁ Ω b)
  (hc : IsSmoothOnClosedCylinder r₀ r₁ Ω c) (hF : IsSmoothOnClosedCylinder r₀ r₁ Ω F)
  (hbound : ReverseTimeCoefficientMajorant r₀ r₁ (tsupport χ.toFun) δ M a b c F)
include hcarrier ha hb hc hF hbound

/-- Literal spatial derivative and value majorants on the fixed coordinate
carrier give all raw reverse-time amplitudes used by the Caccioppoli
commutator. -/
theorem reverseTimeSpatialRawAmplitude_bounds_of_majorants :
    (∀ (k : Fin d) (h : ℝ), |h| ≤ δ →
      χ.ShiftMapsInto k h Ω) ∧
    (∀ (k : Fin d) (h τ : ℝ) (y : PDE.Vec d), |h| ≤ δ →
      τ ∈ Set.Icc 0 (r₁ - r₀) → y ∈ tsupport χ.toFun →
      |spatialDifferenceQuotient k h
        (fun z : TimeVelocity d => reverseTimeScalarCoefficient r₁ F z.1 z.2)
        (τ, y)| ≤ M) ∧
    (∀ (i j k : Fin d) (h τ : ℝ) (y : PDE.Vec d), |h| ≤ δ →
      τ ∈ Set.Icc 0 (r₁ - r₀) → y ∈ tsupport χ.toFun →
      |spatialDifferenceQuotient k h
        (fun z : TimeVelocity d => reverseTimeCoefficient r₁ a z.1 z.2 i j)
        (τ, y)| ≤ M) ∧
    (∀ (j k : Fin d) (h τ : ℝ) (y : PDE.Vec d), |h| ≤ δ →
      τ ∈ Set.Icc 0 (r₁ - r₀) → y ∈ tsupport χ.toFun →
      |spatialTranslate k h
        (fun z : TimeVelocity d => reverseTimeDivergenceDrift r₁ a b z.1 z.2 j)
        (τ, y)| ≤ M) ∧
    (∀ (j k : Fin d) (h τ : ℝ) (y : PDE.Vec d), |h| ≤ δ →
      τ ∈ Set.Icc 0 (r₁ - r₀) → y ∈ tsupport χ.toFun →
      |spatialDifferenceQuotient k h
        (fun z : TimeVelocity d => reverseTimeDivergenceDrift r₁ a b z.1 z.2 j)
        (τ, y)| ≤ M) ∧
    (∀ (k : Fin d) (h τ : ℝ) (y : PDE.Vec d), |h| ≤ δ →
      τ ∈ Set.Icc 0 (r₁ - r₀) → y ∈ tsupport χ.toFun →
      |spatialTranslate k h
        (fun z : TimeVelocity d => reverseTimeScalarCoefficient r₁ c z.1 z.2)
        (τ, y)| ≤ M) ∧
    (∀ (k : Fin d) (h τ : ℝ) (y : PDE.Vec d), |h| ≤ δ →
      τ ∈ Set.Icc 0 (r₁ - r₀) → y ∈ tsupport χ.toFun →
      |spatialDifferenceQuotient k h
        (fun z : TimeVelocity d => reverseTimeScalarCoefficient r₁ c z.1 z.2)
        (τ, y)| ≤ M) := by
  classical
  let Q : Set (TimeVelocity d) := Set.Icc 0 (r₁ - r₀) ×ˢ
    spatialCoordinateShiftCarrier (tsupport χ.toFun) δ
  have hQreverse : reverseTimeMap r₁ '' Q ⊆ scalarParabolicClosedCylinder r₀ r₁ Ω :=
    reverseTimeImage_subset_closedCylinder hcarrier
  have hAderiv (i j : Fin d) : ∀ w ∈ Q, DifferentiableAt ℝ
      (fun z : TimeVelocity d => reverseTimeCoefficient r₁ a z.1 z.2 i j) w := by
    intro w hw
    change DifferentiableAt ℝ
      (((fun z : TimeVelocity d => a z.1 z.2 i j) ∘ reverseTimeMap r₁)) w
    exact IsSmoothOnNeighborhood.differentiableAt
      (IsSmoothOnNeighborhood.reverseTime r₁ hQreverse
        (IsSmoothOnNeighborhood.coefficientEntry a ha i j)) hw
  have hBderiv (j : Fin d) : ∀ w ∈ Q, DifferentiableAt ℝ
      (fun z : TimeVelocity d => reverseTimeDivergenceDrift r₁ a b z.1 z.2 j) w := by
    intro w hw
    change DifferentiableAt ℝ
      (((fun z : TimeVelocity d => scalarSpatialCoefficientDivergence a z j -
        b z.1 z.2 j) ∘ reverseTimeMap r₁)) w
    exact IsSmoothOnNeighborhood.differentiableAt
      (IsSmoothOnNeighborhood.reverseTime r₁ hQreverse
        (IsSmoothOnNeighborhood.divergenceDriftEntry a b ha hb j)) hw
  have hscalar (f : ℝ → PDE.Vec d → ℝ) (hf : IsSmoothOnClosedCylinder r₀ r₁ Ω f) :
      ∀ w ∈ Q, DifferentiableAt ℝ (fun z => reverseTimeScalarCoefficient r₁ f z.1 z.2) w :=
    fun _ hw => IsSmoothOnNeighborhood.differentiableAt (IsSmoothOnNeighborhood.reverseTime r₁ hQreverse hf) hw
  have hdiff {f : TimeVelocity d → ℝ} (k : Fin d) {h τ : ℝ} {y : PDE.Vec d}
      (hh : |h| ≤ δ) (hτ : τ ∈ Icc 0 (r₁ - r₀)) (hy : y ∈ tsupport χ.toFun)
      (hd : ∀ w ∈ Q, DifferentiableAt ℝ f w)
      (hm : ∀ w ∈ Q, |(fderiv ℝ f w) (0, PDE.basisVec k)| ≤ M) :
      |spatialDifferenceQuotient k h f (τ, y)| ≤ M := by
    have hs := segment_spatialShift_subset_prod_spatialCoordinateShiftCarrier k (τ, y) hh ⟨hτ, hy⟩
    exact abs_spatialDifferenceQuotient_le_of_segment_spatialFDeriv_bound
      (fun w hw => hd w (hs hw)) (fun w hw => hm w (hs hw))
  have hshift (k : Fin d) {h τ : ℝ} {y : PDE.Vec d}
      (hh : |h| ≤ δ) (hτ : τ ∈ Icc 0 (r₁ - r₀)) (hy : y ∈ tsupport χ.toFun) :
      spatialShift k h (τ, y) ∈ Q :=
    ⟨by simpa only [spatialShift_apply] using hτ, mem_spatialCoordinateShiftCarrier_of_mem_of_abs_le hy hh⟩
  refine ⟨fun k _ hh => mapsTo_add_smul_basisVec_of_spatialCoordinateShiftCarrier_subset hcarrier k hh,
    ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro k h τ y hh hτ hy
    exact hdiff k hh hτ hy (hscalar F hF) fun w hw =>
      (abs_spatialScalarFDeriv_le _ w k).trans (hbound.sourceDeriv w hw)
  · intro i j k h τ y hh hτ hy
    exact hdiff k hh hτ hy (hAderiv i j) fun w hw =>
      (abs_spatialMatrixFDeriv_le _ w i j k).trans (hbound.diffusionDeriv w hw)
  · intro j k h τ y hh hτ hy
    rw [spatialTranslate_apply]
    exact (PDE.abs_apply_le_vecEuclideanNorm _ j).trans (hbound.drift _ (hshift k hh hτ hy))
  · intro j k h τ y hh hτ hy
    exact hdiff k hh hτ hy (hBderiv j) fun w hw =>
      (abs_spatialVectorFDeriv_le _ w j k).trans (hbound.driftDeriv w hw)
  · intro k h τ y hh hτ hy
    exact hbound.scalar _ (hshift k hh hτ hy)
  · intro k h τ y hh hτ hy
    exact hdiff k hh hτ hy (hscalar c hc) fun w hw =>
      (abs_spatialScalarFDeriv_le _ w k).trans (hbound.scalarDeriv w hw)

end

end HypoellipticAleksandrov.Parabolic.Dirichlet
