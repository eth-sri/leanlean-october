module

public import HypoellipticAleksandrov.Parabolic.Dirichlet.OriginalTimeInteriorGeometry
public import HypoellipticAleksandrov.Parabolic.Dirichlet.OriginalTimeProductRepresentativeUnique
public import HypoellipticAleksandrov.Parabolic.Dirichlet.ReverseTimeInteriorCoefficientMajorant
public import HypoellipticAleksandrov.Parabolic.Dirichlet.H10InteriorCaccioppoliTimeDerivative
public import HypoellipticAleksandrov.Parabolic.ParabolicW12TimeReflection
import HypoellipticAleksandrov.Parabolic.Dirichlet.OriginalTimeProductRepresentative
import HypoellipticAleksandrov.Parabolic.NestedQuantitativeSmoothCutoffExistence
import HypoellipticAleksandrov.Parabolic.Dirichlet.H10InteriorCaccioppoliGradientRawTransport
import HypoellipticAleksandrov.Parabolic.Dirichlet.H10InteriorCaccioppoliHessian
import HypoellipticAleksandrov.Parabolic.Dirichlet.HessianCoefficientCancellation
import HypoellipticAleksandrov.Parabolic.Dirichlet.HessianCoefficientCancellationAlgebra
import HypoellipticAleksandrov.Parabolic.Dirichlet.HessianCoefficientWeightedWeakIdentity
import HypoellipticAleksandrov.Parabolic.Dirichlet.HessianTimeDerivativeL2Assembly
import HypoellipticAleksandrov.Parabolic.Dirichlet.ReverseTimeProductRepresentative
import HypoellipticAleksandrov.Parabolic.Dirichlet.ReverseTimeSeparatedProductDistribution
import HypoellipticAleksandrov.Parabolic.Dirichlet.ReverseTimeSeparatedRawIntegrability
import HypoellipticAleksandrov.Parabolic.Dirichlet.ReverseTimeSpatialWeakDerivative
import HypoellipticAleksandrov.Parabolic.Dirichlet.SeparatedTestsDetermineWeakTimeDerivative
import HypoellipticAleksandrov.Parabolic.SpatialDifferenceQuotientL2WeakDerivative
import Mathlib.MeasureTheory.Integral.Bochner.Basic

/-!
# Original-time local L2 strong jets

This file reflects the interior reverse-time weak Hessian and time derivative
back to the original-time cylinder.
-/

@[expose] public section

noncomputable section

namespace HypoellipticAleksandrov.Parabolic.Dirichlet

open Filter MeasureTheory Set IsReverseTimeVariationalEnergySolution
open scoped BigOperators ENNReal MatrixOrder Matrix.Norms.Elementwise
open Topology
open scoped Topology RealInnerProductSpace

/- A supplied global original-time value representative admits a local
anisotropic `L²` weak jet satisfying the literal original-time equation. -/
theorem exists_originalTimeLocalL2StrongJet_of_valueRepresentative
    {d : ℕ} {Ω O : Set (PDE.Vec d)}
    (hd : 0 < d)
    (r₀ s₀ s₁ r₁ : ℝ)
    (h₀₁ : r₀ < r₁)
    (hr₀s₀ : r₀ < s₀)
    (hs₀s₁ : s₀ < s₁)
    (hs₁r₁ : s₁ < r₁)
    (hΩ : IsOpen Ω)
    (hΩbounded : Bornology.IsBounded Ω)
    (hOopen : IsOpen O)
    (hOnonempty : O.Nonempty)
    (hOcompact : IsCompact (closure O))
    (hOΩ : closure O ⊆ Ω)
    (lam Lam : ℝ)
    (hlam : 0 < lam)
    (hlamLam : lam ≤ Lam)
    (a : CoefficientField d)
    (b : ℝ → PDE.Vec d → PDE.Vec d)
    (c F : ℝ → PDE.Vec d → ℝ)
    (haSmooth : IsSmoothOnNeighborhood
      (fun z : TimeVelocity d => a z.1 z.2)
      (scalarParabolicClosedCylinder r₀ r₁ Ω))
    (hbSmooth : IsSmoothOnNeighborhood
      (fun z : TimeVelocity d => b z.1 z.2)
      (scalarParabolicClosedCylinder r₀ r₁ Ω))
    (hcSmooth : IsSmoothOnNeighborhood
      (fun z : TimeVelocity d => c z.1 z.2)
      (scalarParabolicClosedCylinder r₀ r₁ Ω))
    (hFSmooth : IsSmoothOnNeighborhood
      (fun z : TimeVelocity d => F z.1 z.2)
      (scalarParabolicClosedCylinder r₀ r₁ Ω))
    (hLower : ∀ z : TimeVelocity d,
      z ∈ scalarParabolicClosedCylinder r₀ r₁ Ω →
        lam • (1 : PDE.Mat d) ≤ a z.1 z.2)
    (hUpper : ∀ z : TimeVelocity d,
      z ∈ scalarParabolicClosedCylinder r₀ r₁ Ω →
        a z.1 z.2 ≤ Lam • (1 : PDE.Mat d))
    (hcNonpos : ∀ z : TimeVelocity d,
      z ∈ scalarParabolicClosedCylinder r₀ r₁ Ω →
        c z.1 z.2 ≤ 0)
    (initial : PDE.ScalarLp Ω (2 : ℝ≥0∞))
    (u : ReverseTimeL2V hΩ (r₁ - r₀))
    (g : ReverseTimeL2VStar hΩ (r₁ - r₀))
    (hdu : HasGelfandWeakTimeDerivative hΩ (r₁ - r₀)
      (sub_pos.mpr h₀₁) u g)
    (hu : IsReverseTimeVariationalEnergySolution
      r₀ r₁ h₀₁ hΩ hΩbounded
      a b c F hFSmooth initial u g hdu)
    (w : TimeVelocity d → ℝ)
    (hwmem : MemLp w (2 : ℝ≥0∞)
      (timeVelocityVolumeOn (Set.Ioo r₀ r₁ ×ˢ Ω)))
    (hwslice : ∀ᵐ r ∂volume.restrict (Set.Ioo r₀ r₁),
      (fun y => w (r, y)) =ᵐ[PDE.volumeOn Ω]
        fun y => valueCLM hΩ (u (r₁ - r)) y) :
    ∃ J : ParabolicW12Function d
        (Set.Ioo s₀ s₁ ×ˢ O) (2 : ℝ≥0∞),
      J.toFun =ᵐ[
        timeVelocityVolumeOn (Set.Ioo s₀ s₁ ×ˢ O)] w ∧
      ∀ᵐ z ∂timeVelocityVolumeOn (Set.Ioo s₀ s₁ ×ˢ O),
        J.timeDeriv z +
              (∑ i : Fin d, ∑ j : Fin d,
                a z.1 z.2 i j * J.velocityHessian z j i) +
            (∑ j : Fin d,
              b z.1 z.2 j * J.velocityGrad z j) +
          c z.1 z.2 * J.toFun z =
        F z.1 z.2 := by
  obtain ⟨Kη, η, Kχ, χ, τ₀, τ₁, τ₂, τ₃, hχΩ, rfl, rfl, rfl, rfl,
      hτ₀, hτ₀τ₁, hτ₁τ₂, hτ₂τ₃, hτ₃⟩ : ∃ (Kη : ℝ)
      (η : PDE.QuantitativeSmoothCutoff (closure O) Ω Kη)
      (Kχ : ℝ)
      (χ : PDE.QuantitativeSmoothCutoff (tsupport η.toFun) Ω Kχ)
      (τ₀ τ₁ τ₂ τ₃ : ℝ),
      tsupport χ.toFun ⊆ Ω ∧
      τ₀ = (r₁ - s₁) / 2 ∧
      τ₁ = r₁ - s₁ ∧
      τ₂ = r₁ - s₀ ∧
      τ₃ = ((r₁ - s₀) + (r₁ - r₀)) / 2 ∧
      0 < τ₀ ∧ τ₀ < τ₁ ∧ τ₁ < τ₂ ∧
      τ₂ < τ₃ ∧ τ₃ < r₁ - r₀ := by
      obtain ⟨Kη, ⟨η, Kχ, χ⟩⟩ :=
        exists_nestedQuantitativeSmoothCutoffs_tsupport_subset hOcompact hΩ hOΩ
      refine ⟨Kη, η, Kχ, χ, (r₁ - s₁) / 2, r₁ - s₁, r₁ - s₀,
        ((r₁ - s₀) + (r₁ - r₀)) / 2, χ.tsupport_subset, rfl, rfl, rfl, rfl, ?_⟩
      constructor
      · linarith
      constructor
      · linarith
      constructor
      · linarith
      constructor <;> linarith

    /- Reflection at `r₁` carries the selected reverse-time interior cylinder
    back to the literal original-time cylinder. -/
  obtain ⟨δ, hδ, hcarrier, hpredecessor⟩ :
      ∃ (δ : ℝ) (hδ : 0 < δ)
              (hcarrier : spatialCoordinateShiftCarrier (tsupport χ.toFun) δ ⊆ Ω),
            ∀ (τ₀ τ₁ τ₂ τ₃ : ℝ)
              (hτ₀ : 0 < τ₀) (hτ₀τ₁ : τ₀ < τ₁)
              (hτ₁τ₂ : τ₁ < τ₂) (hτ₂τ₃ : τ₂ < τ₃)
              (hτ₃ : τ₃ < r₁ - r₀),
            ∀ (lam Lam M : ℝ) (hlam : 0 < lam)
              (hlamLam : lam ≤ Lam) (hM : 0 ≤ M),
              ∃ C_cac : ℝ, 0 ≤ C_cac ∧
                ∀ (a : CoefficientField d)
                  (b : ℝ → PDE.Vec d → PDE.Vec d)
                  (c F : ℝ → PDE.Vec d → ℝ),
                ∀ (haSmooth : IsSmoothOnNeighborhood
                      (fun z : TimeVelocity d => a z.1 z.2)
                      (scalarParabolicClosedCylinder r₀ r₁ Ω))
                  (hbSmooth : IsSmoothOnNeighborhood
                      (fun z : TimeVelocity d => b z.1 z.2)
                      (scalarParabolicClosedCylinder r₀ r₁ Ω))
                  (hcSmooth : IsSmoothOnNeighborhood
                      (fun z : TimeVelocity d => c z.1 z.2)
                      (scalarParabolicClosedCylinder r₀ r₁ Ω))
                  (hFSmooth : IsSmoothOnNeighborhood
                      (fun z : TimeVelocity d => F z.1 z.2)
                      (scalarParabolicClosedCylinder r₀ r₁ Ω))
                  (hLower : ∀ z : TimeVelocity d,
                      z ∈ scalarParabolicClosedCylinder r₀ r₁ Ω →
                        lam • (1 : PDE.Mat d) ≤ a z.1 z.2)
                  (hUpper : ∀ z : TimeVelocity d,
                      z ∈ scalarParabolicClosedCylinder r₀ r₁ Ω →
                        a z.1 z.2 ≤ Lam • (1 : PDE.Mat d))
                  (hcNonpos : ∀ z : TimeVelocity d,
                      z ∈ scalarParabolicClosedCylinder r₀ r₁ Ω →
                        c z.1 z.2 ≤ 0)
                  (hA : ∀ z ∈ Set.Icc 0 (r₁ - r₀) ×ˢ
                      spatialCoordinateShiftCarrier (tsupport χ.toFun) δ,
                      spatialMatrixFDerivFrobeniusNorm
                        (fun w : TimeVelocity d =>
                          reverseTimeCoefficient r₁ a w.1 w.2) z ≤ M)
                  (hB : ∀ z ∈ Set.Icc 0 (r₁ - r₀) ×ˢ
                      spatialCoordinateShiftCarrier (tsupport χ.toFun) δ,
                      PDE.vecEuclideanNorm
                        (reverseTimeDivergenceDrift r₁ a b z.1 z.2) ≤ M)
                  (hBD : ∀ z ∈ Set.Icc 0 (r₁ - r₀) ×ˢ
                      spatialCoordinateShiftCarrier (tsupport χ.toFun) δ,
                      spatialVectorFDerivFrobeniusNorm
                        (fun w : TimeVelocity d =>
                          reverseTimeDivergenceDrift r₁ a b w.1 w.2) z ≤ M)
                  (hq : ∀ z ∈ Set.Icc 0 (r₁ - r₀) ×ˢ
                      spatialCoordinateShiftCarrier (tsupport χ.toFun) δ,
                      |-(reverseTimeScalarCoefficient r₁ c z.1 z.2)| ≤ M)
                  (hqD : ∀ z ∈ Set.Icc 0 (r₁ - r₀) ×ˢ
                      spatialCoordinateShiftCarrier (tsupport χ.toFun) δ,
                      spatialScalarFDerivEuclideanNorm
                        (fun w : TimeVelocity d =>
                          -(reverseTimeScalarCoefficient r₁ c w.1 w.2)) z ≤ M)
                  (hfD : ∀ z ∈ Set.Icc 0 (r₁ - r₀) ×ˢ
                      spatialCoordinateShiftCarrier (tsupport χ.toFun) δ,
                      spatialScalarFDerivEuclideanNorm
                        (fun w : TimeVelocity d =>
                          -(reverseTimeScalarCoefficient r₁ F w.1 w.2)) z ≤ M),
                ∀ (initial : PDE.ScalarLp Ω (2 : ℝ≥0∞))
                  (u : ReverseTimeL2V hΩ (r₁ - r₀))
                  (g : ReverseTimeL2VStar hΩ (r₁ - r₀))
                  (hdu : HasGelfandWeakTimeDerivative hΩ (r₁ - r₀)
                    (sub_pos.mpr h₀₁) u g)
                  (hu : IsReverseTimeVariationalEnergySolution
                    r₀ r₁ h₀₁ hΩ hΩbounded a b c F hFSmooth initial u g hdu),
                  ∃ G : Fin d → TimeVelocity d → ℝ,
                    (∀ j, MemLp (G j) (2 : ℝ≥0∞)
                      (timeVelocityVolumeOn
                        (reverseTimeOpenInterval (r₁ - r₀) ×ˢ Ω))) ∧
                    ∃ H : TimeVelocity d → PDE.Mat d,
                      ∃ hHmem : ∀ j k : Fin d,
                          ParabolicMemLpOn (Set.Ioo τ₁ τ₂ ×ˢ O)
                            (2 : ℝ≥0∞) (fun z => H z j k),
                        (∀ j k : Fin d,
                          HasWeakVelocityPartialDerivOn
                            (Set.Ioo τ₁ τ₂ ×ˢ O) k (G j)
                            (fun z => H z j k)) ∧
                        (∀ j k : Fin d,
                          ‖(hHmem j k).toLp (fun z => H z j k)‖ ≤
                            Real.sqrt
                              (C_cac *
                                ((r₁ - r₀) +
                                  (reverseTimeGalerkinPrimalRadius
                                    r₀ r₁ lam h₀₁ hlam hΩ hΩbounded a b c F
                                    haSmooth hbSmooth hcSmooth hFSmooth hLower hcNonpos
                                    initial) ^ 2))) ∧
                        ∃ U : TimeVelocity d → ℝ,
                          MemLp U (2 : ℝ≥0∞)
                            (timeVelocityVolumeOn
                              (reverseTimeOpenInterval (r₁ - r₀) ×ˢ Ω)) ∧
                          (∀ᵐ τ ∂reverseTimeVolume (r₁ - r₀),
                            ((fun y => U (τ, y)) =ᵐ[PDE.volumeOn Ω]
                              fun y => valueCLM hΩ (u τ) y) ∧
                            (∀ j,
                              (fun y => G j (τ, y)) =ᵐ[PDE.volumeOn Ω]
                                fun y => gradientCLM hΩ (u τ) y j)) ∧
                          (∀ j : Fin d,
                            HasWeakVelocityPartialDerivOn
                              (Set.Ioo τ₁ τ₂ ×ˢ O) j U (G j)) ∧
                          let W : TimeVelocity d → ℝ := fun z =>
                            (∑ i : Fin d, ∑ j : Fin d,
                              reverseTimeCoefficient r₁ a z.1 z.2 i j * H z j i) +
                            (∑ j : Fin d,
                              reverseTimeVectorCoefficient r₁ b z.1 z.2 j * G j z) +
                            reverseTimeScalarCoefficient r₁ c z.1 z.2 * U z -
                            reverseTimeScalarCoefficient r₁ F z.1 z.2
                          ParabolicMemLpOn (Set.Ioo τ₁ τ₂ ×ˢ O)
                              (2 : ℝ≥0∞) W ∧
                            HasWeakTimeDerivOn (Set.Ioo τ₁ τ₂ ×ˢ O) U W := by
    obtain ⟨δ, hδ, hcarrier, hprev⟩ : ∃ (δ : ℝ) (hδ : 0 < δ)
          (hcarrier : spatialCoordinateShiftCarrier (tsupport χ.toFun) δ ⊆ Ω),
        ∀ (τ₀ τ₁ τ₂ τ₃ : ℝ)
          (hτ₀ : 0 < τ₀) (hτ₀τ₁ : τ₀ < τ₁)
          (hτ₁τ₂ : τ₁ < τ₂) (hτ₂τ₃ : τ₂ < τ₃)
          (hτ₃ : τ₃ < r₁ - r₀),
        ∀ (lam Lam M : ℝ) (hlam : 0 < lam)
          (hlamLam : lam ≤ Lam) (hM : 0 ≤ M),
          ∃ C_cac : ℝ, 0 ≤ C_cac ∧
            ∀ (a : CoefficientField d)
              (b : ℝ → PDE.Vec d → PDE.Vec d)
              (c F : ℝ → PDE.Vec d → ℝ),
            ∀ (haSmooth : IsSmoothOnNeighborhood
                  (fun z : TimeVelocity d => a z.1 z.2)
                  (scalarParabolicClosedCylinder r₀ r₁ Ω))
              (hbSmooth : IsSmoothOnNeighborhood
                  (fun z : TimeVelocity d => b z.1 z.2)
                  (scalarParabolicClosedCylinder r₀ r₁ Ω))
              (hcSmooth : IsSmoothOnNeighborhood
                  (fun z : TimeVelocity d => c z.1 z.2)
                  (scalarParabolicClosedCylinder r₀ r₁ Ω))
              (hFSmooth : IsSmoothOnNeighborhood
                  (fun z : TimeVelocity d => F z.1 z.2)
                  (scalarParabolicClosedCylinder r₀ r₁ Ω))
              (hLower : ∀ z : TimeVelocity d,
                  z ∈ scalarParabolicClosedCylinder r₀ r₁ Ω →
                    lam • (1 : PDE.Mat d) ≤ a z.1 z.2)
              (hUpper : ∀ z : TimeVelocity d,
                  z ∈ scalarParabolicClosedCylinder r₀ r₁ Ω →
                    a z.1 z.2 ≤ Lam • (1 : PDE.Mat d))
              (hcNonpos : ∀ z : TimeVelocity d,
                  z ∈ scalarParabolicClosedCylinder r₀ r₁ Ω →
                    c z.1 z.2 ≤ 0)
              (hA : ∀ z ∈ Set.Icc 0 (r₁ - r₀) ×ˢ
                  spatialCoordinateShiftCarrier (tsupport χ.toFun) δ,
                  spatialMatrixFDerivFrobeniusNorm
                    (fun w : TimeVelocity d =>
                      reverseTimeCoefficient r₁ a w.1 w.2) z ≤ M)
              (hB : ∀ z ∈ Set.Icc 0 (r₁ - r₀) ×ˢ
                  spatialCoordinateShiftCarrier (tsupport χ.toFun) δ,
                  PDE.vecEuclideanNorm
                    (reverseTimeDivergenceDrift r₁ a b z.1 z.2) ≤ M)
              (hBD : ∀ z ∈ Set.Icc 0 (r₁ - r₀) ×ˢ
                  spatialCoordinateShiftCarrier (tsupport χ.toFun) δ,
                  spatialVectorFDerivFrobeniusNorm
                    (fun w : TimeVelocity d =>
                      reverseTimeDivergenceDrift r₁ a b w.1 w.2) z ≤ M)
              (hq : ∀ z ∈ Set.Icc 0 (r₁ - r₀) ×ˢ
                  spatialCoordinateShiftCarrier (tsupport χ.toFun) δ,
                  |-(reverseTimeScalarCoefficient r₁ c z.1 z.2)| ≤ M)
              (hqD : ∀ z ∈ Set.Icc 0 (r₁ - r₀) ×ˢ
                  spatialCoordinateShiftCarrier (tsupport χ.toFun) δ,
                  spatialScalarFDerivEuclideanNorm
                    (fun w : TimeVelocity d =>
                      -(reverseTimeScalarCoefficient r₁ c w.1 w.2)) z ≤ M)
              (hfD : ∀ z ∈ Set.Icc 0 (r₁ - r₀) ×ˢ
                  spatialCoordinateShiftCarrier (tsupport χ.toFun) δ,
                  spatialScalarFDerivEuclideanNorm
                    (fun w : TimeVelocity d =>
                      -(reverseTimeScalarCoefficient r₁ F w.1 w.2)) z ≤ M),
            ∀ (initial : PDE.ScalarLp Ω (2 : ℝ≥0∞))
              (u : ReverseTimeL2V hΩ (r₁ - r₀))
              (g : ReverseTimeL2VStar hΩ (r₁ - r₀))
              (hdu : HasGelfandWeakTimeDerivative hΩ (r₁ - r₀)
                (sub_pos.mpr h₀₁) u g)
              (hu : IsReverseTimeVariationalEnergySolution
                r₀ r₁ h₀₁ hΩ hΩbounded a b c F hFSmooth initial u g hdu),
              ∃ G : Fin d → TimeVelocity d → ℝ,
                (∀ j, MemLp (G j) (2 : ℝ≥0∞)
                  (timeVelocityVolumeOn
                    (reverseTimeOpenInterval (r₁ - r₀) ×ˢ Ω))) ∧
                (∀ᵐ τ ∂reverseTimeVolume (r₁ - r₀), ∀ j,
                  (fun y => G j (τ, y)) =ᵐ[PDE.volumeOn Ω]
                    fun y => gradientCLM hΩ (u τ) y j) ∧
                ∃ H : TimeVelocity d → PDE.Mat d,
                  ∃ hHmem : ∀ j k : Fin d,
                      ParabolicMemLpOn (Set.Ioo τ₁ τ₂ ×ˢ O)
                        (2 : ℝ≥0∞) (fun z => H z j k),
                    (∀ j k : Fin d,
                      HasWeakVelocityPartialDerivOn
                        (Set.Ioo τ₁ τ₂ ×ˢ O) k (G j) (fun z => H z j k)) ∧
                    ∀ j k : Fin d,
                      ‖(hHmem j k).toLp (fun z => H z j k)‖ ≤
                        Real.sqrt
                          (C_cac *
                            ((r₁ - r₀) +
                              (reverseTimeGalerkinPrimalRadius
                                r₀ r₁ lam h₀₁ hlam hΩ hΩbounded a b c F
                                haSmooth hbSmooth hcSmooth hFSmooth hLower hcNonpos
                                initial) ^ 2)) := by
      obtain ⟨δ, hδ, hcarrier, hraw⟩ :=
        exists_gradientCoord_representatives_uniform_interiorSpatialDifferenceQuotient_caccioppoli
          hd r₀ r₁ h₀₁ hΩ hΩbounded hOopen hOnonempty subset_closure η χ
      refine ⟨δ, hδ, hcarrier, ?_⟩
      intro τ₀ τ₁ τ₂ τ₃ hτ₀ hτ₀τ₁ hτ₁τ₂ hτ₂τ₃ hτ₃ lam Lam M hlam hlamLam hM
      obtain ⟨C_cac, hC_cac, hraw'⟩ :=
        hraw τ₀ τ₁ τ₂ τ₃ hτ₀ hτ₀τ₁ hτ₁τ₂ hτ₂τ₃ hτ₃ lam Lam M hlam hlamLam hM
      refine ⟨C_cac, hC_cac, ?_⟩
      intro a b c F haSmooth hbSmooth hcSmooth hFSmooth hLower hUpper hcNonpos
        hA hB hBD hq hqD hfD initial u g hdu hu
      obtain ⟨G, hGmem, hGslice, hDQmem, _, hDQnorm⟩ :=
        hraw' a b c F haSmooth hbSmooth hcSmooth hFSmooth hLower hUpper hcNonpos
          hA hB hBD hq hqD hfD initial u g hdu hu
      refine ⟨G, hGmem, hGslice, ?_⟩
      let Qin := Set.Ioo τ₁ τ₂ ×ˢ O
      let B : ℝ := C_cac * ((r₁ - r₀) +
        (reverseTimeGalerkinPrimalRadius r₀ r₁ lam h₀₁ hlam hΩ hΩbounded
          a b c F haSmooth hbSmooth hcSmooth hFSmooth hLower hcNonpos initial) ^ 2)
      have hQinOpen : IsOpen Qin := isOpen_Ioo.prod hOopen
      have hOΩ := subset_closure.trans η.inner_subset_outer
      have htime : Set.Ioo τ₁ τ₂ ⊆ reverseTimeOpenInterval (r₁ - r₀) := by
        intro τ hτ
        exact ⟨hτ₀.trans (hτ₀τ₁.trans hτ.1),
          hτ.2.trans (hτ₂τ₃.trans hτ₃)⟩
      have hQin :=
        Set.prod_mono htime hOΩ
      have hGlocal : ∀ j, ParabolicMemLpOn Qin (2 : ℝ≥0∞) (G j) := by
        intro j
        exact (hGmem j).mono_measure (Measure.restrict_mono_set volume hQin)
      have hclose : ∀ j k : Fin d, ∃ entry : TimeVelocity d → ℝ,
          ∃ hentry : ParabolicMemLpOn Qin (2 : ℝ≥0∞) entry,
            HasWeakVelocityPartialDerivOn Qin k (G j) entry ∧
              ‖hentry.toLp entry‖ ≤ Real.sqrt B := by
        intro j k
        exact exists_hasWeakVelocityPartialDerivOn_norm_le_of_uniform_spatialDifferenceQuotient
          Qin hQinOpen k (G j) (hGlocal j) δ (Real.sqrt B) hδ
            (hDQmem j k) (hDQnorm j k)
      choose entry hentry hweak hnorm using hclose
      let H : TimeVelocity d → PDE.Mat d := fun z j k => entry j k z
      let hHmem : ∀ j k : Fin d,
          ParabolicMemLpOn Qin (2 : ℝ≥0∞) (fun z => H z j k) := fun j k => hentry j k
      refine ⟨H, hHmem, ?_, ?_⟩
      · intro j k
        exact hweak j k
      · intro j k
        exact hnorm j k
    refine ⟨δ, hδ, hcarrier, ?_⟩
    intro τ₀ τ₁ τ₂ τ₃ hτ₀ hτ₀τ₁ hτ₁τ₂ hτ₂τ₃ hτ₃ lam Lam M hlam hlamLam hM
    obtain ⟨C_cac, hC_cac, hprevC⟩ :=
      hprev τ₀ τ₁ τ₂ τ₃ hτ₀ hτ₀τ₁ hτ₁τ₂ hτ₂τ₃ hτ₃ lam Lam M hlam hlamLam hM
    refine ⟨C_cac, hC_cac, ?_⟩
    intro a b c F haSmooth hbSmooth hcSmooth hFSmooth hLower hUpper hcNonpos
      hA hB hBD hq hqD hfD initial u g hdu hu
    obtain ⟨G, hG, hGslice, H, hHmem, hHweak, hHbound⟩ :=
      hprevC a b c F haSmooth hbSmooth hcSmooth hFSmooth hLower hUpper hcNonpos
        hA hB hBD hq hqD hfD initial u g hdu hu
    refine ⟨G, hG, H, hHmem, hHweak, hHbound, ?_⟩
    obtain ⟨U, hU, hUslice⟩ := exists_reverseTimeL2V_value_product_representative hΩ (r₁ - r₀) u
    have hslice : ∀ᵐ τ ∂reverseTimeVolume (r₁ - r₀),
        ((fun y => U (τ, y)) =ᵐ[PDE.volumeOn Ω]
          fun y => valueCLM hΩ (u τ) y) ∧
        (∀ j, (fun y => G j (τ, y)) =ᵐ[PDE.volumeOn Ω]
          fun y => gradientCLM hΩ (u τ) y j) := by
      filter_upwards [hUslice, hGslice] with τ hUτ hGτ
      exact ⟨hUτ, hGτ⟩
    have htime : Set.Ioo τ₁ τ₂ ⊆ reverseTimeOpenInterval (r₁ - r₀) := by
      intro τ hτ
      exact ⟨hτ₀.trans (hτ₀τ₁.trans hτ.1), hτ.2.trans (hτ₂τ₃.trans hτ₃)⟩
    have hOΩ := subset_closure.trans η.inner_subset_outer
    have hUGlobal :=
      reverseTime_hasWeakVelocityPartialDerivOn_of_product_representatives
        hΩ (r₁ - r₀) u U hU hUslice G hG hGslice
    have hUweak : ∀ j : Fin d,
        HasWeakVelocityPartialDerivOn (Set.Ioo τ₁ τ₂ ×ˢ O) j U (G j) := by
      intro j
      exact (hUGlobal j).restrict (Set.prod_mono htime hOΩ)
    let W : TimeVelocity d → ℝ := fun z =>
      (∑ i : Fin d, ∑ j : Fin d,
        reverseTimeCoefficient r₁ a z.1 z.2 i j * H z j i) +
      (∑ j : Fin d, reverseTimeVectorCoefficient r₁ b z.1 z.2 j * G j z) +
      reverseTimeScalarCoefficient r₁ c z.1 z.2 * U z -
      reverseTimeScalarCoefficient r₁ F z.1 z.2
    have hUlocal :=
      hU.mono_measure
        (Measure.restrict_mono_set volume (Set.prod_mono htime hOΩ))
    have hGlocal : ∀ j,
        ParabolicMemLpOn (Set.Ioo τ₁ τ₂ ×ˢ O) (2 : ℝ≥0∞) (G j) := fun j =>
      (hG j).mono_measure
        (Measure.restrict_mono_set volume (Set.prod_mono htime hOΩ))
    have hW :=
      hessianTimeDerivative_memLp r₀ r₁ τ₁ τ₂ hΩ hΩbounded hOopen hOΩ htime
        a b c F haSmooth hbSmooth hcSmooth hFSmooth U hUlocal G hGlocal H hHmem
    have hsep : ∀ (eta : OriginalTimeScalarTest τ₁ τ₂)
          (psi : PDE.WeakTestFunction O),
        (∫ z in Set.Ioo τ₁ τ₂ ×ˢ O,
            U z * (eta.deriv z.1 * psi z.2)
            ∂(volume : Measure (TimeVelocity d))) =
          -∫ z in Set.Ioo τ₁ τ₂ ×ˢ O,
            ((∑ i : Fin d, ∑ j : Fin d,
                reverseTimeCoefficient r₁ a z.1 z.2 i j * H z j i) +
              (∑ j : Fin d,
                reverseTimeVectorCoefficient r₁ b z.1 z.2 j * G j z) +
              reverseTimeScalarCoefficient r₁ c z.1 z.2 * U z -
              reverseTimeScalarCoefficient r₁ F z.1 z.2) *
              (eta z.1 * psi z.2)
            ∂(volume : Measure (TimeVelocity d)) := by
      intro eta psi
      let S : Set (TimeVelocity d) := Set.Ioo τ₁ τ₂ ×ˢ O
      let globalS : Set (TimeVelocity d) := reverseTimeOpenInterval (r₁ - r₀) ×ˢ Ω
      let μ : Measure (TimeVelocity d) := timeVelocityVolumeOn S
      let mass : TimeVelocity d → ℝ := fun z => U z * (eta.deriv z.1 * psi z.2)
      let grouped : Fin d → Fin d → TimeVelocity d → ℝ := fun i j z =>
        G j z * (reverseTimeCoefficient r₁ a z.1 z.2 i j *
            (eta z.1 * psi.partialDeriv i z.2) +
          (eta z.1 * psi z.2) *
            (fderiv ℝ (fun y : PDE.Vec d =>
              reverseTimeCoefficient r₁ a z.1 y i j) z.2) (PDE.basisVec i))
      let hessian : Fin d → Fin d → TimeVelocity d → ℝ := fun i j z =>
        H z j i * (reverseTimeCoefficient r₁ a z.1 z.2 i j * (eta z.1 * psi z.2))
      let drift : Fin d → TimeVelocity d → ℝ := fun j z =>
        reverseTimeVectorCoefficient r₁ b z.1 z.2 j * G j z * (eta z.1 * psi z.2)
      let scalar : TimeVelocity d → ℝ := fun z =>
        reverseTimeScalarCoefficient r₁ c z.1 z.2 * U z * (eta z.1 * psi z.2)
      let source : TimeVelocity d → ℝ := fun z =>
        reverseTimeScalarCoefficient r₁ F z.1 z.2 * (eta z.1 * psi z.2)
      have hSglobal : S ⊆ globalS := Set.prod_mono htime hOΩ
      have hGlocal (j : Fin d) : LocallyIntegrableOn (G j) S volume := by
        have hj : ParabolicMemLpOn S (2 : ℝ≥0∞) (G j) :=
          (hG j).mono_measure (Measure.restrict_mono_set volume hSglobal)
        exact hj.locallyIntegrableOn (by norm_num)
      have hHlocal (j i : Fin d) : LocallyIntegrableOn (fun z => H z j i) S volume :=
        (hHmem j i).locallyIntegrableOn (by norm_num)
      have hweighted (i j : Fin d) :=
        reverseTime_coefficient_weighted_weak_identity r₀ r₁ hOopen hOΩ τ₁ τ₂ htime a
          haSmooth (G j) (fun z => H z j i) (hGlocal j) (hHlocal j i) i j
          (hHweak j i) eta psi
      have hgrouped : ∀ i j : Fin d, Integrable (grouped i j) μ := by
        intro i j
        exact hweighted i j |>.1
      have hhessian : ∀ i j : Fin d, Integrable (hessian i j) μ := by
        intro i j
        exact hweighted i j |>.2.1
      have hweak : ∀ i j : Fin d,
          (∫ z, grouped i j z ∂μ) = -(∫ z, hessian i j z ∂μ) := by
        intro i j
        exact hweighted i j |>.2.2
      let etaGlobal := reverseTimeScalarTestOfLocal htime eta
      let psiGlobal := psi.mono hOΩ
      obtain ⟨hmassGlobal, hprincipalGlobal, hdriftDivGlobal, hscalarGlobal, hsourceGlobal⟩ :=
        raw_reverseTime_separated_product_families_integrable r₀ r₁ hΩ hΩbounded
          a b c F haSmooth hbSmooth hcSmooth hFSmooth U hU G hG etaGlobal psiGlobal
      have hμle : μ ≤ timeVelocityVolumeOn globalS := by
        exact Measure.restrict_mono hSglobal le_rfl
      have hmass : Integrable mass μ := by
        refine (hmassGlobal.mono_measure hμle).congr (ae_of_all _ fun z => ?_)
        simp only [mass, etaGlobal, psiGlobal, reverseTimeScalarTestOfLocal_deriv,
          PDE.WeakTestFunction.mono_apply]
        ring
      have hscalar : Integrable scalar μ := by
        refine (hscalarGlobal.mono_measure hμle).congr (ae_of_all _ fun z => ?_)
        simp only [scalar, etaGlobal, psiGlobal, reverseTimeScalarTestOfLocal_apply,
          PDE.WeakTestFunction.mono_apply]
        ring
      have hsource : Integrable source μ := by
        refine (hsourceGlobal.mono_measure hμle).congr (ae_of_all _ fun z => ?_)
        simp only [source, etaGlobal, psiGlobal, reverseTimeScalarTestOfLocal_apply,
          PDE.WeakTestFunction.mono_apply]
        ring
      have hdrift : ∀ j : Fin d, Integrable (drift j) μ := by
        intro j
        have hsumGrouped := integrable_finset_sum Finset.univ fun i _ => hgrouped i j
        have hprincipal (i : Fin d) : Integrable (fun z : TimeVelocity d =>
            reverseTimeCoefficient r₁ a z.1 z.2 i j * G j z *
              psi.partialDeriv i z.2 * eta z.1) μ := by
          simpa only [etaGlobal, psiGlobal, reverseTimeScalarTestOfLocal_apply,
            PDE.WeakTestFunction.mono_partialDeriv] using
            (hprincipalGlobal i j).mono_measure hμle
        have hsumPrincipal := integrable_finset_sum Finset.univ fun i _ => hprincipal i
        have hdiv := (hdriftDivGlobal j).mono_measure hμle
        apply (hsumGrouped.sub hsumPrincipal |>.sub hdiv).congr
        filter_upwards [ae_restrict_mem ((isOpen_Ioo.prod hOopen).measurableSet)] with z hz
        simp only [drift, grouped, etaGlobal, psiGlobal,
          reverseTimeScalarTestOfLocal_apply, PDE.WeakTestFunction.mono_apply,
          reverseTimeDivergenceDrift,
          scalarSpatialCoefficientDivergence, reverseTimeVectorCoefficient_apply, Pi.sub_apply]
        have hd : G j z * eta z.1 * psi z.2 *
              (∑ i : Fin d, (fderiv ℝ (fun y =>
                reverseTimeCoefficient r₁ a z.1 y i j) z.2) (PDE.basisVec i)) =
            ∑ i : Fin d, G j z * eta z.1 * psi z.2 *
              (fderiv ℝ (fun y => reverseTimeCoefficient r₁ a z.1 y i j) z.2)
                (PDE.basisVec i) := by
          rw [Finset.mul_sum]
        ring_nf at hd ⊢
        rw [Finset.sum_add_distrib]
        rw [hd]
        ring
      have hrawAccepted :=
        reverseTime_separated_product_distribution_of_reverseTimeVariationalEnergy
          r₀ r₁ h₀₁ hΩ hΩbounded hOopen hOΩ τ₁ τ₂ htime a b c F haSmooth hbSmooth
          hcSmooth hFSmooth initial u g hdu hu U hU hUslice G hG hGslice eta psi
      have hraw : (∫ z, mass z -
            (∑ i : Fin d, ∑ j : Fin d, grouped i j z) +
            (∑ j : Fin d, drift j z) + scalar z - source z ∂μ) = 0 := by
        rw [← hrawAccepted.2]
        apply integral_congr_ae
        filter_upwards [ae_restrict_mem ((isOpen_Ioo.prod hOopen).measurableSet)] with z hz
        simp only [mass, grouped, drift, scalar, source,
          reverseTimeDivergenceDrift,
          scalarSpatialCoefficientDivergence, reverseTimeVectorCoefficient_apply, Pi.sub_apply]
        have hd (j : Fin d) : psi z.2 * eta z.1 *
              (∑ i : Fin d, (fderiv ℝ (fun y =>
                reverseTimeCoefficient r₁ a z.1 y i j) z.2) (PDE.basisVec i)) * G j z =
            ∑ i : Fin d, psi z.2 * eta z.1 *
              (fderiv ℝ (fun y => reverseTimeCoefficient r₁ a z.1 y i j) z.2)
                (PDE.basisVec i) * G j z := by
          rw [Finset.mul_sum, Finset.sum_mul]
        ring_nf at hd ⊢
        have hdsum :
            (∑ j : Fin d, psi z.2 * eta z.1 *
                (∑ i : Fin d, (fderiv ℝ (fun y =>
                  reverseTimeCoefficient r₁ a z.1 y i j) z.2) (PDE.basisVec i)) * G j z) =
              ∑ j : Fin d, ∑ i : Fin d, psi z.2 * eta z.1 * G j z *
                (fderiv ℝ (fun y => reverseTimeCoefficient r₁ a z.1 y i j) z.2)
                  (PDE.basisVec i) := by
          exact Finset.sum_congr rfl (fun j _ => hd j)
        ring_nf at hdsum
        rw [Finset.sum_comm] at hdsum
        have hd2 (j : Fin d) : eta z.1 *
              (∑ i : Fin d, psi z.2 *
                (fderiv ℝ (fun y => reverseTimeCoefficient r₁ a z.1 y i j) z.2)
                  (PDE.basisVec i) * G j z) =
            psi z.2 * eta z.1 *
              (∑ i : Fin d, (fderiv ℝ (fun y =>
                reverseTimeCoefficient r₁ a z.1 y i j) z.2) (PDE.basisVec i)) * G j z := by
          rw [Finset.mul_sum, hd j]
          apply Finset.sum_congr rfl
          intro i _
          ring
        have houter :
            (∑ j : Fin d, eta z.1 *
                (∑ i : Fin d, psi z.2 *
                  (fderiv ℝ (fun y => reverseTimeCoefficient r₁ a z.1 y i j) z.2)
                    (PDE.basisVec i) * G j z)) =
              ∑ j : Fin d, psi z.2 * eta z.1 *
                (∑ i : Fin d, (fderiv ℝ (fun y =>
                  reverseTimeCoefficient r₁ a z.1 y i j) z.2) (PDE.basisVec i)) * G j z := by
          exact Finset.sum_congr rfl (fun j _ => hd2 j)
        have hp :
            (∑ i : Fin d, ∑ j : Fin d, eta z.1 * G j z *
                reverseTimeCoefficient r₁ a z.1 z.2 i j * psi.partialDeriv i z.2) =
              ∑ i : Fin d, ∑ j : Fin d, eta z.1 *
                reverseTimeCoefficient r₁ a z.1 z.2 i j * G j z *
                  psi.partialDeriv i z.2 := by
          apply Finset.sum_congr rfl
          intro i _
          apply Finset.sum_congr rfl
          intro j _
          ring
        have hbraw :
            (∑ j : Fin d, psi z.2 * eta z.1 * b (r₁ - z.1) z.2 j * G j z) =
              ∑ j : Fin d, psi z.2 * eta z.1 * G j z * b (r₁ - z.1) z.2 j := by
          apply Finset.sum_congr rfl
          intro j _
          ring
        have hrhs :
            (∑ j : Fin d, eta z.1 *
                ((∑ i : Fin d, psi z.2 *
                  (fderiv ℝ (fun y => reverseTimeCoefficient r₁ a z.1 y i j) z.2)
                    (PDE.basisVec i) * G j z) -
                  psi z.2 * b (r₁ - z.1) z.2 j * G j z)) =
              (∑ j : Fin d, eta z.1 * (∑ i : Fin d, psi z.2 *
                (fderiv ℝ (fun y => reverseTimeCoefficient r₁ a z.1 y i j) z.2)
                  (PDE.basisVec i) * G j z)) -
                ∑ j : Fin d, psi z.2 * eta z.1 * G j z * b (r₁ - z.1) z.2 j := by
          calc
            _ = ∑ j : Fin d, (eta z.1 * (∑ i : Fin d, psi z.2 *
                  (fderiv ℝ (fun y => reverseTimeCoefficient r₁ a z.1 y i j) z.2)
                    (PDE.basisVec i) * G j z) -
                psi z.2 * eta z.1 * G j z * b (r₁ - z.1) z.2 j) := by
                  apply Finset.sum_congr rfl
                  intro j _
                  ring
            _ = _ := by rw [Finset.sum_sub_distrib]
        simp_rw [Finset.sum_add_distrib]
        simp_rw [Finset.mul_sum, Finset.sum_mul]
        rw [hrhs]
        rw [← hdsum]
        rw [← houter]
        rw [hp, hbraw]
        ring
      have halgebra : (∫ x, mass x ∂μ) =
        -(∫ x,
          (∑ i : Fin d, ∑ j : Fin d, hessian i j x) +
          (∑ j : Fin d, drift j x) + scalar x - source x ∂μ) := by
        have hgroupedSum : Integrable
            (fun x => ∑ i : Fin d, ∑ j : Fin d, grouped i j x) μ :=
          integrable_finset_sum Finset.univ fun i _ =>
            integrable_finset_sum Finset.univ fun j _ => hgrouped i j
        have hhessianSum : Integrable
            (fun x => ∑ i : Fin d, ∑ j : Fin d, hessian i j x) μ :=
          integrable_finset_sum Finset.univ fun i _ =>
            integrable_finset_sum Finset.univ fun j _ => hhessian i j
        have hdriftSum : Integrable (fun x => ∑ j : Fin d, drift j x) μ :=
          integrable_finset_sum Finset.univ fun j _ => hdrift j
        have hgroupedIntegral :
            (∫ x, ∑ i : Fin d, ∑ j : Fin d, grouped i j x ∂μ) =
              ∑ i : Fin d, ∑ j : Fin d, ∫ x, grouped i j x ∂μ := by
          rw [integral_finset_sum Finset.univ (fun i _ =>
            integrable_finset_sum Finset.univ fun j _ => hgrouped i j)]
          simp_rw [integral_finset_sum Finset.univ (fun j _ => hgrouped _ j)]
        have hdriftIntegral :
            (∫ x, ∑ j : Fin d, drift j x ∂μ) =
              ∑ j : Fin d, ∫ x, drift j x ∂μ :=
          integral_finset_sum Finset.univ fun j _ => hdrift j
        have hraw' :
            (∫ x, mass x ∂μ) -
              (∑ i : Fin d, ∑ j : Fin d, ∫ x, grouped i j x ∂μ) +
              (∑ j : Fin d, ∫ x, drift j x ∂μ) +
              (∫ x, scalar x ∂μ) - (∫ x, source x ∂μ) = 0 := by
          have e₁ :=
            integral_sub hmass hgroupedSum
          have e₂ : (∫ x, mass x - (∑ i : Fin d, ∑ j : Fin d, grouped i j x) +
              (∑ j : Fin d, drift j x) ∂μ) =
              ((∫ x, mass x ∂μ) - ∫ x, ∑ i : Fin d, ∑ j : Fin d, grouped i j x ∂μ) +
                ∫ x, ∑ j : Fin d, drift j x ∂μ := by
            calc
              _ = (∫ x, mass x - (∑ i : Fin d, ∑ j : Fin d, grouped i j x) ∂μ) +
                  ∫ x, ∑ j : Fin d, drift j x ∂μ := by
                simpa only [Pi.sub_apply, Pi.add_apply] using
                  integral_add (hmass.sub hgroupedSum) hdriftSum
              _ = _ := by rw [e₁]
          have e₃ : (∫ x, mass x - (∑ i : Fin d, ∑ j : Fin d, grouped i j x) +
              (∑ j : Fin d, drift j x) + scalar x ∂μ) =
              (((∫ x, mass x ∂μ) - ∫ x, ∑ i : Fin d, ∑ j : Fin d, grouped i j x ∂μ) +
                ∫ x, ∑ j : Fin d, drift j x ∂μ) + ∫ x, scalar x ∂μ := by
            calc
              _ = (∫ x, mass x - (∑ i : Fin d, ∑ j : Fin d, grouped i j x) +
                  (∑ j : Fin d, drift j x) ∂μ) + ∫ x, scalar x ∂μ := by
                simpa only [Pi.sub_apply, Pi.add_apply] using
                  integral_add ((hmass.sub hgroupedSum).add hdriftSum) hscalar
              _ = _ := by rw [e₂]
          have e₄ : (∫ x, mass x - (∑ i : Fin d, ∑ j : Fin d, grouped i j x) +
              (∑ j : Fin d, drift j x) + scalar x - source x ∂μ) =
              ((((∫ x, mass x ∂μ) - ∫ x, ∑ i : Fin d, ∑ j : Fin d, grouped i j x ∂μ) +
                ∫ x, ∑ j : Fin d, drift j x ∂μ) + ∫ x, scalar x ∂μ) -
                ∫ x, source x ∂μ := by
            calc
              _ = (∫ x, mass x - (∑ i : Fin d, ∑ j : Fin d, grouped i j x) +
                  (∑ j : Fin d, drift j x) + scalar x ∂μ) - ∫ x, source x ∂μ := by
                simpa only [Pi.sub_apply, Pi.add_apply] using
                  integral_sub (((hmass.sub hgroupedSum).add hdriftSum).add hscalar) hsource
              _ = _ := by rw [e₃]
          rw [← hgroupedIntegral, ← hdriftIntegral, ← e₄]
          exact hraw
        have hweakSum :
            (∑ i : Fin d, ∑ j : Fin d, ∫ x, grouped i j x ∂μ) =
              -(∑ i : Fin d, ∑ j : Fin d, ∫ x, hessian i j x ∂μ) := by
          simp_rw [hweak]
          simp only [Finset.sum_neg_distrib]
        have hhessianIntegral :
            (∫ x, ∑ i : Fin d, ∑ j : Fin d, hessian i j x ∂μ) =
              ∑ i : Fin d, ∑ j : Fin d, ∫ x, hessian i j x ∂μ := by
          rw [integral_finset_sum Finset.univ (fun i _ =>
            integrable_finset_sum Finset.univ fun j _ => hhessian i j)]
          simp_rw [integral_finset_sum Finset.univ (fun j _ => hhessian _ j)]
        have hright :
            (∫ x, (∑ i : Fin d, ∑ j : Fin d, hessian i j x) +
                (∑ j : Fin d, drift j x) + scalar x - source x ∂μ) =
              ((∑ i : Fin d, ∑ j : Fin d, ∫ x, hessian i j x ∂μ) +
                (∑ j : Fin d, ∫ x, drift j x ∂μ) + ∫ x, scalar x ∂μ) -
                ∫ x, source x ∂μ := by
          calc
            _ = (∫ x, (∑ i : Fin d, ∑ j : Fin d, hessian i j x) +
                (∑ j : Fin d, drift j x) + scalar x ∂μ) - ∫ x, source x ∂μ := by
              simpa only [Pi.sub_apply, Pi.add_apply] using
                integral_sub ((hhessianSum.add hdriftSum).add hscalar) hsource
            _ = (((∫ x, ∑ i : Fin d, ∑ j : Fin d, hessian i j x ∂μ) +
                ∫ x, ∑ j : Fin d, drift j x ∂μ) + ∫ x, scalar x ∂μ) -
                ∫ x, source x ∂μ := by
              rw [show (∫ x, (∑ i : Fin d, ∑ j : Fin d, hessian i j x) +
                  (∑ j : Fin d, drift j x) + scalar x ∂μ) =
                  (∫ x, (∑ i : Fin d, ∑ j : Fin d, hessian i j x) +
                    (∑ j : Fin d, drift j x) ∂μ) + ∫ x, scalar x ∂μ from by
                    simpa only [Pi.add_apply] using integral_add (hhessianSum.add hdriftSum) hscalar]
              rw [show (∫ x, (∑ i : Fin d, ∑ j : Fin d, hessian i j x) +
                  (∑ j : Fin d, drift j x) ∂μ) =
                  (∫ x, ∑ i : Fin d, ∑ j : Fin d, hessian i j x ∂μ) +
                    ∫ x, ∑ j : Fin d, drift j x ∂μ from by
                      simpa only [Pi.add_apply] using integral_add hhessianSum hdriftSum]
            _ = _ := by rw [hhessianIntegral, hdriftIntegral]
        rw [hright]
        rw [hweakSum] at hraw'
        linarith
      calc
        _ = -(∫ z, (∑ i : Fin d, ∑ j : Fin d, hessian i j z) +
            (∑ j : Fin d, drift j z) + scalar z - source z ∂μ) := halgebra
        _ = _ := by
          congr 2
          funext z
          simp only [hessian, drift, scalar, source]
          have hh : (eta z.1 * psi z.2) *
                (∑ i : Fin d, ∑ j : Fin d,
                  reverseTimeCoefficient r₁ a z.1 z.2 i j * H z j i) =
              ∑ i : Fin d, ∑ j : Fin d,
                (eta z.1 * psi z.2) *
                  (reverseTimeCoefficient r₁ a z.1 z.2 i j * H z j i) := by
            rw [Finset.mul_sum]
            congr 1
            funext i
            rw [Finset.mul_sum]
          have hb : (eta z.1 * psi z.2) *
                (∑ j : Fin d, reverseTimeVectorCoefficient r₁ b z.1 z.2 j * G j z) =
              ∑ j : Fin d, (eta z.1 * psi z.2) *
                (reverseTimeVectorCoefficient r₁ b z.1 z.2 j * G j z) := by
            rw [Finset.mul_sum]
          have hhcomm :
              (∑ i : Fin d, ∑ j : Fin d,
                (eta z.1 * psi z.2) * H z j i *
                  reverseTimeCoefficient r₁ a z.1 z.2 i j) =
              ∑ i : Fin d, ∑ j : Fin d,
                (eta z.1 * psi z.2) *
                  reverseTimeCoefficient r₁ a z.1 z.2 i j * H z j i := by
            apply Finset.sum_congr rfl
            intro i _
            apply Finset.sum_congr rfl
            intro j _
            ring
          ring_nf at hh hb hhcomm ⊢
          rw [hh, hb, hhcomm]
          ring
    have hWweak :=
      hasWeakTimeDerivOn_of_forall_separatedProduct hOopen hUlocal hW (by
        intro eta psi
        simpa only [W] using hsep eta psi)
    exact ⟨U, hU, hslice, hUweak, hW, hWweak⟩
  obtain ⟨M, hM, hA, hB, hBD, hq, hqD, hfD⟩ :=
    exists_reverseTimeInteriorCoefficientMajorant r₀ r₁ χ δ hcarrier
      a b c F haSmooth hbSmooth hcSmooth hFSmooth
  obtain ⟨C_cac, hC_cac, hrun⟩ :=
    hpredecessor _ _ _ _ hτ₀ hτ₀τ₁ hτ₁τ₂ hτ₂τ₃ hτ₃
      lam Lam M hlam hlamLam hM
  obtain ⟨G, hG, H, hHmem, hHweak, _hHbound, U, hU, hUslice, hUweak,
      hWmem, hWweak⟩ :=
    hrun a b c F haSmooth hbSmooth hcSmooth hFSmooth hLower hUpper hcNonpos
      hA hB hBD hq hqD hfD initial u g hdu hu
  let Q : Set (TimeVelocity d) := Set.Ioo (r₁ - s₁) (r₁ - s₀) ×ˢ O
  let W : TimeVelocity d → ℝ := fun z =>
    (∑ i : Fin d, ∑ j : Fin d,
      reverseTimeCoefficient r₁ a z.1 z.2 i j * H z j i) +
    (∑ j : Fin d, reverseTimeVectorCoefficient r₁ b z.1 z.2 j * G j z) +
    reverseTimeScalarCoefficient r₁ c z.1 z.2 * U z -
    reverseTimeScalarCoefficient r₁ F z.1 z.2
  have htime : Set.Ioo (r₁ - s₁) (r₁ - s₀) ⊆
      reverseTimeOpenInterval (r₁ - r₀) := by
    intro τ hτ
    exact ⟨hτ₀.trans (hτ₀τ₁.trans hτ.1),
      hτ.2.trans (hτ₂τ₃.trans hτ₃)⟩
  have hOΩ' : O ⊆ Ω := subset_closure.trans hOΩ
  have hQglobal : Q ⊆ reverseTimeOpenInterval (r₁ - r₀) ×ˢ Ω :=
    Set.prod_mono htime hOΩ'
  have hUlocal : ParabolicMemLpOn Q (2 : ℝ≥0∞) U :=
    hU.mono_measure (Measure.restrict_mono_set volume hQglobal)
  have hGlocal : ∀ j, ParabolicMemLpOn Q (2 : ℝ≥0∞) (G j) := fun j =>
    (hG j).mono_measure (Measure.restrict_mono_set volume hQglobal)
  let Jrev : ParabolicW12Function d Q (2 : ℝ≥0∞) :=
    { toFun := U
      timeDeriv := W
      velocityGrad := fun z j => G j z
      velocityHessian := H
      memLp := hUlocal
      timeDeriv_memLp := hWmem
      velocityGrad_memLp := hGlocal
      velocityHessian_memLp := hHmem
      hasWeakTimeDeriv := hWweak
      hasWeakVelocityPartialDeriv := hUweak
      hasWeakVelocitySecondPartialDeriv := hHweak }
  have hQmeas : MeasurableSet Q := measurableSet_Ioo.prod hOopen.measurableSet
  have hQreflect : reverseTimeMap r₁ ⁻¹' Q = Set.Ioo s₀ s₁ ×ˢ O := by
    simpa only [Q] using reverseTimeMap_preimage_originalTimeInteriorCylinder r₁ s₀ s₁ O
  let Jreflected := Jrev.timeReflect r₁ hQmeas
  let J : ParabolicW12Function d (Set.Ioo s₀ s₁ ×ˢ O) (2 : ℝ≥0∞) :=
    { toFun := fun z => U (reverseTimeMap r₁ z)
      timeDeriv := fun z => -W (reverseTimeMap r₁ z)
      velocityGrad := fun z j => G j (reverseTimeMap r₁ z)
      velocityHessian := fun z => H (reverseTimeMap r₁ z)
      memLp := by
        simpa only [Jreflected, ParabolicW12Function.timeReflect, Jrev, hQreflect]
          using Jreflected.memLp
      timeDeriv_memLp := by
        simpa only [Jreflected, ParabolicW12Function.timeReflect, Jrev, hQreflect]
          using Jreflected.timeDeriv_memLp
      velocityGrad_memLp := by
        intro i
        simpa only [Jreflected, ParabolicW12Function.timeReflect, Jrev, hQreflect]
          using Jreflected.velocityGrad_memLp i
      velocityHessian_memLp := by
        intro i j
        simpa only [Jreflected, ParabolicW12Function.timeReflect, Jrev, hQreflect]
          using Jreflected.velocityHessian_memLp i j
      hasWeakTimeDeriv := by
        simpa only [Jreflected, ParabolicW12Function.timeReflect, Jrev, hQreflect]
          using Jreflected.hasWeakTimeDeriv
      hasWeakVelocityPartialDeriv := by
        intro i
        simpa only [Jreflected, ParabolicW12Function.timeReflect, Jrev, hQreflect]
          using Jreflected.hasWeakVelocityPartialDeriv i
      hasWeakVelocitySecondPartialDeriv := by
        intro i j
        simpa only [Jreflected, ParabolicW12Function.timeReflect, Jrev, hQreflect] using
          Jreflected.hasWeakVelocitySecondPartialDeriv i j }
  refine ⟨J, ?_, ?_⟩
  · have hUreflectMem : MemLp (fun z => U (reverseTimeMap r₁ z)) (2 : ℝ≥0∞)
        (timeVelocityVolumeOn (Set.Ioo r₀ r₁ ×ˢ Ω)) := by
      have hglobal := reverseTimeMap_measurePreserving_restrict (d := d) r₁
        (U := reverseTimeOpenInterval (r₁ - r₀) ×ˢ Ω)
        ((measurableSet_Ioo.prod hΩ.measurableSet))
      have hglobalSet : reverseTimeMap r₁ ⁻¹'
          (reverseTimeOpenInterval (r₁ - r₀) ×ˢ Ω) =
          Set.Ioo r₀ r₁ ×ˢ Ω := by
        simpa only [reverseTimeOpenInterval, sub_self] using
          reverseTimeMap_preimage_originalTimeInteriorCylinder r₁ r₀ r₁ Ω
      simpa only [Function.comp_def, hglobalSet] using hU.comp_measurePreserving hglobal
    have hUreflectSlice : ∀ᵐ r ∂volume.restrict (Set.Ioo r₀ r₁),
        (fun y => U (reverseTimeMap r₁ (r, y))) =ᵐ[PDE.volumeOn Ω]
          fun y => valueCLM hΩ (u (r₁ - r)) y := by
      have hreflection : MeasurePreserving (fun r : ℝ => r₁ - r)
          (volume : Measure ℝ) volume := by
        simpa only [Function.comp_def, sub_eq_add_neg] using
          (measurePreserving_add_left (volume : Measure ℝ) r₁).comp
            (Measure.measurePreserving_neg (volume : Measure ℝ))
      have hpreimage : (fun r : ℝ => r₁ - r) ⁻¹' Set.Ioo 0 (r₁ - r₀) =
          Set.Ioo r₀ r₁ := by
        rw [preimage_const_sub_Ioo]
        congr 1 <;> ring
      have htimeReflect : MeasurePreserving (fun r : ℝ => r₁ - r)
          (volume.restrict (Set.Ioo r₀ r₁)) (reverseTimeVolume (r₁ - r₀)) := by
        rw [reverseTimeVolume, reverseTimeOpenInterval, ← hpreimage]
        exact hreflection.restrict_preimage isOpen_Ioo.measurableSet
      filter_upwards [htimeReflect.quasiMeasurePreserving.ae hUslice] with r hr
      simpa only [reverseTimeMap_apply] using hr.1
    have hUw : (fun z => U (reverseTimeMap r₁ z)) =ᵐ[timeVelocityVolumeOn (Set.Ioo r₀ r₁ ×ˢ Ω)] w := by
      let U := (fun z => U (reverseTimeMap r₁ z))
      have hU_meas := hUreflectMem.aemeasurable
      have hV_meas := hwmem.aemeasurable
      have hprod :
          (volume.restrict (Set.Ioo r₀ r₁)).prod (PDE.volumeOn Ω) =
            timeVelocityVolumeOn (Set.Ioo r₀ r₁ ×ˢ Ω) := by
        rw [timeVelocityVolumeOn, volume_timeVelocity_eq_prod]
        simpa only [PDE.volumeOn] using Measure.prod_restrict
          (μ := (volume : Measure ℝ)) (ν := (volume : Measure (PDE.Vec d)))
            (Set.Ioo r₀ r₁) Ω
      rw [← hprod] at hU_meas hV_meas ⊢
      let U' := hU_meas.mk U
      let V' := hV_meas.mk w
      have hUU' : U =ᵐ[(volume.restrict (Set.Ioo r₀ r₁)).prod (PDE.volumeOn Ω)] U' :=
        hU_meas.ae_eq_mk
      have hVV' : w =ᵐ[(volume.restrict (Set.Ioo r₀ r₁)).prod (PDE.volumeOn Ω)] V' :=
        hV_meas.ae_eq_mk
      have hUV : ∀ᵐ r ∂volume.restrict (Set.Ioo r₀ r₁),
          (fun y => U (r, y)) =ᵐ[PDE.volumeOn Ω] fun y => w (r, y) := by
        filter_upwards [hUreflectSlice, hwslice] with r hUr hVr
        exact hUr.trans hVr.symm
      have hU'U : ∀ᵐ r ∂volume.restrict (Set.Ioo r₀ r₁),
          (fun y => U' (r, y)) =ᵐ[PDE.volumeOn Ω] fun y => U (r, y) :=
        (Measure.ae_ae_eq_curry_of_prod hUU').mono fun _ hr => hr.symm
      have hVV'c :=
        Measure.ae_ae_eq_curry_of_prod hVV'
      have hU'V' : ∀ᵐ r ∂volume.restrict (Set.Ioo r₀ r₁),
          (fun y => U' (r, y)) =ᵐ[PDE.volumeOn Ω] fun y => V' (r, y) := by
        filter_upwards [hU'U, hUV, hVV'c] with r hU'Ur hUVr hVV'r
        exact hU'Ur.trans (hUVr.trans hVV'r)
      have hU'V'_meas : MeasurableSet {z | U' z = V' z} :=
        measurableSet_eq_fun hU_meas.measurable_mk hV_meas.measurable_mk
      have hU'V'prod :
          U' =ᵐ[(volume.restrict (Set.Ioo r₀ r₁)).prod (PDE.volumeOn Ω)] V' :=
        (Measure.ae_prod_iff_ae_ae hU'V'_meas).2 hU'V'
      exact hUU'.trans (hU'V'prod.trans hVV'.symm)
    have hlocal : (fun z => U (reverseTimeMap r₁ z)) =ᵐ[
        timeVelocityVolumeOn (Set.Ioo s₀ s₁ ×ˢ O)] w :=
      hUw.filter_mono (ae_mono (Measure.restrict_mono_set volume (by
        exact Set.prod_mono
          (Set.Ioo_subset_Ioo hr₀s₀.le hs₁r₁.le) hOΩ')))
    change (fun z => U (reverseTimeMap r₁ z)) =ᵐ[
      timeVelocityVolumeOn (Set.Ioo s₀ s₁ ×ˢ O)] w
    exact hlocal
  · filter_upwards [] with z
    change -W (reverseTimeMap r₁ z) +
          (∑ i : Fin d, ∑ j : Fin d, a z.1 z.2 i j * H (reverseTimeMap r₁ z) j i) +
        (∑ j : Fin d, b z.1 z.2 j * G j (reverseTimeMap r₁ z)) +
      c z.1 z.2 * U (reverseTimeMap r₁ z) = F z.1 z.2
    simp only [W, reverseTimeMap_apply, reverseTimeCoefficient,
      reverseTimeVectorCoefficient, reverseTimeScalarCoefficient, sub_sub_cancel]
    ring

/- A supplied reverse-time variational solution has one global original-time
value representative admitting compatible local anisotropic `L²` weak jets. -/
end HypoellipticAleksandrov.Parabolic.Dirichlet
