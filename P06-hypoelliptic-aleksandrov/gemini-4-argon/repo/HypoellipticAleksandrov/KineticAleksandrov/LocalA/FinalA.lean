module

public import HypoellipticAleksandrov.KineticAleksandrov.LocalA.AssemblyA
public import HypoellipticAleksandrov.KineticAleksandrov.LocalA.SmoothHolder
public import HypoellipticAleksandrov.KineticAleksandrov.LocalA.SpatialDerivatives
import HypoellipticAleksandrov.KineticAleksandrov.LocalA.SmoothHolderNormalized
import HypoellipticAleksandrov.KineticAleksandrov.LocalA.SmoothLocalStatement
import HypoellipticAleksandrov.KineticAleksandrov.Maximum.BorelSource
import HypoellipticAleksandrov.KineticAleksandrov.SectionTwo.Realization
import Mathlib.Analysis.Calculus.ContDiff.FTaylorSeries
import Mathlib.Tactic
import HypoellipticAleksandrov.KineticAleksandrov.Evolution.ExternalRegularity
import HypoellipticAleksandrov.KineticAleksandrov.Holder.Setting
import HypoellipticAleksandrov.KineticAleksandrov.LocalA.KineticPullbackJets
import HypoellipticAleksandrov.KineticAleksandrov.TheoremA.SmoothEstimateEllipticity
import HypoellipticAleksandrov.Parabolic.Scaling
import Mathlib.MeasureTheory.Measure.OpenPos
import HypoellipticAleksandrov.KineticAleksandrov.Holder.OscillationBasics
import HypoellipticAleksandrov.KineticAleksandrov.Holder.PairGeometryCompact
import HypoellipticAleksandrov.KineticAleksandrov.LocalA.KineticPullback
import HypoellipticAleksandrov.KineticAleksandrov.LocalA.ScalingSlices
import HypoellipticAleksandrov.KineticAleksandrov.LocalA.SmoothHolderGeometry
import HypoellipticAleksandrov.Parabolic.AffineScalarCalculus
import HypoellipticAleksandrov.Parabolic.KrylovEstimate.ScalarAffine
import HypoellipticAleksandrov.Parabolic.LocalHolder.ForcedIteration
import HypoellipticAleksandrov.Parabolic.LocalHolder.ForcedIterationDyadic
import HypoellipticAleksandrov.Parabolic.LocalHolder.ForcedIterationGeometric
import HypoellipticAleksandrov.Parabolic.LocalHolder.ForcedIterationGeometry
import HypoellipticAleksandrov.Parabolic.LocalHolder.HarnackOscillation
import HypoellipticAleksandrov.Parabolic.LocalHolder.HarnackOscillationGeometry
import HypoellipticAleksandrov.Parabolic.LocalHolder.HarnackOscillationScaling
import HypoellipticAleksandrov.Parabolic.LocalHolder.Holder
import HypoellipticAleksandrov.Parabolic.LocalHolder.HolderExponent
import HypoellipticAleksandrov.Parabolic.LocalHolder.HolderGeometry
import HypoellipticAleksandrov.Parabolic.LocalHolder.ReplacementForward
import HypoellipticAleksandrov.Statements.ParabolicHarnack
import Mathlib.Algebra.Order.Archimedean.Basic
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import HypoellipticAleksandrov.KineticAleksandrov.LocalA.ExitL1DerivativesFinal
import HypoellipticAleksandrov.KineticAleksandrov.LocalA.SpatialDerivativesReflection
import HypoellipticAleksandrov.KineticAleksandrov.LocalA.SpatialDerivativesForward
import HypoellipticAleksandrov.KineticAleksandrov.Maximum.InnerCylinderReflection

/-! # Time–velocity Hölder estimate from the proved spatial derivative bounds -/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.KineticAleksandrov
open Set MeasureTheory Holder LocalA
open scoped MatrixOrder

namespace LocalA
open Parabolic SectionTwo HypoellipticAleksandrov.KineticAleksandrov.LocalA
open scoped ContDiff Matrix.Norms.Elementwise
open Filter
open scoped Topology
open LocalHolder KineticAleksandrov.LocalA HypoellipticAleksandrov.Parabolic.LocalHolder HypoellipticAleksandrov.Parabolic

/- The joint smooth local statement follows from the spatial derivative theorem. -/
theorem smoothLocalRegularityStatement_holds : SmoothLocalRegularityStatement := by
  intro hH hLE d hd lam Lam hlam hLam
  obtain ⟨C_m, hCm, hspatial⟩ : ∃ C_m : ℕ → ℝ, (∀ m, 0 ≤ C_m m) ∧
      ∀ (A : CoefficientField d), IsSectionTwoCoefficient lam Lam A →
      ∀ (P₀ : KineticPoint d) (R : ℝ), 0 < R →
      ∀ (u : KineticPoint d → ℝ),
      ContinuousOn u (closure (backwardCylinder P₀ R)) →
      IsKineticC112On u (backwardCylinder P₀ R) →
      (∀ᵐ P ∂volume.restrict (backwardCylinder P₀ R),
        backwardOperatorOfTimeVelocityCoefficient A u P = 0) →
      (∀ P ∈ backwardCylinder P₀ R,
        ContDiffAt ℝ (⊤ : ℕ∞) (physicalPositionSlice u P) P.position) ∧
      ∀ (m : ℕ), 1 ≤ m → ∀ P ∈ backwardCylinder P₀ (3 * R / 4),
        R ^ (3 * m) * ‖iteratedFDeriv ℝ m (physicalPositionSlice u P) P.position‖ ≤
          C_m m * Holder.oscillationOn u (backwardCylinder P₀ R) := by
    obtain ⟨C, hC, hkernel⟩ : ∃ C : ℕ → ℝ, (∀ j, 0 ≤ C j) ∧
        ∀ (B : CoefficientField d) (hB : IsSectionTwoCoefficient lam Lam B)
          (v₀ : PDE.Vec d) (R : ℝ) (hR : 0 < R)
          (P : LocalBallStart v₀ R) (T : {t : ℝ // P.1.time < t}),
        P.1.velocity ∈ PDE.euclideanBall v₀ (3 * R / 4) →
        T.1 - P.1.time = R ^ 2 / 8 → ∀ j,
        (∫ y, ‖iteratedFDeriv ℝ j
          (exitL1Density (ballExit hH hLE hd hlam hLam B hB v₀ hR P T)) y‖) ≤
          C j * R ^ (-3 * (j : ℝ)) := by
      obtain ⟨D, hD, hb⟩ :=
        ballExitL1Inversion_uniform_derivative_bound hH hLE d hd lam Lam hlam hLam
      refine ⟨fun j => (2 : ℝ) ^ d * D j, fun j => mul_nonneg (by positivity) (hD j), ?_⟩
      intro B hB v₀ R hR P T hv hT j
      let G := exitL1Density (ballExit hH hLE hd hlam hLam B hB v₀ hR P T)
      have hbound (y : PDE.Vec d) : ‖iteratedFDeriv ℝ j G y‖ ≤
          D j * R ^ (-3 * ((d : ℝ) + (j : ℝ))) :=
        (ballExitL1Density_derivative_le hH hLE hd hlam hLam B hB v₀ hR P T hv hT j y).trans
          (hb B hB v₀ R hR P T hv hT j y)
      have hi := exitDerivative_integral_le_volume G hR
        (ballExitL1Density_zero_outside hH hLE hd hlam hLam B hB v₀ hR P T hv hT) j
        (mul_nonneg (hD j) (Real.rpow_nonneg hR.le _)) hbound
      have hp : R ^ (3 * d) * R ^ (-3 * ((d : ℝ) + (j : ℝ))) =
          R ^ (-3 * (j : ℝ)) := by
        rw [← Real.rpow_natCast R (3 * d), ← Real.rpow_add hR]
        congr 1
        push_cast
        ring
      calc
        _ ≤ ((2 : ℝ) ^ d * R ^ (3 * d)) *
            (D j * R ^ (-3 * ((d : ℝ) + (j : ℝ)))) := hi
        _ = ((2 : ℝ) ^ d * D j) *
            (R ^ (3 * d) * R ^ (-3 * ((d : ℝ) + (j : ℝ)))) := by ring
        _ = _ := by rw [hp]
    refine ⟨C, hC, ?_⟩
    intro A hA P₀ R hR u huc hus hue
    let B := kineticReflectedCoefficient A
    let U := u ∘ kineticReflection
    let Z₀ := kineticReflection P₀
    have hB := sectionTwo_coefficient_reflection hA
    obtain ⟨hUc, hUs, hUe⟩ :
        let U := u ∘ kineticReflection
            let Z₀ := kineticReflection P₀
            ContinuousOn U (closure (forwardCylinder Z₀ R hR)) ∧
              IsKineticC112On U (forwardCylinder Z₀ R hR) ∧
              ∀ Q ∈ forwardCylinder Z₀ R hR,
                forwardKineticOperator (ofTimeVelocityCoefficient (kineticReflectedCoefficient A)) U Q =
                  0 := by
      dsimp only
      have heq := spatial_backward_equation_pointwise (isOpen_backwardCylinder P₀ R hR)
        A (sectionTwo_coefficient_smooth hA) u hus hue
      refine ⟨?_, ?_, ?_⟩
      · rw [← TheoremA.preimage_closure_backwardCylinder_reflection P₀ R hR]
        exact huc.comp (continuous_kineticReflection d).continuousOn (fun _ h => h)
      · rw [← TheoremA.preimage_backwardCylinder_reflection P₀ R hR]
        exact isKineticC112On_kineticReflection u _ hus
      · intro Q hQ
        rw [reflectedKineticOperator_reflection, heq (kineticReflection Q) ?_, neg_zero]
        rw [← TheoremA.preimage_backwardCylinder_reflection P₀ R hR] at hQ
        exact hQ
    refine ⟨?_, ?_⟩
    · intro P hP
      have hp : kineticReflection P ∈ forwardCylinder Z₀ R hR := by
        rw [← kineticReflection_image_backwardCylinder P₀ R hR]
        exact ⟨P, hP, rfl⟩
      have hs := spatial_forward_slice_smooth hH B hB Z₀ hR U hUs hUe
        (kineticReflection P) hp
      rw [spatial_slice_reflection]
      exact hs.comp P.position contDiffAt_id.neg
    · intro m hm P hP
      have hri : 0 < 3 * R / 4 := by positivity
      have hQi : kineticReflection P ∈ forwardCylinder Z₀ (3 * R / 4) hri := by
        rw [← kineticReflection_image_backwardCylinder P₀ (3 * R / 4) hri]
        exact ⟨P, hP, rfl⟩
      let Q := kineticReflection P
      have hQo := spatial_inner_subset_outer Z₀ hR hQi
      let p : LocalBallStart Z₀.velocity R := ⟨Q, hQo.2.2.1⟩
      let T : {t : ℝ // p.1.time < t} :=
        ⟨p.1.time + R ^ 2 / 8, by nlinarith only [sq_pos_of_pos hR]⟩
      have hT : T.1 - p.1.time = R ^ 2 / 8 := by dsimp only [T]; ring
      have hfb := spatial_forward_derivative_bound hH hLE hd hlam hLam B hB Z₀ hR
        U hUc hUs hUe p hQi T hT m hm
      have hki := hkernel B hB Z₀.velocity R hR p T hQi.2.2.1 hT m
      have hM :=
        (spatialData_local_extension Z₀ Q hR hQo U hUc).1
      have hbound := hfb.trans (mul_le_mul_of_nonneg_left hki hM)
      have hscale : R ^ (3 * m) * R ^ (-3 * (m : ℝ)) = 1 := by
        rw [← Real.rpow_natCast R (3 * m), ← Real.rpow_add hR]
        have he : ((3 * m : ℕ) : ℝ) + -3 * (m : ℝ) = 0 := by push_cast; ring
        rw [he, Real.rpow_zero]
      have _h_xinl_0 (u : KineticPoint d → ℝ) (P) (m : ℕ) : ‖iteratedFDeriv ℝ m (physicalPositionSlice u P) P.position‖ = ‖iteratedFDeriv ℝ m (physicalPositionSlice (u ∘ kineticReflection) (kineticReflection P)) (kineticReflection P).position‖ := by
        rw [spatial_slice_reflection]
        exact (LinearIsometryEquiv.neg ℝ (E := PDE.Vec d)).norm_iteratedFDeriv_comp_right _ _ _
      rw [_h_xinl_0]
      calc
        _ ≤ R ^ (3 * m) * (Holder.oscillationOn U (forwardCylinder Z₀ R hR) *
            (C m * R ^ (-3 * (m : ℝ)))) :=
          mul_le_mul_of_nonneg_left hbound (pow_nonneg hR.le _)
        _ = (C m * Holder.oscillationOn U (forwardCylinder Z₀ R hR)) *
            (R ^ (3 * m) * R ^ (-3 * (m : ℝ))) := by ring
        _ = C m * Holder.oscillationOn u (backwardCylinder P₀ R) := by
          have _h_xinl_0 : Holder.oscillationOn (u ∘ kineticReflection) (forwardCylinder (kineticReflection P₀) R hR) = Holder.oscillationOn u (backwardCylinder P₀ R) := by
            have hi : (u ∘ kineticReflection) '' forwardCylinder (kineticReflection P₀) R hR =
                u '' backwardCylinder P₀ R := by
              rw [image_comp, kineticReflection_image_forwardCylinder, kineticReflection_involutive]
            simp only [Holder.oscillationOn, hi]
          rw [hscale, mul_one, _h_xinl_0]
  obtain ⟨C, α, hC, hα, hα1, hholder⟩ : ∃ C α : ℝ, 0 < C ∧ 0 < α ∧ α < 1 ∧
      ∀ (A : CoefficientField d), IsSmoothCoefficient A → IsSymmetricCoefficient A →
      HasLowerEllipticity lam A → HasUpperEllipticity Lam A →
      ∀ (u : KineticPoint d → ℝ),
      ContinuousOn u (closure (backwardCylinder (⟨0, 0, 0⟩ : KineticPoint d) 1)) →
      IsKineticC112On u (backwardCylinder (⟨0, 0, 0⟩ : KineticPoint d) 1) →
      (∀ P ∈ backwardCylinder (⟨0, 0, 0⟩ : KineticPoint d) 1,
        backwardOperatorOfTimeVelocityCoefficient A u P = 0) →
      (∀ P ∈ backwardCylinder (⟨0, 0, 0⟩ : KineticPoint d) (3 / 4),
        ‖fderiv ℝ (physicalPositionSlice u P) P.position‖ ≤
          (C_m 1) * oscillationOn u (backwardCylinder (⟨0, 0, 0⟩ : KineticPoint d) 1)) →
      ∀ P ∈ backwardCylinder (⟨0, 0, 0⟩ : KineticPoint d) (1 / 2),
      ∀ Q ∈ backwardCylinder (⟨0, 0, 0⟩ : KineticPoint d) (1 / 2),
        |u P - u Q| ≤ C * oscillationOn u
          (backwardCylinder (⟨0, 0, 0⟩ : KineticPoint d) 1) *
          kineticIncrement (⟨0, 0, 0⟩ : KineticPoint d) P Q ^ α := by
    let K := (C_m 1)
    have hK := (hCm 1)
    obtain ⟨Cp, α, hCp, hα, hα1, hpar⟩ : ∃ C α : ℝ, 0 < C ∧ 0 < α ∧ α < 1 ∧
        ∀ (A : CoefficientField d), IsSmoothCoefficient A → IsSymmetricCoefficient A →
        HasLowerEllipticity lam A → HasUpperEllipticity Lam A →
        ∀ (w : TimeVelocity d → ℝ) (M : ℝ), 0 ≤ M →
        IsScalarC12On w (scalarParabolicOpenCylinder (-9/16) 0
          (PDE.euclideanBall 0 (3/4 : ℝ))) →
        (∀ z ∈ scalarParabolicOpenCylinder (-9/16) 0
          (PDE.euclideanBall 0 (3/4 : ℝ)), |w z| ≤ M) →
        (∀ z ∈ scalarParabolicOpenCylinder (-9/16) 0
          (PDE.euclideanBall 0 (3/4 : ℝ)),
          |scalarTimeDerivative w z - matrixContraction (coefficientAt A z)
            (scalarSpatialHessian w z)| ≤ M) →
        ∀ z ∈ scalarParabolicOpenCylinder (-1/4) 0 (PDE.euclideanBall 0 (1/2 : ℝ)),
        ∀ z' ∈ scalarParabolicOpenCylinder (-1/4) 0 (PDE.euclideanBall 0 (1/2 : ℝ)),
          |w z - w z'| ≤ C * M * parabolicDistance z z' ^ α := by
      obtain ⟨q, K, hqhalf, hq1, hK, hdecay⟩ : ∃ q K : ℝ, (1 / 2 : ℝ) ≤ q ∧ q < 1 ∧ 0 < K ∧
          ∀ (A : CoefficientField d), IsSmoothCoefficient A → IsSymmetricCoefficient A →
            HasLowerEllipticity lam A → HasUpperEllipticity Lam A →
          ∀ (U : Set (TimeVelocity d)) (T : ℝ) (v₀ : PDE.Vec d) (r : ℝ),
            0 < r → r ≤ 1 →
            scalarParabolicClosedCylinder (T - r ^ 2) T (PDE.euclideanBall v₀ r) ⊆ U →
          ∀ (w : TimeVelocity d → ℝ) (M : ℝ), 0 ≤ M →
            IsScalarC12On w U → (∀ z ∈ U, |w z| ≤ M) →
            (∀ z ∈ U, |scalarTimeDerivative w z -
              matrixContraction (coefficientAt A z) (scalarSpatialHessian w z)| ≤ M) →
            ∀ (n : ℕ) (z z' : TimeVelocity d),
              z ∈ scalarParabolicOpenCylinder (T - dyadicRadius r n ^ 2) T
                (PDE.euclideanBall v₀ (dyadicRadius r n)) →
              z' ∈ scalarParabolicOpenCylinder (T - dyadicRadius r n ^ 2) T
                (PDE.euclideanBall v₀ (dyadicRadius r n)) →
              |w z - w z'| ≤ K * M * q ^ n := by
        obtain ⟨θ, hθ, hθ1, hc⟩ : ∃ θ : ℝ, 0 ≤ θ ∧ θ < 1 ∧
        ∀ (A : CoefficientField d), IsSmoothCoefficient A → IsSymmetricCoefficient A →
          HasLowerEllipticity lam A → HasUpperEllipticity Lam A →
        ∀ (T : ℝ) (v₀ : PDE.Vec d) (r : ℝ), 0 < r →
        ∀ (w : TimeVelocity d → ℝ) (M : ℝ), 0 ≤ M →
          IsScalarC12On w
            (scalarParabolicOpenCylinder (T - r ^ 2) T (PDE.euclideanBall v₀ r)) →
          ContinuousOn w
            (scalarParabolicClosedCylinder (T - r ^ 2) T (PDE.euclideanBall v₀ r)) →
          (∀ z ∈ scalarParabolicOpenCylinder (T - r ^ 2) T (PDE.euclideanBall v₀ r),
            |scalarTimeDerivative w z -
              matrixContraction (coefficientAt A z) (scalarSpatialHessian w z)| ≤ M) →
          ∀ l b : ℝ,
            (∀ z ∈ scalarParabolicOpenCylinder (T - r ^ 2) T (PDE.euclideanBall v₀ r),
              l ≤ w z ∧ w z ≤ b) →
          ∃ l' b' : ℝ, b' - l' ≤ θ * (b - l) + 4 * M * r ^ 2 ∧
            ∀ z ∈ scalarParabolicOpenCylinder (T - (r / 2) ^ 2) T
              (PDE.euclideanBall v₀ (r / 2)), l' ≤ w z ∧ w z ≤ b' := by
          have hN := hd
          obtain ⟨θ, hθ, hθ1, hc⟩ : ∃ θ : ℝ, 0 ≤ θ ∧ θ < 1 ∧
              ∀ (A : CoefficientField d), IsSmoothCoefficient A → IsSymmetricCoefficient A →
                HasLowerEllipticity lam A → HasUpperEllipticity Lam A →
              ∀ (T : ℝ) (v₀ : PDE.Vec d) (r : ℝ), 0 < r →
              ∀ (v : TimeVelocity d → ℝ),
                IsScalarC12On v
                  (scalarParabolicOpenCylinder (T - r ^ 2) T (PDE.euclideanBall v₀ r)) →
                (∀ z ∈ scalarParabolicOpenCylinder (T - r ^ 2) T (PDE.euclideanBall v₀ r),
                  scalarTimeDerivative v z =
                    matrixContraction (coefficientAt A z) (scalarSpatialHessian v z)) →
                ∀ l b : ℝ,
                  (∀ z ∈ scalarParabolicOpenCylinder (T - r ^ 2) T (PDE.euclideanBall v₀ r),
                    l ≤ v z ∧ v z ≤ b) →
                ∃ l' b' : ℝ, b' - l' = θ * (b - l) ∧
                  ∀ z ∈ scalarParabolicOpenCylinder (T - (r / 2) ^ 2) T
                    (PDE.euclideanBall v₀ (r / 2)), l' ≤ v z ∧ v z ≤ b' := by
            obtain ⟨h, hh, hh1, hc⟩ : ∃ h : ℝ, 0 < h ∧ h ≤ 1 ∧
              ∀ (A : CoefficientField d) (v : TimeVelocity d → ℝ),
                IsContinuousCoefficientOn A (Ioo (0 : ℝ) 1 ×ˢ PDE.euclideanBall 0 1) →
                (∀ z ∈ Ioo (0 : ℝ) 1 ×ˢ PDE.euclideanBall 0 1, (coefficientAt A z).IsSymm) →
                HasLowerEllipticityOn lam A (Ioo (0 : ℝ) 1 ×ˢ PDE.euclideanBall 0 1) →
                HasUpperEllipticityOn Lam A (Ioo (0 : ℝ) 1 ×ˢ PDE.euclideanBall 0 1) →
                IsScalarC12On v (Ioo (0 : ℝ) 1 ×ˢ PDE.euclideanBall 0 1) →
                (∀ z ∈ Ioo (0 : ℝ) 1 ×ˢ PDE.euclideanBall 0 1,
                  scalarTimeDerivative v z =
                    matrixContraction (coefficientAt A z) (scalarSpatialHessian v z)) →
                ∀ l b : ℝ, (∀ z ∈ Ioo (0 : ℝ) 1 ×ˢ PDE.euclideanBall 0 1, l ≤ v z ∧ v z ≤ b) →
                ∃ l' b' : ℝ, b' - l' = (1 - h) * (b - l) ∧
                  ∀ z ∈ Ioo (3 / 4 : ℝ) 1 ×ˢ PDE.euclideanBall 0 (1 / 2 : ℝ),
                    l' ≤ v z ∧ v z ≤ b' := by
              obtain ⟨h₀, hh₀, harnack⟩ := parabolic_harnack_unit_cylinder d hN lam hlam Lam hLam
              let h := min h₀ 1
              have hh := lt_min hh₀ zero_lt_one
              refine ⟨h, hh, min_le_right _ _, ?_⟩
              intro A v hA hs hlo hhi hv he l b hbound
              let p : TimeVelocity d := (3 / 8, 0)
              have hp : p ∈ Ioo (1 / 4 : ℝ) (1 / 2 : ℝ) ×ˢ
                  PDE.euclideanBall 0 (1 / 2 : ℝ) := by
                constructor
                · norm_num [p]
                · simp [p, PDE.euclideanBall]
              have hpU : p ∈ Ioo (0 : ℝ) 1 ×ˢ PDE.euclideanBall 0 1 := by
                constructor
                · norm_num [p]
                · simp [p, PDE.euclideanBall]
              have haffine (k c : ℝ) : ∀ z ∈ Ioo (0 : ℝ) 1 ×ˢ PDE.euclideanBall 0 1,
                  scalarTimeDerivative (fun q => k * v q + c) z =
                    matrixContraction (coefficientAt A z)
                      (scalarSpatialHessian (fun q => k * v q + c) z) := by
                intro z hz
                rw [scalarTimeDerivative_const_mul_add_const, scalarSpatialHessian_const_mul_add_const,
                  matrixContraction_smul_right, he z hz]
              have hn (z : TimeVelocity d) (hz : z ∈ Ioo (0 : ℝ) 1 ×ˢ PDE.euclideanBall 0 1) :
                  0 ≤ 1 * v z + -l := by linarith only [(hbound z hz).1]
              have hn' (z : TimeVelocity d) (hz : z ∈ Ioo (0 : ℝ) 1 ×ˢ PDE.euclideanBall 0 1) :
                  0 ≤ -1 * v z + b := by linarith only [(hbound z hz).2]
              refine ⟨l + h * (v p - l), b - h * (b - v p), by ring, ?_⟩
              intro z hz
              have hlow := harnack A (fun q => 1 * v q + -l) hA hs hlo hhi
                (hv.const_mul_add_const 1 (-l)) hn (haffine 1 (-l)) p hp z hz
              have hupp := harnack A (fun q => -1 * v q + b) hA hs hlo hhi
                (hv.const_mul_add_const (-1) b) hn' (haffine (-1) b) p hp z hz
              have hlscale : h * (v p - l) ≤ h₀ * (v p - l) :=
                mul_le_mul_of_nonneg_right (min_le_left _ _) (sub_nonneg.mpr (hbound p hpU).1)
              have huscale : h * (b - v p) ≤ h₀ * (b - v p) :=
                mul_le_mul_of_nonneg_right (min_le_left _ _) (sub_nonneg.mpr (hbound p hpU).2)
              constructor <;> linarith only [hlow, hupp, hlscale, huscale]
            refine ⟨1 - h, sub_nonneg.mpr hh1, by linarith only [hh], ?_⟩
            intro A hA hs hlo hhi T v₀ r hr v hv he l b hb
            let D := scalarParabolicOpenCylinder (T - r ^ 2) T (PDE.euclideanBall v₀ r)
            let U := Ioo (0 : ℝ) 1 ×ˢ PDE.euclideanBall (0 : PDE.Vec d) 1
            let a := parabolicAffine (T - r ^ 2) v₀ r
            have hm : MapsTo (parabolicAffine (T - r ^ 2) v₀ r)
              (Ioo (0 : ℝ) 1 ×ˢ PDE.euclideanBall 0 1)
              (scalarParabolicOpenCylinder (T - r ^ 2) T (PDE.euclideanBall v₀ r)) := by
                intro z hz
                change (T - r ^ 2 + r ^ 2 * z.1, v₀ + r • z.2) ∈ _
                constructor
                · have hs := sq_pos_of_pos hr
                  constructor <;> nlinarith only [hs, hz.1.1, hz.1.2]
                · rw [PDE.mem_euclideanBall_iff_vecEuclideanNorm_lt hr]
                  rw [add_sub_cancel_left, PDE.vecEuclideanNorm_smul, abs_of_pos hr]
                  have hn := (PDE.mem_euclideanBall_iff_vecEuclideanNorm_lt zero_lt_one).mp hz.2
                  simp only [sub_zero] at hn
                  nlinarith only [hr, hn]

              /- Inverse coordinates of a physical point recover the point exactly. -/
            have hD : IsOpen D := isOpen_Ioo.prod (PDE.isOpen_euclideanBall v₀ r)
            obtain ⟨hvhat, hj⟩ := KrylovEstimate.scalarC12On_affine_pullback hD v hv
              (T - r ^ 2) v₀ hr
            have hvU : IsScalarC12On (v ∘ a) U := by
              rcases hvhat with ⟨hv₀, ht, hv₂, hdt, hdg, hdh⟩
              exact ⟨hv₀.mono hm, fun z hz => ht z (hm hz), fun z hz => hv₂ z (hm hz),
                hdt.mono hm, hdg.mono hm, hdh.mono hm⟩
            have heU : ∀ z ∈ U, scalarTimeDerivative (v ∘ a) z =
                matrixContraction (coefficientAt (pullbackCoefficient A (T - r ^ 2) v₀ r) z)
                  (scalarSpatialHessian (v ∘ a) z) := by
              intro z hz
              rw [(hj z (hm hz)).1, (hj z (hm hz)).2, coefficientAt_pullbackCoefficient,
                matrixContraction_smul_right, he _ (hm hz)]
            have hAc :=
              IsContinuousCoefficientOn.pullback
                (hA.continuous.continuousOn : IsContinuousCoefficientOn A D) hm
            have hsU : ∀ z ∈ U,
                (coefficientAt (pullbackCoefficient A (T - r ^ 2) v₀ r) z).IsSymm := by
              intro z _
              exact hs _ _
            have hloU : HasLowerEllipticityOn lam
                (pullbackCoefficient A (T - r ^ 2) v₀ r) U := by
              intro z _
              exact hlo _ _
            have hhiU : HasUpperEllipticityOn Lam
                (pullbackCoefficient A (T - r ^ 2) v₀ r) U := by
              intro z _
              exact hhi _ _
            obtain ⟨l', b', hw, hbounds⟩ := hc
              (pullbackCoefficient A (T - r ^ 2) v₀ r) (v ∘ a) hAc hsU hloU hhiU hvU heU
              l b (fun z hz => hb _ (hm hz))
            refine ⟨l', b', hw, ?_⟩
            intro z hz
            have hn := backward_half_ball_inverse_mem T v₀ hr hz
            have h := hbounds _ hn
            simpa only [Function.comp_def, a, parabolicAffine_inverse_apply T v₀ hr z] using h
          refine ⟨θ, hθ, hθ1, ?_⟩
          intro A hA hs hlo hhi T v₀ r hr w M hM hw hwc hf l b hb
          have haT := sub_lt_self T (sq_pos_of_pos hr)
          obtain ⟨v, hv, hvc, htrace, he, herr⟩ := exists_parabolic_homogeneous_replacement
            hLE hN lam Lam hlam hLam A hA hs hlo hhi (T - r ^ 2) T haT v₀ r hr w M hM hw hwc hf
          have herr' (z : TimeVelocity d)
              (hz : z ∈ scalarParabolicOpenCylinder (T - r ^ 2) T (PDE.euclideanBall v₀ r)) :
              |w z - v z| ≤ M * r ^ 2 := by
            have h := herr z ⟨⟨hz.1.1.le, hz.1.2.le⟩, subset_closure hz.2⟩
            simpa only [sub_sub_cancel] using h
          have hvb : ∀ z ∈ scalarParabolicOpenCylinder (T - r ^ 2) T (PDE.euclideanBall v₀ r),
              l - M * r ^ 2 ≤ v z ∧ v z ≤ b + M * r ^ 2 := by
            intro z hz
            have hd := abs_le.mp (herr' z hz)
            constructor <;> linarith only [hd.1, hd.2, (hb z hz).1, (hb z hz).2]
          obtain ⟨l', b', hwidth, hbounds⟩ := hc A hA hs hlo hhi T v₀ r hr v hv he
            (l - M * r ^ 2) (b + M * r ^ 2) hvb
          refine ⟨l' - M * r ^ 2, b' + M * r ^ 2, ?_, ?_⟩
          · have hh : 0 ≤ (1 - θ) * (M * r ^ 2) :=
              mul_nonneg (sub_nonneg.mpr hθ1.le) (mul_nonneg hM (sq_nonneg r))
            linarith only [hwidth, hh]
          · intro z hz
            have hzU : z ∈ scalarParabolicOpenCylinder (T - r ^ 2) T
                (PDE.euclideanBall v₀ r) := by
              constructor
              · constructor
                · nlinarith only [hz.1.1, sq_pos_of_pos hr]
                · exact hz.1.2
              · rw [PDE.mem_euclideanBall_iff_vecEuclideanNorm_lt hr]
                have hn := (PDE.mem_euclideanBall_iff_vecEuclideanNorm_lt (half_pos hr)).mp hz.2
                exact hn.trans (half_lt_self hr)
            have hd := abs_le.mp (herr' z hzU)
            constructor <;> linarith only [hd.1, hd.2, (hbounds z hz).1, (hbounds z hz).2]
        let q := (1 + θ) / 2
        have hqhalf : (1 / 2 : ℝ) ≤ q := by dsimp [q]; linarith only [hθ]
        have hq1 : q < 1 := by dsimp [q]; linarith only [hθ1]
        have hgap : 0 < q - θ := by dsimp [q]; linarith only [hθ1]
        let K := 2 + 4 / (q - θ)
        have hK : 0 < K := by dsimp [K]; positivity
        have hK2 : 2 ≤ K := le_add_of_nonneg_right (div_nonneg (by norm_num) hgap.le)
        have hKgap : 4 ≤ (q - θ) * K := by
          dsimp [K]
          have heq : (q - θ) * (2 + 4 / (q - θ)) = 2 * (q - θ) + 4 := by
            field_simp [hgap.ne']
          rw [heq]
          linarith only [hgap]
        refine ⟨q, K, hqhalf, hq1, hK, ?_⟩
        intro A hA hs hlo hhi U T v₀ r hr hr1 hU w M hM hw hb hf
        let Q (n : ℕ) := scalarParabolicOpenCylinder (T - dyadicRadius r n ^ 2) T
          (PDE.euclideanBall v₀ (dyadicRadius r n))
        have hclosed (n : ℕ) : scalarParabolicClosedCylinder (T - dyadicRadius r n ^ 2) T
            (PDE.euclideanBall v₀ (dyadicRadius r n)) ⊆ U :=
          (backward_ball_closed_mono T v₀ (dyadicRadius_pos hr n)
            (dyadicRadius_le hr.le n)).trans hU
        have hQU (n : ℕ) : Q n ⊆ U := by
          intro z hz
          exact hclosed n ⟨⟨hz.1.1.le, hz.1.2.le⟩, subset_closure hz.2⟩
        have hne (n : ℕ) : (w '' Q n).Nonempty :=
          (backward_ball_nonempty T v₀ (dyadicRadius_pos hr n)).image w
        have hab (n : ℕ) : BddAbove (w '' Q n) := by
          refine ⟨M, ?_⟩
          rintro _ ⟨z, hz, rfl⟩
          exact le_of_abs_le (hb z (hQU n hz))
        have hbb (n : ℕ) : BddBelow (w '' Q n) := by
          refine ⟨-M, ?_⟩
          rintro _ ⟨z, hz, rfl⟩
          exact neg_le_of_abs_le (hb z (hQU n hz))
        let f (n : ℕ) := sSup (w '' Q n) - sInf (w '' Q n)
        have hrec (n : ℕ) : f (n + 1) ≤ θ * f n + (4 * M * r ^ 2) * (1 / 4 : ℝ) ^ n := by
          have hbounds : ∀ z ∈ Q n, sInf (w '' Q n) ≤ w z ∧ w z ≤ sSup (w '' Q n) :=
            fun z hz => ⟨csInf_le (hbb n) (mem_image_of_mem w hz),
              le_csSup (hab n) (mem_image_of_mem w hz)⟩
          obtain ⟨l, b, hwidth, hbounds'⟩ := hc A hA hs hlo hhi T v₀ (dyadicRadius r n)
            (dyadicRadius_pos hr n) w M hM (scalarC12On_mono hw (hQU n))
            (hw.continuousOn.mono (hclosed n)) (fun z hz => hf z (hQU n hz))
            (sInf (w '' Q n)) (sSup (w '' Q n)) hbounds
          have hb' : ∀ z ∈ Q (n + 1), l ≤ w z ∧ w z ≤ b := by
            intro z hz
            apply hbounds'
            simpa only [Q, dyadicRadius_succ] using hz
          have hsup : sSup (w '' Q (n + 1)) ≤ b := csSup_le (hne _) (by
            rintro _ ⟨z, hz, rfl⟩
            exact (hb' z hz).2)
          have hinf : l ≤ sInf (w '' Q (n + 1)) := le_csInf (hne _) (by
            rintro _ ⟨z, hz, rfl⟩
            exact (hb' z hz).1)
          have hwidth' := hwidth
          rw [dyadicRadius_sq] at hwidth'
          change _ ≤ θ * f n + _ at hwidth'
          dsimp only [f]
          nlinarith only [hsup, hinf, hwidth']
        have hbase : f 0 ≤ K * M := by
          have hsup : sSup (w '' Q 0) ≤ M := csSup_le (hne _) (by
            rintro _ ⟨z, hz, rfl⟩
            exact le_of_abs_le (hb z (hQU 0 hz)))
          have hinf : -M ≤ sInf (w '' Q 0) := le_csInf (hne _) (by
            rintro _ ⟨z, hz, rfl⟩
            exact neg_le_of_abs_le (hb z (hQU 0 hz)))
          have hkm := mul_le_mul_of_nonneg_right hK2 hM
          dsimp [f]
          linarith only [hsup, hinf, hkm]
        have hforce : 4 * M * r ^ 2 ≤ (q - θ) * (K * M) := by
          have hrsq : r ^ 2 ≤ 1 := by nlinarith only [hr.le, hr1]
          have h := mul_le_mul_of_nonneg_right hKgap hM
          nlinarith only [h, mul_le_mul_of_nonneg_left hrsq (mul_nonneg (by norm_num : (0 : ℝ) ≤ 4) hM)]
        have hdecay := forced_recurrence_le_geometric hθ (by linarith only [hqhalf])
          (by positivity : 0 ≤ 4 * M * r ^ 2) hforce f hbase hrec
        intro n z z' hz hz'
        have hlz := csInf_le (hbb n) (mem_image_of_mem w hz)
        have huz := le_csSup (hab n) (mem_image_of_mem w hz)
        have hlz' := csInf_le (hbb n) (mem_image_of_mem w hz')
        have huz' := le_csSup (hab n) (mem_image_of_mem w hz')
        have hn := hdecay n
        dsimp only [f] at hn
        rw [abs_le]
        constructor <;> linarith only [hlz, huz, hlz', huz', hn]
      obtain ⟨α, hα, hα1, hqα⟩ : ∃ α : ℝ, 0 < α ∧ α < 1 ∧ q ≤ (1 / 2 : ℝ) ^ α := by
          have hcont : ContinuousAt (fun α : ℝ => (1 / 2 : ℝ) ^ α) 0 :=
            Real.continuousAt_const_rpow (by norm_num)
          have hnhds : {α : ℝ | q < (1 / 2 : ℝ) ^ α} ∈ 𝓝 0 :=
            hcont.preimage_mem_nhds (Ioi_mem_nhds (by simpa only [Real.rpow_zero] using hq1))
          obtain ⟨ε, hε, hsub⟩ := Metric.mem_nhds_iff.mp hnhds
          let α := min (ε / 2) (1 / 2)
          have hα : 0 < α := lt_min (half_pos hε) (by norm_num)
          have hαε : α < ε := (min_le_left _ _).trans_lt (half_lt_self hε)
          have hα1 : α < 1 := (min_le_right _ _).trans_lt (by norm_num)
          refine ⟨α, hα, hα1, le_of_lt (hsub ?_)⟩
          change dist α 0 < ε
          simpa only [Real.dist_eq, sub_zero, abs_of_pos hα] using hαε

        /- A dyadic scale chosen above `x` bounds the corresponding geometric decay by `2x`. -/
      let C := K * (32 : ℝ) ^ α + 2 * (64 : ℝ) ^ α
      have hC : 0 < C := by dsimp [C]; positivity
      refine ⟨C, α, hC, hα, hα1, ?_⟩
      intro A hA hs hlo hhi w M hM hw hb hf z hz z' hz'
      have hsub : scalarParabolicOpenCylinder (-1/4) 0 (PDE.euclideanBall (0 : PDE.Vec d) (1/2)) ⊆
          scalarParabolicOpenCylinder (-9/16) 0 (PDE.euclideanBall 0 (3/4)) := by
        intro y hy
        constructor
        · constructor
          · linarith only [hy.1.1]
          · exact hy.1.2
        · rw [PDE.mem_euclideanBall_iff_vecEuclideanNorm_lt (by norm_num)]
          exact ((PDE.mem_euclideanBall_iff_vecEuclideanNorm_lt
            (by norm_num : (0 : ℝ) < 1 / 2)).mp hy.2).trans (by norm_num)
      by_cases heq : z = z'
      · rw [heq, sub_self, abs_zero]
        exact mul_nonneg (mul_nonneg hC.le hM) (Real.rpow_nonneg (parabolicDistance_nonneg _ _) _)
      let δ := parabolicDistance z z'
      have hδ : 0 < δ := parabolicDistance_pos heq
      by_cases hsmall : δ < 1 / 64
      · obtain ⟨T, hTpair, hT0, hmargin⟩ := exists_pair_top hz.1.2 hz'.1.2 hδ
        have hzt : z.1 < T := (le_max_left _ _).trans_lt hTpair
        have hbase := pair_base_closed_cylinder_subset hz hzt hT0
        have hx : 0 < 16 * δ := mul_pos (by norm_num) hδ
        have hx1 : 16 * δ ≤ 1 := by linarith only [hsmall]
        obtain ⟨n, hnlo, hnhi⟩ := exists_nat_pow_near_of_lt_one hx hx1
          (by norm_num : (0 : ℝ) < 1 / 2) (by norm_num)
        have hrad : 2 * δ ≤ dyadicRadius (1 / 8) n := by
          dsimp only [dyadicRadius]
          linarith only [hnhi]
        obtain ⟨hzn, hz'n⟩ := pair_mem_common_backward_cylinder heq hTpair hmargin hrad
        have hbound := hdecay A hA hs hlo hhi _ T z.2 (1 / 8) (by norm_num) (by norm_num)
          hbase w M hM hw hb hf n z z' hzn hz'n
        have hpower : q ^ n ≤ (32 * δ) ^ α := by
          have hp := geometric_decay_le_holder_power (by linarith only [hqhalf]) hα hqα n hnlo
          have he : 2 * (16 * δ) = 32 * δ := by ring
          rw [he] at hp
          exact hp
        have hC32 : K * (32 : ℝ) ^ α ≤ C :=
          le_add_of_nonneg_right (mul_nonneg (by norm_num) (Real.rpow_nonneg (by norm_num) _))
        calc |w z - w z'| ≤ K * M * q ^ n := hbound
          _ ≤ K * M * (32 * δ) ^ α :=
            mul_le_mul_of_nonneg_left hpower (mul_nonneg hK.le hM)
          _ = (K * (32 : ℝ) ^ α) * M * δ ^ α := by
            rw [Real.mul_rpow (by norm_num) hδ.le]
            ring
          _ ≤ C * M * δ ^ α := by gcongr
      · have hlarge : (1 / 64 : ℝ) ≤ δ := not_lt.mp hsmall
        have hprod : 1 ≤ (64 : ℝ) ^ α * δ ^ α := by
          rw [← Real.mul_rpow (by norm_num) hδ.le]
          have hscale : (1 : ℝ) ≤ 64 * δ := by linarith only [hlarge]
          simpa only [Real.one_rpow] using Real.rpow_le_rpow zero_le_one hscale hα.le
        have hC64 : 2 * (64 : ℝ) ^ α ≤ C :=
          le_add_of_nonneg_left (mul_nonneg hK.le (Real.rpow_nonneg (by norm_num) _))
        have habs : |w z - w z'| ≤ 2 * M :=
          (abs_sub_le (w z) 0 (w z')).trans (by
            simpa only [sub_zero, zero_sub, abs_neg, two_mul] using
              add_le_add (hb z (hsub hz)) (hb z' (hsub hz')))
        calc |w z - w z'| ≤ 2 * M := habs
          _ ≤ (2 * (64 : ℝ) ^ α) * M * δ ^ α := by
            have h := mul_le_mul_of_nonneg_left hprod (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) hM)
            nlinarith only [h]
          _ ≤ C * M * δ ^ α := by gcongr
    refine ⟨Cp * (1 + K) + K, α, by positivity, hα, hα1, ?_⟩
    intro A hA hs hlo hhi u hc hu he hdx P hP Q hQ
    let Z : KineticPoint d := ⟨0, 0, 0⟩
    let D := backwardCylinder Z 1
    let O := oscillationOn u D
    obtain ⟨habc, hbbc⟩ := bounded_values_of_compact
      (isCompact_closure_backwardCylinder Z 1 (by norm_num)) hc
    have hab := habc.mono (image_mono subset_closure)
    have hbb := hbbc.mono (image_mono subset_closure)
    have hO := oscillationOn_nonneg (backwardCylinder_nonempty Z (by norm_num)) hab hbb
    obtain ⟨hPt, hPx⟩ := holder_half_coordinates hP
    obtain ⟨hQt, hQx⟩ := holder_half_coordinates hQ
    have houter : ∀ z ∈ scalarParabolicOpenCylinder (-1 / 4) 0
        (PDE.euclideanBall (0 : PDE.Vec d) (1 / 2)),
        z ∈ scalarParabolicOpenCylinder (-9 / 16) 0 (PDE.euclideanBall 0 (3 / 4)) := by
      intro z hz
      exact ⟨⟨by linarith only [hz.1.1], hz.1.2⟩,
        PDE.euclideanBall_mono (by norm_num) (by norm_num) hz.2⟩
    let B : KineticPoint d := ⟨-1 / 2, 0, 0⟩
    have hB : B ∈ D := by
      norm_num [B, D, Z, backwardCylinder, relativePosition, PDE.euclideanBall,
        PDE.euclideanSqDist, PDE.vecNormSq, PDE.vecDot]
    let w : TimeVelocity d → ℝ := fun z => 1 * u ⟨z.1, P.position, z.2⟩ + -u B
    obtain ⟨hw, hwe⟩ := normalized_slice_equation A u hu he P.position hPx
    have hw' := hw.const_mul_add_const 1 (-u B)
    have hwb : ∀ z ∈ scalarParabolicOpenCylinder (-9 / 16) 0
        (PDE.euclideanBall (0 : PDE.Vec d) (3 / 4)), |w z| ≤ (1 + K) * O := by
      intro z hz
      have h := abs_sub_le_oscillationOn hab hbb (normalized_slice_mem P.position hPx z hz) hB
      have hKO := mul_nonneg hK hO
      dsimp only [w]
      simp only [one_mul, ← sub_eq_add_neg]
      dsimp only [O]
      linarith only [h, hKO]
    have hwf : ∀ z ∈ scalarParabolicOpenCylinder (-9 / 16) 0
        (PDE.euclideanBall (0 : PDE.Vec d) (3 / 4)),
        |scalarTimeDerivative w z - matrixContraction (coefficientAt A z)
          (scalarSpatialHessian w z)| ≤ (1 + K) * O := by
      intro z hz
      dsimp only [w]
      rw [scalarTimeDerivative_const_mul_add_const,
        scalarSpatialHessian_const_mul_add_const]
      simp only [one_mul, one_smul]
      rw [hwe z hz, abs_neg]
      have ht := abs_position_transport_le u ⟨z.1, P.position, z.2⟩ z.2
      have hv : PDE.vecEuclideanNorm z.2 ≤ 1 := by
        have h := (PDE.mem_euclideanBall_iff_vecEuclideanNorm_lt (by norm_num)).mp hz.2
        simp only [sub_zero] at h
        linarith only [h]
      have hbound := hdx _ (holder_slice_mem_inner P.position hPx z hz)
      have h := ht.trans (mul_le_mul hbound hv (PDE.vecEuclideanNorm_nonneg _) (mul_nonneg hK hO))
      linarith only [h, hO]
    have hslice := hpar A hA hs hlo hhi w ((1 + K) * O) (by positivity) hw'
      hwb hwf (P.time, P.velocity) hPt (Q.time, Q.velocity) hQt
    have hslice' : |u P - u ⟨Q.time, P.position, Q.velocity⟩| ≤
        Cp * ((1 + K) * O) * parabolicDistance (P.time, P.velocity) (Q.time, Q.velocity) ^ α := by
      convert hslice using 1
      dsimp only [w]
      congr 1
      ring
    have hdiff : ∀ x ∈ PDE.euclideanBall (0 : PDE.Vec d) (1 / 8),
        DifferentiableAt ℝ (fun x => u ⟨Q.time, x, Q.velocity⟩) x := by
      intro x hx
      exact ((hu.positionSlice_contDiffAt
        (normalized_slice_mem x hx _ (houter _ hQt))).differentiableAt (by norm_num))
    have hbound : ∀ x ∈ PDE.euclideanBall (0 : PDE.Vec d) (1 / 8),
        ‖fderiv ℝ (fun x => u ⟨Q.time, x, Q.velocity⟩) x‖ ≤ K * O := by
      intro x hx
      exact hdx _ (holder_slice_mem_inner x hx _ (houter _ hQt))
    have hspace := Convex.norm_image_sub_le_of_norm_fderiv_le
      hdiff hbound (PDE.convex_euclideanBall (0 : PDE.Vec d) (1 / 8)) hQx hPx
    have hspace' : |u ⟨Q.time, P.position, Q.velocity⟩ - u Q| ≤
        K * O * PDE.vecEuclideanNorm (P.position - Q.position) := by
      rw [Real.norm_eq_abs] at hspace
      exact hspace.trans (mul_le_mul_of_nonneg_left
        (PDE.norm_le_vecEuclideanNorm _) (mul_nonneg hK hO))
    have hpdist : parabolicDistance (P.time, P.velocity) (Q.time, Q.velocity) ≤
        kineticIncrement Z P Q := by
      exact le_add_of_nonneg_right (Real.rpow_nonneg (PDE.vecEuclideanNorm_nonneg _) _)
    have hdist : 0 ≤ parabolicDistance (P.time, P.velocity) (Q.time, Q.velocity) :=
      add_nonneg (Real.rpow_nonneg (abs_nonneg _) _) (PDE.vecEuclideanNorm_nonneg _)
    have hpower := Real.rpow_le_rpow hdist hpdist hα.le
    have hxpower : PDE.vecEuclideanNorm (P.position - Q.position) ≤
      kineticIncrement (⟨0, 0, 0⟩ : KineticPoint d) P Q ^ α := by
        let x := PDE.vecEuclideanNorm (P.position - Q.position)
        have hx : 0 ≤ x := PDE.vecEuclideanNorm_nonneg _
        have hx1 : x ≤ 1 := by
          have h := PDE.vecEuclideanNorm_add_le P.position (-Q.position)
          have hp := (PDE.mem_euclideanBall_iff_vecEuclideanNorm_lt (by norm_num)).mp hPx
          have hq := (PDE.mem_euclideanBall_iff_vecEuclideanNorm_lt (by norm_num)).mp hQx
          simp only [sub_zero] at hp hq
          simp only [PDE.vecEuclideanNorm_neg] at h
          change PDE.vecEuclideanNorm (P.position + -Q.position) ≤ _ at h
          dsimp only [x]
          change PDE.vecEuclideanNorm (P.position + -Q.position) ≤ 1
          linarith only [h, hp, hq]
        have hbase : x ^ (1 / 3 : ℝ) ≤
            kineticIncrement (⟨0, 0, 0⟩ : KineticPoint d) P Q := by
          dsimp only [kineticIncrement]
          simp only [smul_zero, sub_zero]
          exact le_add_of_nonneg_left (add_nonneg (Real.rpow_nonneg (abs_nonneg _) _)
            (PDE.vecEuclideanNorm_nonneg _))
        calc
          x ≤ x ^ (α / 3) := by
            simpa only [Real.rpow_one] using
              Real.rpow_le_rpow_of_exponent_ge' hx hx1 (by positivity : 0 ≤ α / 3)
                (by linarith only [hα1] : α / 3 ≤ 1)
          _ = (x ^ (1 / 3 : ℝ)) ^ α := by
            rw [← Real.rpow_mul hx]
            congr 1
            ring
          _ ≤ kineticIncrement (⟨0, 0, 0⟩ : KineticPoint d) P Q ^ α :=
            Real.rpow_le_rpow (Real.rpow_nonneg hx _) hbase hα.le

      /- Parabolic and spatial moduli give an oscillation-normalized kinetic estimate. -/
    calc
      |u P - u Q| ≤ |u P - u ⟨Q.time, P.position, Q.velocity⟩| +
          |u ⟨Q.time, P.position, Q.velocity⟩ - u Q| := abs_sub_le _ _ _
      _ ≤ Cp * ((1 + K) * O) * parabolicDistance (P.time, P.velocity) (Q.time, Q.velocity) ^ α +
          K * O * PDE.vecEuclideanNorm (P.position - Q.position) := add_le_add hslice' hspace'
      _ ≤ Cp * ((1 + K) * O) * kineticIncrement Z P Q ^ α +
          K * O * kineticIncrement Z P Q ^ α := by gcongr
      _ = (Cp * (1 + K) + K) * O * kineticIncrement Z P Q ^ α := by ring
  refine ⟨C_m, C, α, hCm, hC, hα, hα1, ?_⟩
  intro A hA hs hloAE hhiAE P₀ R hR u hc hu he
  obtain ⟨hlo, hhi⟩ := TheoremA.ellipticity_of_smooth_ae hA hloAE hhiAE
  have hsec := sectionTwo_of_smooth_bounds hlam hLam hA hs hlo hhi
  obtain ⟨hsm, hder⟩ := hspatial A hsec P₀ R hR u hc hu he
  refine ⟨hsm, hder, ?_⟩
  let Z : KineticPoint d := ⟨0, 0, 0⟩
  let U := kineticPullback u P₀ R
  let B := kineticPullbackCoefficient A P₀ R
  have hB : IsSmoothCoefficient (kineticPullbackCoefficient A P₀ R) := by
      exact hA.comp (show ContDiff ℝ ∞ (fun z : TimeVelocity d =>
        (P₀.time + R ^ 2 * z.1, P₀.velocity + R • z.2)) by fun_prop)

    /- Normalization preserves the symmetry and the literal ellipticity constants. -/
  obtain ⟨hBs, hBlo, hBhi⟩ : IsSymmetricCoefficient (kineticPullbackCoefficient A P₀ R) ∧
    HasLowerEllipticity lam (kineticPullbackCoefficient A P₀ R) ∧
    HasUpperEllipticity Lam (kineticPullbackCoefficient A P₀ R) := by
      exact (
    ⟨fun t v => hs (P₀.time + R ^ 2 * t) (P₀.velocity + R • v),
        fun t v => hlo (P₀.time + R ^ 2 * t) (P₀.velocity + R • v),
        fun t v => hhi (P₀.time + R ^ 2 * t) (P₀.velocity + R • v)⟩

    /- The anisotropic classical class is preserved by the moving affine pullback. -/
    )
  obtain ⟨hU, hUe⟩ : IsKineticC112On (kineticPullback u P₀ R)
      (backwardCylinder (⟨0, 0, 0⟩ : KineticPoint d) 1) ∧
    ∀ P ∈ backwardCylinder (⟨0, 0, 0⟩ : KineticPoint d) 1,
      backwardOperatorOfTimeVelocityCoefficient (kineticPullbackCoefficient A P₀ R)
        (kineticPullback u P₀ R) P = 0 := by
    have hD := isOpen_backwardCylinder P₀ R hR
    have hp : ∀ P ∈ backwardCylinder (⟨0, 0, 0⟩ : KineticPoint d) 1,
        kineticAffine P₀ R P ∈ backwardCylinder P₀ R :=
      fun P h => (kineticAffine_mem_cylinder P₀ P hR).mpr h
    have hreg := kineticPullback_C112 hD hu P₀ R
    have hreg' : IsKineticC112On (kineticPullback u P₀ R)
        (backwardCylinder (⟨0, 0, 0⟩ : KineticPoint d) 1) := by
      exact ⟨hreg.1.mono hp, fun P h => hreg.2.1 P (hp P h),
        fun P h => hreg.2.2.1 P (hp P h), fun P h => hreg.2.2.2.1 P (hp P h),
        hreg.2.2.2.2.1.mono hp, hreg.2.2.2.2.2.1.mono hp,
        hreg.2.2.2.2.2.2.1.mono hp, hreg.2.2.2.2.2.2.2.mono hp⟩
    refine ⟨hreg', ?_⟩
    intro P hP
    have _h_xinl_0 : backwardOperatorOfTimeVelocityCoefficient (kineticPullbackCoefficient A P₀ R)
      (kineticPullback u P₀ R) P =
    R ^ 2 * backwardOperatorOfTimeVelocityCoefficient A u (kineticAffine P₀ R P) := by
      have hp := (hp P hP)
      rw [backwardOperatorOfTimeVelocityCoefficient_apply,
        kineticPullback_timeDerivative hD hu P₀ R P hp,
        kineticPullback_positionGradient hu P₀ R P hp,
        kineticPullback_velocityHessian hu P₀ R P hp,
        matrixContraction_smul_right, backwardOperatorOfTimeVelocityCoefficient_apply]
      have hd₁ : ∀ (c : ℝ) (v g : PDE.Vec d),
          PDE.vecDot v (c • g) = c * PDE.vecDot v g := by
        intro c v g
        simp only [PDE.vecDot, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro i _
        ring
      have hd₂ : ∀ (c : ℝ) (v w g : PDE.Vec d),
          PDE.vecDot (v + c • w) g = PDE.vecDot v g + c * PDE.vecDot w g := by
        intro c v w g
        simp only [PDE.vecDot, Pi.add_apply, Pi.smul_apply, smul_eq_mul,
          add_mul, Finset.sum_add_distrib, Finset.mul_sum, mul_assoc]
      rw [hd₁, kineticAffine_velocity, hd₂]
      simp only [kineticPullbackCoefficient, kineticAffine_time]
      ring
    rw [_h_xinl_0,
      backwardEquation_pointwise hD hu hA.continuous he _ (hp P hP), mul_zero]
  have hUc : ContinuousOn (kineticPullback u P₀ R)
      (closure (backwardCylinder (⟨0, 0, 0⟩ : KineticPoint d) 1)) := by
      apply hc.comp (continuous_kineticAffine P₀ R).continuousOn
      intro P hP
      rw [← kineticAffine_image_closedUnitCylinder P₀ hR]
      exact mem_image_of_mem _ hP

    /- Kinetic increments scale by one power of the physical radius. -/
  have hBsec := sectionTwo_of_smooth_bounds hlam hLam hB hBs hBlo hBhi
  have hUae : ∀ᵐ P ∂volume.restrict (backwardCylinder Z 1),
      backwardOperatorOfTimeVelocityCoefficient B U P = 0 := by
    filter_upwards [ae_restrict_mem (isOpen_backwardCylinder Z 1 (by norm_num)).measurableSet]
      with P hP
    exact hUe P hP
  have hgrad : ∀ P ∈ backwardCylinder Z (3 / 4),
      ‖fderiv ℝ (physicalPositionSlice U P) P.position‖ ≤
        C_m 1 * oscillationOn U (backwardCylinder Z 1) := by
    intro P hP
    have hg := (hspatial B hBsec Z 1 (by norm_num) U hUc hU hUae).2 1 (by norm_num) P
      (by simpa only [mul_one] using hP)
    simpa only [one_pow, one_mul, norm_iteratedFDeriv_one] using hg
  have hmod := hholder B hB hBs hBlo hBhi U hUc hU hUe hgrad
  intro P hP Q hQ
  let p := kineticAffineInverse P₀ R P
  let q := kineticAffineInverse P₀ R Q
  have hp : kineticAffine P₀ R p = P := kineticAffine_apply_inverse P₀ hR.ne' P
  have hq : kineticAffine P₀ R q = Q := kineticAffine_apply_inverse P₀ hR.ne' Q
  have hp' : p ∈ backwardCylinder Z (1 / 2) := by
    apply (kineticAffine_mem_radius P₀ p hR (by norm_num : (0 : ℝ) < 1 / 2)).mp
    simpa only [hp, mul_one_div] using hP
  have hq' : q ∈ backwardCylinder Z (1 / 2) := by
    apply (kineticAffine_mem_radius P₀ q hR (by norm_num : (0 : ℝ) < 1 / 2)).mp
    simpa only [hq, mul_one_div] using hQ
  have h := hmod p hp' q hq'
  have hi : kineticIncrement P₀ (kineticAffine P₀ R p) (kineticAffine P₀ R q) / R =
      kineticIncrement (⟨0, 0, 0⟩ : KineticPoint d) p q := by
    have ht : (kineticAffine P₀ R p).time - (kineticAffine P₀ R q).time =
        R ^ 2 * (p.time - q.time) := by simp only [kineticAffine_time]; ring
    have hv : (kineticAffine P₀ R p).velocity - (kineticAffine P₀ R q).velocity =
        R • (p.velocity - q.velocity) := by simp only [kineticAffine_velocity]; module
    have hx : (kineticAffine P₀ R p).position - (kineticAffine P₀ R q).position -
        ((kineticAffine P₀ R p).time - (kineticAffine P₀ R q).time) • P₀.velocity =
        R ^ 3 • (p.position - q.position) := by
      simp only [kineticAffine_position, ht]
      module
    have hp2 : (R ^ 2) ^ (1 / 2 : ℝ) = R := by
      rw [← Real.rpow_natCast_mul hR.le]
      norm_num
    have hp3 : (R ^ 3) ^ (1 / 3 : ℝ) = R := by
      rw [← Real.rpow_natCast_mul hR.le]
      norm_num
    simp only [kineticIncrement]
    rw [hx, ht, hv]
    simp only [abs_mul, abs_of_pos (pow_pos hR 2),
      PDE.vecEuclideanNorm_smul, abs_of_pos hR, abs_of_pos (pow_pos hR 3),
      Real.mul_rpow (pow_nonneg hR.le 2) (abs_nonneg (p.time - q.time)),
      Real.mul_rpow (pow_nonneg hR.le 3) (PDE.vecEuclideanNorm_nonneg _),
      hp2, hp3, smul_zero, sub_zero]
    field_simp
  rw [hp, hq] at hi
  have ho : oscillationOn (kineticPullback u P₀ R)
      (backwardCylinder (⟨0, 0, 0⟩ : KineticPoint d) 1) =
      oscillationOn u (backwardCylinder P₀ R) := by
      have he : kineticPullback u P₀ R ''
          backwardCylinder (⟨0, 0, 0⟩ : KineticPoint d) 1 =
          u '' backwardCylinder P₀ R := by
        simp only [kineticPullback, Function.comp_def]
        rw [← image_image u (kineticAffine P₀ R),
          kineticAffine_image_unitCylinder P₀ hR]
      simp only [oscillationOn, he]

    /- Continuity on the closed outer cylinder is preserved under normalization. -/
  change |u (kineticAffine P₀ R p) - u (kineticAffine P₀ R q)| ≤ _ at h
  rw [hp, hq] at h
  rw [ho, ← hi] at h
  exact h

end LocalA

end HypoellipticAleksandrov.KineticAleksandrov
