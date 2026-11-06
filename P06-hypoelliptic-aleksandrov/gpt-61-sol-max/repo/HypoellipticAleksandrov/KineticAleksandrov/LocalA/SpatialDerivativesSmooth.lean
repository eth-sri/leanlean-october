module

public import HypoellipticAleksandrov.KineticAleksandrov.LocalA.LocalRepresentation
public import HypoellipticAleksandrov.KineticAleksandrov.Maximum.ABPAbstractDefect
public import HypoellipticAleksandrov.KineticAleksandrov.TheoremA.SmoothEstimateReflection
import Batteries.Tactic.Alias
import HypoellipticAleksandrov.KineticAleksandrov.Occupation.WholeSpaceCoefficient
public import PDEFoundation.Calculus.RegularityOrder




/-! # Interior spatial smoothness and pointwise equations from the source C112 class -/

 public section

namespace HypoellipticAleksandrov.KineticAleksandrov.LocalA
open Set MeasureTheory Parabolic SectionTwo Evolution
open scoped Matrix.Norms.Elementwise

variable {d : ℕ}

variable {lam Lam : ℝ} {B : CoefficientField d} (hB : IsSectionTwoCoefficient lam Lam B)

/-- Entrywise smoothness of the source lift implies smoothness on time-velocity space. -/
alias sectionTwo_coefficient_smooth := _root_.HypoellipticAleksandrov.KineticAleksandrov.Occupation.sectionTwoCoefficient_smooth


include hB in
/-- The full source coefficient class is preserved by the stipulated reflection. -/
theorem sectionTwo_coefficient_reflection   :
    IsSectionTwoCoefficient lam Lam (kineticReflectedCoefficient B) := by
  refine ⟨hB.1, hB.2.1, ?_, ?_, ?_, ?_⟩
  · exact TheoremA.isSmoothFullKineticCoefficient_zIndependent
      (isSmoothCoefficient_kineticReflectedCoefficient B (sectionTwo_coefficient_smooth hB))
  · exact isSymmetricCoefficient_kineticReflectedCoefficient B hB.2.2.2.1
  · intro t v
    exact hB.2.2.2.2.1 (-t) v
  · intro t v
    exact hB.2.2.2.2.2 (-t) v

/-- Continuous classical backward residuals equal zero pointwise when zero almost everywhere. -/
theorem spatial_backward_equation_pointwise  {D : Set (KineticPoint d)}
    (hD : IsOpen D) (A : CoefficientField d) (hA : IsSmoothCoefficient A)
    (u : HypoellipticAleksandrov.KineticScalarField d) (hu : IsKineticC112On u D)
    (he : ∀ᵐ P ∂volume.restrict D, backwardOperatorOfTimeVelocityCoefficient A u P = 0) :
    ∀ P ∈ D, backwardOperatorOfTimeVelocityCoefficient A u P = 0 := (eqOn_of_ae_eq_of_continuousOn_kinetic hD
  (ContinuousOn.comp
    (id
      (ContinuousOn.sub
        (ContinuousOn.add (IsKineticC112On.continuousOn_kineticTimeDerivative hu)
          (id
            (continuousOn_finsetSum Finset.univ fun i a =>
              ContinuousOn.mul (Continuous.continuousOn (Continuous.comp (continuous_apply i) continuous_velocity))
                (Continuous.comp_continuousOn (continuous_apply i)
                  (IsKineticC112On.continuousOn_kineticPositionGradient hu)))))
        (continuousOn_matrixContraction
          (Continuous.continuousOn
            (Continuous.comp (ContDiff.continuous hA) (Continuous.prodMk continuous_time continuous_velocity)))
          (IsKineticC112On.continuousOn_kineticVelocityHessian hu))))
    (Continuous.continuousOn (Homeomorph.continuous (evolutionHomeomorph d))) fun x h => h)
  continuousOn_const he)

/-- Hormander interior regularity gives the stipulated physical spatial slice smoothness. -/
theorem spatial_forward_slice_smooth
    (hH : HormanderHypoellipticityStatement) {d : ℕ} {lam Lam : ℝ}
    (B : CoefficientField d) (hB : IsSectionTwoCoefficient lam Lam B)
    (Z₀ : KineticPoint d) {R : ℝ} (hR : 0 < R) (U : HypoellipticAleksandrov.KineticScalarField d)
    (hUs : IsKineticC112On U (forwardCylinder Z₀ R hR))
    (hUe : ∀ Q ∈ forwardCylinder Z₀ R hR,
      forwardKineticOperator (ofTimeVelocityCoefficient B) U Q = 0)
    (P : KineticPoint d) (hP : P ∈ forwardCylinder Z₀ R hR) :
    ContDiffAt ℝ PDE.smoothOrder (physicalPositionSlice U P) P.position := by
  have hs := mass_classical_homogeneous_smooth hH B hB
    (isOpen_forwardCylinder Z₀ R hR) U hUs hUe


  change ContDiffAt ℝ PDE.smoothOrder ((U ∘ (KineticPoint.equivProd d).symm) ∘
    fun x => (P.time, (x, P.velocity))) P.position
  exact (hs.contDiffAt ((show IsOpen ((KineticPoint.equivProd d) '' forwardCylinder Z₀ R hR) by

      exact ((KineticPoint.homeomorphProd d).isOpenMap _ (isOpen_forwardCylinder Z₀ R hR))).mem_nhds ⟨P, hP, rfl⟩)).comp P.position (contDiffAt_const.prodMk
    (contDiffAt_id.prodMk contDiffAt_const))

end HypoellipticAleksandrov.KineticAleksandrov.LocalA
