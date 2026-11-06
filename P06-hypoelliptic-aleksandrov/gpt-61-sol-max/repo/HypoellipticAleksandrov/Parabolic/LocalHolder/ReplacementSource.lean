module

public import HypoellipticAleksandrov.KineticAleksandrov.SourceProblem.SourceCorrection

public import HypoellipticAleksandrov.Parabolic.LocalHolder.ReplacementApprox
public import HypoellipticAleksandrov.Parabolic.LocalHolder.SourceComparisonCalculus
public import HypoellipticAleksandrov.KineticAleksandrov.ClassicalInputs
public import HypoellipticAleksandrov.Parabolic.LocalHolder.SourceComparison
import HypoellipticAleksandrov.KineticAleksandrov.Occupation.LocalizedKrylovRegularity

/-! # Signed smooth compact source corrections

The internal signed source solver gives the correction and its time-barrier bound.
-/

 public section

namespace HypoellipticAleksandrov.Parabolic.LocalHolder
open Set

open scoped MatrixOrder Matrix.Norms.Elementwise

/-- Subtracting supplied classical solutions subtracts their source and boundary data. -/
theorem isClassicalBackwardDirichletSolution_sub {n : ℕ}
    {a T : ℝ} {Ω : PDE.VelocityRegion n} {A : CoefficientField n}
    {b : PDE.TimeVectorField n} {c F G : PDE.TimeScalarField n}
    {φ χ : PDE.ScalarField n} {h k u v : HypoellipticAleksandrov.Parabolic.ScalarField n}
    (hu : IsClassicalBackwardDirichletSolution a T Ω A b c F φ h u)
    (hv : IsClassicalBackwardDirichletSolution a T Ω A b c G χ k v) :
    IsClassicalBackwardDirichletSolution a T Ω A b c
      (fun t x => F t x - G t x) (fun x => φ x - χ x)
      (fun z => h z - k z) (fun z => u z - v z) := by
  refine ⟨hu.1.sub hv.1, isScalarC12On_sub hu.2.1 hv.2.1, ?_, ?_, ?_⟩
  · intro z hz
    rw [scalarParabolicZeroOrderOperator_sub A b c hu.2.1 hv.2.1 hz,
      hu.2.2.1 z hz, hv.2.2.1 z hz]
  · intro y hy
    change u (T, y) - v (T, y) = φ y - χ y
    rw [hu.2.2.2.1 y hy, hv.2.2.2.1 y hy]
  · intro z hz
    change u z - v z = h z - k z
    rw [hu.2.2.2.2 z hz, hv.2.2.2.2 z hz]

end HypoellipticAleksandrov.Parabolic.LocalHolder
