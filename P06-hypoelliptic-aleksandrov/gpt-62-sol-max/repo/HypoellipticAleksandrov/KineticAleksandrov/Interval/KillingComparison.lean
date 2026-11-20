module

import HypoellipticAleksandrov.KineticAleksandrov.Decay.ScalarTerminalComparison

public import HypoellipticAleksandrov.KineticAleksandrov.Interval.FourierKernelsEvolution
public import HypoellipticAleksandrov.KineticAleksandrov.Decay.MinorantScaling
public import HypoellipticAleksandrov.KineticAleksandrov.Decay.MaxPrinciple
public import HypoellipticAleksandrov.KineticAleksandrov.Evolution.ComparisonCalculus

/-! # Terminal comparison on a bounded interval

The comparison lemma is an internal maximum-principle tool. Its supersolution data
will be discharged by the positive-time error-function barrier.
-/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.KineticAleksandrov.Interval
open Set MeasureTheory HypoellipticAleksandrov HypoellipticAleksandrov.Parabolic
open HypoellipticAleksandrov.KineticAleksandrov.SectionTwo
open HypoellipticAleksandrov.KineticAleksandrov.Decay

/-- A smooth supersolution dominates the supplied scalar terminal solution on an interval. -/
theorem interval_terminal_comparison {a c lam Lam σ τ : ℝ}
    (hac : a < c) (hστ : σ < τ) (hlam : 0 < lam)
    (B : CoefficientField 1) (hB : IsSectionTwoCoefficient lam Lam B)
    (F : BoundedBorel (PDE.Vec 1)) (V U : TimeVelocity 1 → ℝ)
    (hV : ParabolicProbe.IsClassicalScalarTerminalSolution (PDE.oneDimensionalAxisBox a c)
      stationary (zIndependentCoefficient B) τ F V)
    (hUc : ContinuousOn U (scalarParabolicClosedCylinder σ τ
      (PDE.oneDimensionalAxisBox a c)))
    (hUj : ∀ p ∈ scalarParabolicOpenCylinder σ τ (PDE.oneDimensionalAxisBox a c),
      ContDiffAt ℝ 2 U p)
    (hUs : ∀ p ∈ scalarParabolicOpenCylinder σ τ (PDE.oneDimensionalAxisBox a c),
      scalarParabolicOperator B 0 U p ≤ 0)
    (hterm : ∀ v ∈ closure (PDE.oneDimensionalAxisBox a c), F v ≤ U (τ, v))
    (hlat : ∀ p ∈ scalarParabolicLateralFace σ τ (PDE.oneDimensionalAxisBox a c),
      0 ≤ U p) :
    ∀ v ∈ closure (PDE.oneDimensionalAxisBox a c), V (σ, v) ≤ U (σ, v) := by
  have h := scalar_terminal_signed_comparison (Or.inr ⟨rfl, a, c, hac, rfl⟩)
    hστ B (fun t v => (posDef_of_loewner_lower hlam (hB.2.2.2.2.1 t v)).posSemidef)
    F hV hUc hUj (-1)
    (fun p hp => by simpa only [neg_one_mul, neg_nonneg] using hUs p hp)
    (fun v hv => by simpa only [neg_one_mul, neg_nonpos, sub_nonneg] using hterm v hv)
    (fun p hp => by simpa only [neg_one_mul, neg_nonpos] using hlat p hp)
  simpa only [neg_one_mul, neg_nonpos, sub_nonneg] using h

end HypoellipticAleksandrov.KineticAleksandrov.Interval
