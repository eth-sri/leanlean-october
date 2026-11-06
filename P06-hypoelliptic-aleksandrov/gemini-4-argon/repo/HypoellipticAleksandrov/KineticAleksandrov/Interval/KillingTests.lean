module

public import HypoellipticAleksandrov.KineticAleksandrov.Interval.KillingComparison
public import HypoellipticAleksandrov.KineticAleksandrov.Interval.KillingJets
import HypoellipticAleksandrov.KineticAleksandrov.SectionTwo.UniquenessMeasure
import Mathlib.Topology.Order.Compact

/-! # Regularized endpoint comparison and its terminal limit

Smooth compact tests are scaled strictly below one. Compactness of their supports
makes the positive endpoint distance uniform, permitting the terminal epsilon limit.
-/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.KineticAleksandrov.Interval
open Set MeasureTheory Filter Topology HypoellipticAleksandrov HypoellipticAleksandrov.Parabolic
open HypoellipticAleksandrov.KineticAleksandrov.SectionTwo
open HypoellipticAleksandrov.KineticAleksandrov.Decay
open scoped MatrixOrder

/- The scalar diagonal inherits the source lower ellipticity bound. -/
theorem interval_coefficient_lower {lam Lam } (B : CoefficientField 1)
    (hB : IsSectionTwoCoefficient lam Lam B) (r : ℝ) (v : PDE.Vec 1) :
    lam ≤ B r v 0 0 := by
  have h := (hB.2.2.2.2.1 r v).diag_nonneg (i := (0 : Fin 1))
  simpa only [Matrix.sub_apply, Matrix.smul_apply, Matrix.one_apply_eq,
    smul_eq_mul, mul_one, sub_nonneg] using h

/- Coordinates of the closure of an interval satisfy the closed endpoint bounds. -/
theorem interval_coordinate_closure {a c v}
    (hv : v ∈ closure (PDE.oneDimensionalAxisBox a c)) : a ≤ v 0 ∧ v 0 ≤ c := by
  have hsub : PDE.oneDimensionalAxisBox a c ⊆ {w : PDE.Vec 1 | a ≤ w 0 ∧ w 0 ≤ c} := by
    intro w hw
    have hh := PDE.mem_oneDimensionalAxisBox_iff.mp hw
    exact ⟨hh.1.le, hh.2.le⟩
  exact closure_minimal hsub ((isClosed_le continuous_const (continuous_apply 0)).inter
    (isClosed_le (continuous_apply 0) continuous_const)) hv

/- Positive endpoint distance on compact test support provides eventual terminal domination. -/
end HypoellipticAleksandrov.KineticAleksandrov.Interval
