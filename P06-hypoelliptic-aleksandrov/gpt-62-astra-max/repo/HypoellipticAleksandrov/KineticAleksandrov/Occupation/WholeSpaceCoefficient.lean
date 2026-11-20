module

public import HypoellipticAleksandrov.KineticAleksandrov.SectionTwo.Realization
import Mathlib.Tactic.FunProp
import Mathlib.Analysis.Matrix.Order

/-! # Scalar coefficient consequences of the Section Two hypotheses -/

@[expose] public section
namespace HypoellipticAleksandrov.KineticAleksandrov.Occupation
open HypoellipticAleksandrov SectionTwo
open scoped ContDiff MatrixOrder

variable {d : ℕ} {lam Lam : ℝ} {B : CoefficientField d} (hB : IsSectionTwoCoefficient lam Lam B)
include hB

/-- Full smoothness restricts to the time--velocity coefficient. -/
theorem sectionTwoCoefficient_smooth : IsSmoothCoefficient B := by
  apply contDiff_pi.mpr
  intro i
  apply contDiff_pi.mpr
  intro j
  have he : ContDiff ℝ (⊤ : ℕ∞)
      (fun q : ℝ × PDE.Vec d => (q.1, (q.2, (0 : PDE.Vec d)))) := by fun_prop
  exact (hB.2.2.1 i j).comp he

end HypoellipticAleksandrov.KineticAleksandrov.Occupation
