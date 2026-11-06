module

public import HypoellipticAleksandrov.KineticAleksandrov.SectionTwo.Realization
import Mathlib.Tactic.FunProp
import Mathlib.Analysis.Matrix.Order
public import PDEFoundation.Calculus.RegularityOrder


/-! # Scalar coefficient consequences of the Section Two hypotheses -/

 public section
namespace HypoellipticAleksandrov.KineticAleksandrov.Occupation
open HypoellipticAleksandrov SectionTwo
open scoped ContDiff MatrixOrder

variable {d : ℕ} {lam Lam : ℝ} {B : CoefficientField d} (hB : IsSectionTwoCoefficient lam Lam B)

include hB
/-- Full smoothness restricts to the time--velocity coefficient. -/
theorem sectionTwoCoefficient_smooth  : IsSmoothCoefficient B := by
  apply contDiff_pi.mpr
  intro i
  apply contDiff_pi.mpr
  intro j
  have he : ContDiff ℝ PDE.smoothOrder
      (fun q : ℝ × PDE.Vec d => (q.1, (q.2, (0 : PDE.Vec d)))) := by fun_prop
  exact (hB.2.2.1 i j).comp he

/-- Lower ellipticity implies positive semidefiniteness. -/
theorem sectionTwoCoefficient_posSemidef  (r : ℝ)
    (v : PDE.Vec d) : (B r v).PosSemidef := (Matrix.nonneg_iff_posSemidef.mp
  (LE.le.trans (smul_nonneg (LT.lt.le hB.left) (Matrix.nonneg_iff_posSemidef.mpr Matrix.PosSemidef.one))
    (hB.right.right.right.right.left r v)))

end HypoellipticAleksandrov.KineticAleksandrov.Occupation
