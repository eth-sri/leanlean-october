import Mathlib.Tactic

import GS.NonmanifoldCompletion.SpectralTwo
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Inverse



/-!
# An actual small rotation angle for orthogonal two-by-two matrices near I

The angle is arcsin of the lower-left entry. Positivity of both determinant
and upper-left entry selects the branch. The branch domain is open and contains
I for every positive angle bound. No global continuous argument is chosen.

-/
noncomputable section
namespace GS.NonmanifoldCompletion

variable (U : Mat 2)

/-- Concrete local inverse of the angle parametrization near the identity. -/
def localRotationAngle  : ℝ := Real.arcsin (U 1 0)

theorem continuous_localRotationAngle : Continuous localRotationAngle := Real.continuous_arcsin.comp (by fun_prop)

@[simp] theorem localRotationAngle_one : localRotationAngle (1 : Mat 2) = 0 := by
  simp [localRotationAngle]

variable (η : ℝ)

/-- Positive determinant eliminates the reflection component. -/
theorem orthogonal_det_one_of_pos  (hU : Orthogonal U)
    (hp : 0 < U.det) : U.det = 1 := by
  have hg := congrArg Matrix.det hU.1
  have hs : U.det^2=1 := by simp_all [pow_two,Matrix.det_mul,Matrix.det_transpose]
  nlinarith

/-- The determinant-one condition determines the second column. -/
theorem orthogonal2_columns  (hU : Orthogonal U) (hd : U.det=1) :
    U 1 1 = U 0 0 ∧ U 0 1 = -U 1 0 := by
  have hc := congrFun (congrFun hU.1 0) 0
  have hp := congrFun (congrFun hU.1 0) 1
  norm_num [Matrix.mul_apply,Matrix.transpose_apply,Matrix.one_apply,Fin.sum_univ_two] at hc hp
  have hdet : U 0 0 * U 1 1 - U 0 1 * U 1 0 = 1 := by simp_all [Matrix.det_fin_two]
  constructor
  · grind
  · grind

/-- On the chosen branch, the arcsin formula reconstructs the whole matrix. -/
theorem rotation_localRotationAngle  (hU : Orthogonal U)
    (hdet : 0 < U.det) (ha : 0 < U 0 0) :
    rotation (localRotationAngle U) = U := by
  have hd := orthogonal_det_one_of_pos U hU hdet
  obtain ⟨hdiag,hoff⟩ := orthogonal2_columns U hU hd
  have hc := congrFun (congrFun hU.1 0) 0
  norm_num [Matrix.mul_apply,Matrix.transpose_apply,Matrix.one_apply,Fin.sum_univ_two] at hc
  have hl : -1 ≤ U 1 0 := by nlinarith
  have hr : U 1 0 ≤ 1 := by nlinarith
  have hsin : Real.sin (localRotationAngle U) = U 1 0 := Real.sin_arcsin hl hr
  have hnonneg : 0 ≤ 1-(U 1 0)^2 := by nlinarith
  have hsqrt := Real.sq_sqrt hnonneg
  have hcos : Real.cos (localRotationAngle U) = U 0 0 := by
    rw [localRotationAngle,Real.cos_arcsin]
    nlinarith [Real.sqrt_nonneg (1-(U 1 0)^2)]
  ext i j
  fin_cases i,j <;>
    simp [rotation,hsin,hcos,hdiag,hoff]

def rotationChartDomain  : Set (Mat 2) :=
  {U | 0 < U.det ∧ 0 < U 0 0 ∧ |localRotationAngle U| < η}

theorem isOpen_rotationChartDomain  : IsOpen (rotationChartDomain η) := by
  have hdet : IsOpen {U : Mat 2 | 0 < U.det} :=
    isOpen_lt continuous_const (by fun_prop)
  have hentry : IsOpen {U : Mat 2 | 0 < U 0 0} :=
    isOpen_lt continuous_const (by fun_prop)
  have hangle : IsOpen {U : Mat 2 | |localRotationAngle U| < η} :=
    isOpen_lt continuous_localRotationAngle.abs continuous_const
  exact hdet.inter (hentry.inter hangle)

theorem one_mem_rotationChartDomain {η : ℝ} (hη : 0 < η) :
    (1 : Mat 2) ∈ rotationChartDomain η := by
  refine ⟨by simp,by simp,?_⟩
  simpa using hη

end GS.NonmanifoldCompletion
