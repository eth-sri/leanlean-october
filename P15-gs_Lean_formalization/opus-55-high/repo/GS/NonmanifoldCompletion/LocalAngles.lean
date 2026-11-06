module

public import GS.NonmanifoldCompletion.SpectralTwo
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Inverse

@[expose] public section


/-!
# An actual small rotation angle for orthogonal two-by-two matrices near I

The angle is arcsin of the lower-left entry. Positivity of both determinant
and upper-left entry selects the branch. The branch domain is open and contains
I for every positive angle bound. No global continuous argument is chosen.

-/
noncomputable section
namespace GS.NonmanifoldCompletion

/-- Concrete local inverse of the angle parametrization near the identity. -/
def localRotationAngle (U : Mat 2) : ℝ := Real.arcsin (U 1 0)

/-- On the chosen branch, the arcsin formula reconstructs the whole matrix. -/
theorem rotation_localRotationAngle (U : Mat 2) (hU : Orthogonal U)
    (hdet : 0 < U.det) (ha : 0 < U 0 0) :
    rotation (localRotationAngle U) = U := by
  have hd : U.det = 1 := by
    have hg := congrArg Matrix.det hU.1
    simp_all
    nlinarith
  have hc := congrFun₂ hU.1 0 0
  have hp := congrFun₂ hU.1 0 1
  norm_num [Matrix.mul_apply, Fin.sum_univ_two, Matrix.det_fin_two] at hc hp hd
  obtain ⟨hdiag, hoff⟩ : U 1 1 = U 0 0 ∧ U 0 1 = -U 1 0 := by grind
  have hsin : Real.sin (localRotationAngle U) = U 1 0 := Real.sin_arcsin (by nlinarith) (by nlinarith)
  have hcos : Real.cos (localRotationAngle U) = U 0 0 := by
    rw [localRotationAngle,Real.cos_arcsin]
    nlinarith [Real.sqrt_nonneg (1-(U 1 0)^2), Real.sq_sqrt (show 0 ≤ 1-(U 1 0)^2 by nlinarith)]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [rotation,hsin,hcos,hdiag,hoff]

def rotationChartDomain (η : ℝ) : Set (Mat 2) :=
  {U | 0 < U.det ∧ 0 < U 0 0 ∧ |localRotationAngle U| < η}

theorem isOpen_rotationChartDomain (η : ℝ) : IsOpen (rotationChartDomain η) := by
  simp only [rotationChartDomain, localRotationAngle, Set.ofPred_and]
  exact (isOpen_lt continuous_const (by fun_prop)).inter ((isOpen_lt continuous_const (by fun_prop)).inter
    (isOpen_lt (Real.continuous_arcsin.comp (by fun_prop)).abs continuous_const))

theorem one_mem_rotationChartDomain {η : ℝ} (hη : 0 < η) :
    (1 : Mat 2) ∈ rotationChartDomain η := by
  simp [rotationChartDomain, localRotationAngle, hη]

end GS.NonmanifoldCompletion
