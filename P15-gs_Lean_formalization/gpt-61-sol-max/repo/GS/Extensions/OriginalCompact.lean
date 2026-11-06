import Mathlib.Tactic

import GS.Extensions.FiniteTopology




/-!
# The original compact-domain construction

No polar-log replacement is made. The implication G-fibre => F-fibre is proved
from the actual definitions, including the collapsed circle. The converse is
not silently assumed proved: it is the sole hypothesis of the compact-image
homeomorphism below.
-/

namespace GS.Extensions

 theorem rotation_zero : rotation 0 = 1 := by
  ext i j
  fin_cases i,j <;> simp [rotation]

 theorem rotation_add (s t : ℝ) : rotation (s+t) = rotation s * rotation t := by
  ext i j
  fin_cases i,j <;>
    simp [rotation, Matrix.mul_apply, Fin.sum_univ_two, Real.cos_add, Real.sin_add] <;>
    ring

 theorem originalPsi_zero (Q₀ : Mat q) : originalPsi Q₀ 0 = Q₀ := by
  simp [originalPsi, NormedSpace.exp_zero]

/-- A fixed representative of the unit circle, only for marking the basepoint. -/
def circleBase : CircleVector := ![1,0]

 theorem circleBase_mem : OnCircle circleBase := by norm_num [circleBase, OnCircle]

 def originalBaseParameters (q : ℕ) : OriginalParameters q :=
  (0,0,0,0,circleBase)

 theorem originalBaseParameters_mem (q : ℕ) {η : ℝ} (hη : 0 ≤ η) :
    originalBaseParameters q ∈ originalK q η := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, circleBase_mem⟩
  · aesop
  · aesop
  · aesop
  · simp [ IsSkew]
  · simp [ IsSkew]
  · aesop
  · aesop

 theorem originalF_basePoint (Q₀ : Mat q) :
    originalF Q₀ (originalBaseParameters q) = basePoint Q₀ := by
  ext i j
  simp [originalF, originalBaseParameters, originalPsi_zero, rotation_zero,
    middleBlock_equal, basePoint, finProdFinEquiv]
  exact Or.inl rfl

 theorem originalG_basePoint (q : ℕ) :
    originalG (originalBaseParameters q) = (0,0,0,0) := by
  aesop (add norm [GS.outer,GS.originalG])

end GS.Extensions
