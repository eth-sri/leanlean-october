/- Native scalar contraction of the retained degree-eight Glennie vector.
All exposition and Lean code are AI-generated under Robert MacGregor's direction.
No novelty is asserted.
-/
module
public import Glennie.Compact.OperationalPhi

@[expose] public section
namespace Glennie.Compact.GlennieScalarPotentialR01
open Glennie
open Glennie.Compact.OperationalPhi
noncomputable section
/-- The commutator of the two native quadratic operators, applied to z. -/
def commU (x y z : Albert) : Albert := U x (U y z) - U y (U x z)

/-- The unhalved Jordan triple product. The name uses the factor-two
convention; it does not double the element `jordan x y` used below. -/
def doubledTriple (a z b : Albert) : Albert :=
  (2 : ℝ) • (jordan a (jordan z b) + jordan (jordan a z) b - jordan (jordan a b) z)

/-- Native/introductory G8, with p = x circle y and the unhalved triple product. -/
def glennieVector (x y z : Albert) : Albert :=
  doubledTriple (commU x y z) z (jordan x y) - commU x y (U z (jordan x y))

/-- The commutator of the self-adjoint U operators is skew-adjoint for raw B. -/
theorem commU_pairing (x y a b : Albert) :
    inner (commU x y a) b = -inner a (commU x y b) := by
  simp only [commU, inner_sub_left, inner_sub_right, ← U_pairing_selfadjoint]
  ring

end
end Glennie.Compact.GlennieScalarPotentialR01
