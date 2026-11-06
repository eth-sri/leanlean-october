import Mathlib.Algebra.Star.Unitary

import GS.Core
import Mathlib.Data.Complex.Basic
import Mathlib.LinearAlgebra.Matrix.Trace



/-! Definitions and basic algebra for the unitary extension.
No assertion about the SU overlap projection is made here.
 -/

open Matrix
namespace GS

abbrev CMat (n : ℕ) := Matrix (Fin n) (Fin n) ℂ

def Unitary {n : ℕ} (A : CMat n) : Prop := Aᴴ*A=1 ∧ A*Aᴴ=1

export GS.MatrixBase (IsSkewHermitian)





namespace Unitary
variable  {A B : CMat n}



theorem conjTranspose (h : Unitary A) : Unitary Aᴴ :=
  _root_.Unitary.star_mem h

theorem mul (hA : Unitary A) (hB : Unitary B) : Unitary (A*B) :=
  (unitary (CMat n)).mul_mem hA hB

end Unitary
end GS
