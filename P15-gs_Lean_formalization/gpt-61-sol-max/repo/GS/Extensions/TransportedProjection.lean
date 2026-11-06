import Mathlib.Tactic

import GS.GeometryAlgebra
open GS.MatrixBase



/-!
# Exact Frobenius projection after orthogonal changes of coordinates

Here `Admissible` is an explicitly defined
linear space. It is not renamed a manifold tangent space by fiat. Identification
with the derivative image of the two-factor parametrization is a later theorem;
identification with a manifold tangent bundle requires the orbit-manifold proof.
-/

open Matrix
namespace GS.Extensions

 def lift (L R X : Mat n) := L * X * R
 theorem frobInner_mul_right (A B C : Mat n) :
    cFrobInner (A*B) C = cFrobInner A (C*Bᵀ) := by grind [cFrobInner_eq_re_trace,Matrix.transpose_mul,Matrix.conjTranspose_eq_transpose_of_trivial,Matrix.trace_mul_comm]

end GS.Extensions
