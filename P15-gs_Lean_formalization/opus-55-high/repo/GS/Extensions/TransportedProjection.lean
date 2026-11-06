module

public import GS.GeometryAlgebra

@[expose] public section


/-!
# Exact Frobenius projection after orthogonal changes of coordinates

Here `Admissible` is an explicitly defined
linear space. It is not renamed a manifold tangent space by fiat. Identification
with the derivative image of the two-factor parametrization is a later theorem;
identification with a manifold tangent bundle requires the orbit-manifold proof.
-/

noncomputable section
open Matrix
namespace GS.Extensions
variable {n : ℕ}

 def lift (L R X : Mat n) : Mat n := L * X * R
 theorem lift_injective (L R : Mat n) (hL : Orthogonal L) (hR : Orthogonal R) :
    Function.Injective (lift L R) :=
  Function.LeftInverse.injective (g := fun Z => Lᵀ * Z * Rᵀ) fun Y => by
    simp [lift, Matrix.mul_assoc, hR.2, ← Matrix.mul_assoc Lᵀ, hL.1]

 theorem lift_frobInner (L R X Y : Mat n) (hL : Orthogonal L) (hR : Orthogonal R) :
    frobInner (lift L R X) (lift L R Y) = frobInner X Y := by
  unfold lift
  rw [frobInner_right_orthogonal R hR, frobInner_left_orthogonal L hL]

 theorem frobInner_mul_right (A B C : Mat n) :
    frobInner (A*B) C = frobInner A (C*Bᵀ) := by
  rw [← frobInner_transpose, Matrix.transpose_mul, frobInner_mul_left, ← frobInner_transpose]
  simp

end GS.Extensions
