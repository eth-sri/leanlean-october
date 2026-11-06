module

public import GS.UnitaryManifold.OrbitDifferential

@[expose] public section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

noncomputable section
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
open Matrix GS GS.UnitaryGeometry
open scoped Topology

namespace GS.UnitaryManifold

variable {n : ℕ} {block₁ block₂ : Fin n → ℕ}

theorem cayley_intertwine (A B P : CMat n) (hA : admissible A)
    (hB : admissible B) (h : A * P = P * B) :
    cayley A * P = P * cayley B := by
  apply GS.UnitaryManifold.cancel_right (1 + B) _ _ hB
  have hp : P * (1 + B) = (1 + A) * P := by
    simp only [Matrix.mul_add, Matrix.add_mul, Matrix.mul_one, Matrix.one_mul]
    rw [h]
  calc
    cayley A * P * (1 + B) = cayley A * (P * (1 + B)) := Matrix.mul_assoc _ _ _
    _ = cayley A * ((1 + A) * P) := by rw [hp]
    _ = (1 - A) * P := by rw [← Matrix.mul_assoc, cayley_mul A hA]
    _ = P * (1 - B) := by
      simp only [Matrix.sub_mul, Matrix.mul_sub, Matrix.one_mul, Matrix.mul_one]
      rw [h]
    _ = P * cayley B * (1 + B) := by rw [Matrix.mul_assoc, cayley_mul B hB]

end GS.UnitaryManifold
