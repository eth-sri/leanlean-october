module

public import HypoellipticAleksandrov.Parabolic.HarnackGeometry

/-!
# Fixed finite-chain geometry for parabolic Harnack

This module contains only the geometry of the square-root-free finite chain
from `(1, 0)` to `(4, z)`.  The velocity work boxes remain coordinate cubes,
while their containment is proved in the explicit Euclidean ball geometry.
-/

@[expose] public section

open Set

namespace HypoellipticAleksandrov.Parabolic

noncomputable section

/-- A closed coordinate cube controls the explicit squared Euclidean distance. -/
theorem vecNormSq_sub_le_natCast_mul_sq_of_mem_velocityClosedCube
    {d : ℕ} {v v0 : PDE.Vec d} {r : ℝ}
    (hv : v ∈ velocityClosedCube v0 r) :
    PDE.vecNormSq (v - v0) ≤ (d : ℝ) * r ^ 2 := by
  rw [PDE.vecNormSq_eq_sum_sq]
  calc
    ∑ i, (v - v0) i ^ 2 ≤ ∑ _i : Fin d, r ^ 2 := by
      apply Finset.sum_le_sum
      intro i _hi
      have hr : 0 ≤ r := le_trans (abs_nonneg (v i - v0 i)) (hv i)
      have hi := (sq_le_sq₀ (abs_nonneg (v i - v0 i)) hr).mpr (hv i)
      simpa only [Pi.sub_apply, sq_abs] using hi
    _ = (d : ℝ) * r ^ 2 := by simp [nsmul_eq_mul]

end

end HypoellipticAleksandrov.Parabolic
